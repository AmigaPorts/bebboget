/*
 * bebboget CLI downloader (HTTP/HTTPS client, progress, redirection)
 * Copyright (C) 2024-2025  Stefan Franke <stefan@franke.ms>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version (GPLv3+).
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 * ----------------------------------------------------------------------
 * Project: bebboget
 * Purpose: Provide a portable CLI tool to download HTTP/HTTPS resources
 *          with configurable ciphers, TLS versions, progress stats, and
 *          optional certificate installation/verification.
 *
 * Features:
 *  - Argument parsing for headers, cipher selection, TLS min/max versions,
 *    timeouts, verbosity, redirects, sloppy mode, output directory/name.
 *  - Amiga and POSIX console sizing and timekeeping.
 *  - Progress display with percent, KB, speed, and ETA.
 *  - HTTPS via Ssl3Client with certificate checks (optional sloppy mode).
 *  - Redirection handling and automatic filename generation.
 * ----------------------------------------------------------------------
 */

#include <stdlib.h>
#include <time.h>
#include <ministl/vector.h>
#include <revision.h>

#include <pkcs6.h>
#include <sha.h>
#include <unhexlify.h>
#include <log.h>
#include <certstuff.h>

#include <sys/stat.h>

#if defined(__AMIGA__)
#include <proto/dos.h>
#include <proto/exec.h>
#include <amistdio.h>

#else
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define __stdargs

#define gets(a,b) fgets(a, b, stdin)

char* concat(const char *s0, ...) {
    if (!s0) return 0;
    size_t sz = 1 + strlen(s0);
    va_list args;
    va_start(args, s0);
    for(;;) {
        char const *s = va_arg(args, char const*);
        if (!s)
            break;
        sz += strlen(s);
    }
    va_end(args);
    char * r = (char *)malloc(sz);
    if (!r) return 0;

    char * q = r;
    va_start(args, s0);
    while ((*q = *s0++)) {
        ++q;
    }
    for(;;) {
        char const *s = va_arg(args, char const*);
        if (!s)
            break;
        while ((*q = *s++)) {
            ++q;
        }
    }
    va_end(args);
    return r;
}

#endif

#include <io/socket.h>
#include <ssl3client.h>

static int numRows;
static int numCols;

static char const *url;
static char const * outFile;
static short outFileSet;
static char * loc;
static int progress = true;
static int clientHeaders;
static int serverHeaders;
// -T and friends as in wget: seconds plus microseconds, 0 means no timeout
static long readTimeout = 900;
static long readTimeoutUs;
static long connectTimeout;
static long connectTimeoutUs;
static int tries = 20; // -t as in wget, 0 means no limit
static int overwrite;
static const char * outDir;
static int pmin = 3;
static int pmax = 4;
static int nredir = 7;
static int sloppy;
static int installCertificates;

static mstl::vector<char const *> headers;
static mstl::vector<uint8_t const *> ciphers;

static void printUsage() {
    puts(__VERSION);
    puts("USAGE: bebboget " __V__ " [options] <url>");
    puts("    -?            display this help");
    puts("    -C            print the outgoing headers");
    puts("    -D <dir>      the directory to write to (must exist)");
    puts("    -H <header>   add the given header");
    puts("    -I            install all certificates");
    puts("    -O            overwrite the file");
    puts("    -S            print the incoming headers");
    puts("    -T <n>        set connect and read timeout in seconds, 0=none");
    puts("    -t <n>        number of tries, 0 or inf=no limit, default=20");
    puts("    -o <outname>  use this as out file name");
    puts("    -p            print progress and verbosity 4 = INFO");
    puts("    -q            print errors only");
    puts("    -v <n>        set verbosity, defaults to 2 = ERROR");
    puts("    --connect-timeout <n> connect timeout in seconds, default=none");
    puts("    --read-timeout <n>    idle read timeout in seconds, default=900");
    puts("    --timeout <n> same as -T");
    puts("    --tries <n>   same as -t");
    puts("    --cipher <c>  use the given cipher, default uses all");
    puts("    --max <n>     max supported protocol version, default=4");
    puts("    --min <n>     min supported protocol version, default=3");
    puts("    --nochpo      disable chacha20_poly1305");
    puts("    --redir <n>   max count of redirects, default=7");
    puts("    --sloppy      skip signature checks");
    puts("");
    puts("available ciphers:");
    int komma = false;
    int pos = 0;
    for (char const ** n = Ssl3::CIPHERSUITENAMES; *n; ++n) {
        if (komma) {
            printf(", ");
            pos += 2;
        }
        char const * s = *n;
        int l = strlen(s);
        if (l + 2 + pos > numCols) {
            puts("");
            pos = 0;
        }
        printf("%s", s);
        pos += l;
        komma = true;
    }
    puts("");
    fflush(stdout);
}

static int addCipher(char const * cname) {
    uint8_t const * ciph = Ssl3::lookupCipher(cname);
    if (ciph) {
        ciphers.push_back(ciph);
        return true;
    }
    printf("error: unknown cipher '%s'\n", cname);
    return false;
}

// The value of an option: what follows its name, after an optional '=',
// or else the next argument. 0 if there is none.
static char const * optionValue(char const * rest, unsigned argc, const char **argv, unsigned & i) {
    if (*rest == '=')
        ++rest;
    if (*rest)
        return rest;
    if (i + 1 == argc)
        return 0;
    return argv[++i];
}

// Seconds, possibly with a fraction as in "0.5", as wget takes them.
static void parseSeconds(char const * s, long * seconds, long * microSeconds) {
    char * end;
    *seconds = strtoul(s, &end, 10);
    *microSeconds = 0;
    if (*end == '.') {
        long scale = 100000;
        for (char const * d = end + 1; *d >= '0' && *d <= '9' && scale; ++d, scale /= 10)
            *microSeconds += (*d - '0') * scale;
    }
}

static void parseTries(char const * s) {
    tries = strcmp(s, "inf") ? strtoul(s, 0, 10) : 0;
}

static void parseParams(unsigned argc, const char **argv) {
    unsigned normal = 0;
    const char *arg = 0;

    if (argc == 1)
        goto usage;

    setLogLevel(L_ERROR);

    for (unsigned i = 1; i < argc; ++i) {
        arg = argv[i];
        if (normal == 0 && arg[0] == '-') {
            switch (arg[1]) {
            case '?':
                goto usage;
            case 'O':
                overwrite = true;
                continue;
            case 'C':
                clientHeaders = true;
                continue;
            case 'D':
                if (arg[2]) {
                    outDir = &arg[2];
                    continue;
                }

                if (i + 1 == argc)
                    goto missing;
                outDir = argv[++i];
                continue;
            case 'H':
                if (arg[2]) {
                    headers.push_back(&arg[2]);
                    continue;
                }

                if (i + 1 == argc)
                    goto missing;
                headers.push_back(argv[++i]);
                continue;
            case 'I':
                installCertificates = true;
                continue;
            case 'S':
                serverHeaders = true;
                continue;
            case 'T': {
                char const * v = optionValue(&arg[2], argc, argv, i);
                if (!v)
                    goto missing;
                parseSeconds(v, &readTimeout, &readTimeoutUs);
                connectTimeout = readTimeout;
                connectTimeoutUs = readTimeoutUs;
                continue;
            }
            case 't': {
                char const * v = optionValue(&arg[2], argc, argv, i);
                if (!v)
                    goto missing;
                parseTries(v);
                continue;
            }
            case 'o':
                if (arg[2]) {
                    outFile = &arg[2];
                    outFileSet = 1;
                    continue;
                }

                if (i + 1 == argc)
                    goto missing;
                outFile = argv[++i];
                outFileSet = 1;
                continue;
            case 'q':
                setLogLevel(L_ERROR);
                progress = false;
                continue;
            case 'p':
                setLogLevel(L_INFO);
                continue;
            case 'v':
                if (arg[2]) {
                    setLogLevel((DebugLevel) atoi(&arg[2]));
                    continue;
                }

                if (i + 1 == argc)
                    goto missing;
                setLogLevel((DebugLevel) atoi(argv[++i]));
                continue;
            case '-':
                if (0 == strncmp("nochpo", &arg[2], 6)) {
                    *(uint32_t*)Ssl3::CIPHERSUITES[0] = 0xffffffff; // poke it invalid
                    continue;
                }
                if (0 == strncmp("cipher", &arg[2], 6)) {
                    if (arg[8]) {
                        if (!addCipher(&arg[8]))
                            exit(10);
                        continue;
                    }

                    if (i + 1 == argc)
                        goto missing;
                    if (!addCipher(argv[++i]))
                        exit(10);
                    continue;
                }
                if (0 == strncmp("min", &arg[2], 3)) {
                    if (arg[5]) {
                        pmin = strtoul(&arg[5], 0, 10);
                        continue;
                    }

                    if (i + 1 == argc)
                        goto missing;
                    pmin = strtoul(argv[++i], 0, 10);
                    continue;
                }
                if (0 == strncmp("max", &arg[2], 3)) {
                    if (arg[5]) {
                        pmax = strtoul(&arg[5], 0, 10);
                        continue;
                    }

                    if (i + 1 == argc)
                        goto missing;
                    pmax = strtoul(argv[++i], 0, 10);
                    continue;
                }
                if (0 == strncmp("redir", &arg[2], 5)) {
                    if (arg[7]) {
                        nredir = strtoul(&arg[7], 0, 10);
                        continue;
                    }

                    if (i + 1 == argc)
                        goto missing;
                    nredir = strtoul(argv[++i], 0, 10);
                    continue;
                }
                if (0 == strncmp("tries", &arg[2], 5)) {
                    char const * v = optionValue(&arg[7], argc, argv, i);
                    if (!v)
                        goto missing;
                    parseTries(v);
                    continue;
                }
                if (0 == strncmp("timeout", &arg[2], 7)) {
                    char const * v = optionValue(&arg[9], argc, argv, i);
                    if (!v)
                        goto missing;
                    parseSeconds(v, &readTimeout, &readTimeoutUs);
                    connectTimeout = readTimeout;
                    connectTimeoutUs = readTimeoutUs;
                    continue;
                }
                if (0 == strncmp("connect-timeout", &arg[2], 15)) {
                    char const * v = optionValue(&arg[17], argc, argv, i);
                    if (!v)
                        goto missing;
                    parseSeconds(v, &connectTimeout, &connectTimeoutUs);
                    continue;
                }
                if (0 == strncmp("read-timeout", &arg[2], 12)) {
                    char const * v = optionValue(&arg[14], argc, argv, i);
                    if (!v)
                        goto missing;
                    parseSeconds(v, &readTimeout, &readTimeoutUs);
                    continue;
                }
                if (0 == strncmp("sloppy", &arg[2], 6)) {
                    sloppy = true;
                    continue;
                }
                /* no break */
            default:
                goto invalid;
            }
        }

        if (normal == 0) {
            url = arg;
        }

        ++normal;
        continue;
    }

    if (normal == 1)
        return;

    usage: printUsage();
    exit(0);

    missing: printf("missing parameter for %s\n", arg);
    exit(10);

    invalid: printf("invalid option %s\n", arg);
    exit(10);
}

#if defined(__AMIGA__)

typedef struct DateStamp TimeType;

BPTR stdoutBptr;
BPTR stdinBptr;

static int getConsoleSize() {
    uint8_t tmp[16];
    if (!stdoutBptr) {
        numCols = 60;
        return false;
    }
    SetMode(stdinBptr, 1);
    Write(stdinBptr, "\x9b\x30\x20\x71", 4);
    uint8_t *p = &tmp[0];
    while (WaitForChar(stdinBptr, 200) == DOSTRUE) {
        Read(stdinBptr, p, 1);
        ++p;
        if (p > &tmp[15])
            break;
    }
    SetMode(stdinBptr, 0);
    uint8_t *q = &tmp[5];
    numRows = 0;
    for (; q < p; ++q) {
        if (*q == ';')
            break;
        numRows = numRows * 10;
        numRows += *q - '0';
    }
    ++q;
    numCols = 0;
    for (; q < p; ++q) {
        if (*q == ' ')
            break;
        numCols = numCols * 10;
        numCols += *q - '0';
    }

    if (numCols < 60)
        numCols = 60;
    return true;
}

int deltaTime(TimeType const & now, TimeType const * then) {
    return (now.ds_Tick - then->ds_Tick
                  + (now.ds_Minute - then->ds_Minute
                  + (now.ds_Days - then->ds_Days) * 24 * 60) * 60 * 50) * 2;
}

void nowTime(TimeType * t) {
    DateStamp(t);
}

#else

typedef struct timeval TimeType;

int deltaTime(TimeType const & now, TimeType const * then) {
    return (now.tv_sec - then->tv_sec) * 1000
            + (now.tv_usec - then->tv_usec) / 1000;
}

void nowTime(TimeType * t) {
    t->tv_sec = time(0);
    t->tv_usec = 0;
}

void getConsoleSize() {
    numRows = 10;
    numCols = 80;
}

#endif

static int firstDone;
static char const * src;
static unsigned long long size;
static unsigned long long pos;
static unsigned long long lastPos;
TimeType startTime;
TimeType lastTime;
TimeType now;


static void printStats(int full) {
    int percent = 0;
    if (size) {
        if (size > 0xffffffffUL / 100)
            percent = pos / (size / 100);
        else
            percent = 100 * pos / size;
        full |= pos == size;
    }

    int sz = pos / 1000;
    if (lastPos > pos)
        lastPos = 0;
    TimeType * then;
    if (full)
        then = &startTime;
     else
        then = &lastTime;
    int delta = deltaTime(now, then);

    int speed = 0;
    if (delta) {
        if (full)
            speed = size / delta;
        else
            speed = (pos - lastPos) / delta;
    }

    lastPos = pos;

    int eta;
    if (speed == 0 || size == 0) {
        eta = 0;
    } else if (full) {
        eta = delta / 100;
    } else {
        eta = ((size - pos) / 100) / speed;
    }
    int min = eta / 60;
    int sec = eta % 60;
    int kb = speed/10;
    printf("%3ld%% %8ldKB %4ld.%ldKB/s %2ld:%02ld %s", percent, sz, kb, speed - 10*kb, min, sec, full ? "   \n" : size ? "ETA" : "???");
    fflush(stdout);
}

static void erase() {
    for (short i = 36; i > 0; --i) {
        putchar('\b');
    }
}

static void updateStats() {
    if (!progress)
        return;

    nowTime(&now);
    if (pos == 0 || !firstDone) {
        if (!firstDone) {
            firstDone = true;
            startTime = now;

            getConsoleSize();

            // print name and fill with spaces
            int spaces = numCols - 37 - strlen(src);
            if (spaces < 0) {
                printf("...%s", src - spaces + 4);
            } else {
                printf("%s", src);
            }
            fflush(stdout);
            if (spaces <= 0)
                spaces = 1;
            while (--spaces >= 0) {
                putchar(' ');
            }
            lastPos = 0;
            lastTime = now;
            printStats(false);

        }
    } else {

        // update every second
        int done = size && size == pos;
#if defined(__AMIGA__)
        int diff = now.ds_Tick - lastTime.ds_Tick;
        if (diff < 0 || diff > TICKS_PER_SECOND || done) {
#else
        int diff = now.tv_sec - lastTime.tv_sec;
        if (diff < 0 || diff > 0 || done) {
#endif
            erase();
            printStats(done);
            lastTime = now;
        }
    }
}

char const * mkFileName(char const * path) {
    char const * p = path;
    char const * q = path;
    while (*p) {
        if (*p == '/')
            q = p + 1;
        ++p;
    }

    if (outFile)
        q = outFile;
    else if (!*q)
        q = "out.dat";

    if (outDir) {
        int odLen = strlen(outDir);
        if (odLen) {
            char last = outDir[odLen - 1];
            if (last == ':' || last == '/')
                q = concat(outDir, q, 0);
            else
                q = concat(outDir, "/", q, 0);
        }
    }

    char * r = strdup(q);
    if (overwrite)
        return r;

    int no = 0;
    for(;;) {
#if defined(__AMIGA__)
        BPTR lock = Lock(r, SHARED_LOCK);
        if (!lock)
            break;
        UnLock(lock);
#else
        FILE * f = fopen(r, "r");
        if (!f)
            break;
        fclose(f);
#endif

        char tmp[16];
        snprintf(tmp, 15, "%ld", no++);

        free(r);
        r = concat(q, ".", tmp, 0);
    }

    return r;
}

// Exit codes, the same wget uses.
#define EXIT_GENERIC 1
#define EXIT_IO      3
#define EXIT_NETWORK 4
#define EXIT_SSL     5
#define EXIT_SERVER  8

static int exitCode;
static int retryable;         // whether the failure of the last download() may go away on another try
static int interrupted;       // Ctrl-C
static unsigned long restval; // bytes of src kept from a failed try, continued with a Range request

static int checkBreak() {
#if defined(__AMIGA__)
    if (SetSignal(0L, SIGBREAKF_CTRL_C) & SIGBREAKF_CTRL_C)
        interrupted = true;
#endif
    return interrupted;
}

static char const * socketError(int e) {
    switch (e) {
    case net::Socket::ERR_HOST_NOT_FOUND:  return "host not found";
    case net::Socket::ERR_REFUSED:         return "connection refused";
    case net::Socket::ERR_CONNECT_FAILED:  return "connection failed";
    case net::Socket::ERR_CONNECT_TIMEOUT: return "connection timed out";
    case net::Socket::ERR_READ_TIMEOUT:    return "read timed out";
    case net::Socket::ERR_READ_ERROR:      return "read error";
    case net::Socket::ERR_INTERRUPTED:     return "interrupted";
    }
    return "connection closed";
}

// End the line the progress display is on, so that messages start on their own.
static void endProgress() {
    if (progress && firstDone) {
        putchar('\n');
        firstDone = false;
    }
}

// As in wget, a host that does not resolve or refuses the connection is
// not tried again, while timeouts and broken connections are.
static char * networkFailure(int e, char const * where) {
    endProgress();
    printf("%s %s\n", socketError(e), where);
    if (e == net::Socket::ERR_INTERRUPTED)
        interrupted = true;
    exitCode = EXIT_NETWORK;
    retryable = e != net::Socket::ERR_HOST_NOT_FOUND && e != net::Socket::ERR_REFUSED && e != net::Socket::ERR_INTERRUPTED;
    return 0;
}

static void sleepSeconds(int seconds) {
#if defined(__AMIGA__)
    for (int t = seconds * 5; t > 0 && !checkBreak(); --t)
        Delay(10);
#else
    sleep(seconds);
#endif
}

char* download() {
    int isHttp = strncmp(url, "http://", 7) == 0;
    int isHttps = strncmp(url, "https://", 8) == 0;

    if (!isHttp && !isHttps) {
        printf("unsupported protocol: %s\n", url);
        return 0;
    }

    char const *host = url + (isHttp ? 7 : 8);

    char const *path = strchr(host, '/');
    if (!path) {
        path = "/";
    } else {
        int len = path - host;
        char *h = (char*) malloc(len + 1);
        strncpy(h, host, len);
        h[len] = 0;
        host = h;
    }

    int port = isHttp ? 80 : 443;
    char const *colon = strchr(host, ':');
    if (colon) {
        int len = colon - host;
        char *h = (char*) malloc(len + 1);
        strncpy(h, host, len);
        h[len] = 0;
        host = h;

        port = strtoul((char*) colon + 1, 0, 10);
    }

    if (!src)
        src = mkFileName(path);

    if (isLogLevel(L_INFO))
        printf("connecting to %s on port %ld\n", host, port);


    uint8_t const ** cs = ciphers.size() > 1 ? ciphers.begin() : Ssl3::CIPHERSUITES;
    Ssl3Client s3(cs);
    if (isHttps) {
        s3.setSloppy(sloppy);
        s3.setMinVersion(pmin);
        s3.setMaxVersion(pmax);
        s3.prepareEEK();
    }

    net::Socket socket(host, port, connectTimeout, connectTimeoutUs);
    if (socket.getError())
        return networkFailure(socket.getError(), "connecting");
    socket.setTimeout(readTimeout, readTimeoutUs);

    InputStream * is;
    OutputStream * os;

    is = socket.getInputStream();
    os = socket.getOutputStream();

    if (isHttps) {
        int r = s3.connect(is, os, host);

        if (r) {
            printf("error %ld\n", r);
            if (socket.getError())
                return networkFailure(socket.getError(), "during the TLS handshake");
            exitCode = EXIT_NETWORK;
            return 0;
        }

        if (!sloppy && !checkCertificates(host, s3.getCerts(), installCertificates)) {
            printf("error: certificate not accepted\n");
            exitCode = EXIT_SSL;
            return 0;
        }

        if (isLogLevel(L_INFO))
            printf("using %s %s\n", s3.getProtocolVersion(), s3.getSelectedCiphersuite());
        is = s3.getInputStream();
        os = s3.getOutputStream();
    }

    // continue what a previous try left, as wget does
    char range[40] = "";
    if (restval)
        snprintf(range, sizeof(range), "Range: bytes=%lu-\r\n", restval);

    char *msg0 = concat("GET ", path, " HTTP/1.1\r\nhost: ", host, "\r\nConnection: close\r\n"
            "User-Agent: BebboGet\r\n", range, 0);

    for (int i = 0; i < headers.size(); ++i) {
        char const * h = headers[i];
        char * msg = concat(msg0, h, "\r\n", 0);
        free(msg0);
        msg0 = msg;
    }

    char * msg = concat(msg0, "\r\n", 0);
    free(msg0);

    if (clientHeaders)
        printf("> %s\n", msg);

    os->write(msg, strlen(msg));

    bytea rest;
    int status = 0;
    int chunked = false;
    size = 0;
    while (!checkBreak()) {
        int start = rest.size();
        rest.setSize(rest.size() + 2048 + 1);
        int read = is->read(rest.begin() + start, 2048);
        if (read <= 0)
            return networkFailure(socket.getError(), "reading the response headers");

        rest.setSize(start + read);
        rest[rest.size()] = 0;

        // read header
        for (;;) {
            char *b = (char*) rest.begin();
            char *n = strchr(b, '\r');
            if (!n)
                break;
            *n = 0;
            if (n == b)
                goto Reading;

            if (serverHeaders)
                printf("< %s\n", b);

            if (!status && 0 == strncmp("HTTP/", b, 5)) {
                char const * code = strchr(b, ' ');
                if (code)
                    status = atoi(code + 1);
            }

            char *colon = strchr(b, ':');
            if (colon) {
                *colon++ = 0;
                while (*colon && *colon <= 32)
                    ++colon;

                if (0 == strcasecmp("Content-Length", b)) {
                    size = strtoul(colon, 0, 10);
                } else if (0 == strcasecmp("Transfer-Encoding", b)) {
                    chunked = 0 == strcasecmp("chunked", colon);
                } else if (0 == strcasecmp("Location", b)) {
                    free(loc);
                    loc = strdup(colon);
                    return loc;
                } else if (!outFileSet && 0 == strcasecmp("Content-Disposition", b)) {
                    char * fn = strstr(colon, "filename=");
                    if (fn) {
                        src = mkFileName(fn + 9);
                    }
                }
            }

            n += 2; // skip \r\n

            int len = n - (char*) rest.begin();

            memmove(rest.begin(), rest.begin() + len, rest.size() - len);
            rest.setSize(rest.size() - len);
        }
    }

    endProgress();
    puts("interrupted");
    exitCode = EXIT_GENERIC;
    return 0;

    Reading:

    fflush(stdout);

    // 206 continues the file, anything else replaces it: also a 200 from
    // a server that ignored the Range request
    int append = status == 206 && restval;
    if (!append)
        restval = 0;
    if (size)
        size += restval;

    updateStats();

#if defined(__AMIGA__)
    BPTR out = append ? Open(src, MODE_OLDFILE) : Open(src, MODE_NEWFILE);
    if (out && append)
        Seek(out, 0, OFFSET_END);
#else
    FILE * out = fopen(src, append ? "ab" : "wb+");
#endif
    if (out) {
        if (rest.size() > 2) { // skip \r\n
#if defined(__AMIGA__)
            Write(out, rest.begin() + 2, rest.size() - 2);
#else
            fwrite(rest.begin() + 2, rest.size() - 2, 1, out);
#endif
        }

        pos = restval + rest.size() - 2;
        updateStats();

        while (!checkBreak()) {
    		if (size && size == pos)
    			break;
            static char buffer[8192];
            int read = is->read(buffer, sizeof(buffer));
            if (read <= 0) {
                break;
            }

            pos += read;
            updateStats();
#if defined(__AMIGA__)
            Write(out, buffer, read);
#else
            fwrite(buffer, read, 1, out);
#endif
        }
#if defined(__AMIGA__)
        Close(out);
#else
        fclose(out);
#endif
    } else {
        printf("can't open '%s' for writing\n", src);
        exitCode = EXIT_IO;
        return 0;
    }

    if (interrupted) {
        endProgress();
        puts("interrupted");
        exitCode = EXIT_GENERIC;
        return 0;
    }

    // Short of the announced length, or cut by a timeout or a broken
    // connection: what arrived is kept and the next try continues it,
    // unless it is chunked, where a Range would not line up.
    int e = socket.getError();
    if ((size && pos < size) || (e && e != net::Socket::ERR_CLOSED)) {
        restval = size && !chunked ? pos : 0;
        return networkFailure(e, "while reading the data");
    }

    if (size == 0) {
        size = pos;
        updateStats();
    }

    if (status >= 400) {
        printf("ERROR %ld\n", (long) status);
        exitCode = EXIT_SERVER;
    }

    return 0;
}

void myinit() {
#if defined(__AMIGA__)
    stdinBptr = Input();
    stdoutBptr = Output();
#endif
    getConsoleSize();
}

extern "C" {
__stdargs
 int main(int argc, char const **argv) {
    myinit();

    parseParams(argc, argv);

    logme(L_DEBUG, "parameters parsed");

    ciphers.push_back(0);

    fflush(stdin);

    // like wget, wait a second more after each failed try, up to 10
    int attempt = 0;
    while (url && nredir > 0) {
        ++attempt;
        exitCode = 0;
        retryable = false;
        char const * next = download();
        if (next) {
            if (isLogLevel(L_WARN))
                printf("redirecting to: %s\n", next);
            url = next;
            --nredir;
            attempt = 0;
            restval = 0;
            continue;
        }
        if (!retryable || interrupted)
            break;
        if (tries && attempt >= tries) {
            puts("giving up");
            break;
        }
        int wait = attempt < 10 ? attempt : 10;
        printf("retrying in %ld s, try %ld\n", (long) wait, (long) attempt + 1);
        fflush(stdout);
        sleepSeconds(wait);
        if (interrupted) {
            puts("interrupted");
            exitCode = EXIT_GENERIC;
            break;
        }
    }

    if (url && nredir == 0) {
        puts("too many redirects");
        exitCode = EXIT_SERVER;
    }

    return exitCode;
}}
