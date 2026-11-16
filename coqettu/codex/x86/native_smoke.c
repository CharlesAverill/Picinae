/* Execute the exact Alpine i386 ELF as an additional specification sanity check.
 * These checks complement the Rocq proofs; they do not validate the lifter.
 * Build without compiler builtins so each call reaches the musl binary.
 */
typedef unsigned int U;
typedef unsigned char B;
_Static_assert(sizeof(int) == 4 && sizeof(void *) == 4, "requires i386");

extern int toascii(int), isascii(int), isdigit(int), islower(int), isupper(int);
extern int isprint(int), isgraph(int), abs(int);
extern long labs(long);
extern U htonl(U), ntohl(U);
extern unsigned short htons(unsigned short), ntohs(unsigned short);
extern U strlen(const char *);
extern int memcmp(const void *, const void *, U);
extern int strcmp(const char *, const char *);
extern void *memrchr(const void *, int, U);
extern int *wmemchr(const int *, int, U);
extern int *wmemset(int *, int, U);
extern int wmemcmp(const int *, const int *, U);
extern int ffs(int), ffsl(long), ffsll(long long);

static U first32(U x) {
    if (!x) return 0;
    U position = 1;
    while (!(x & 1)) { x >>= 1; ++position; }
    return position;
}

static U swap32(U x) {
    return (x >> 24) | ((x >> 8) & 0xff00u) |
           ((x << 8) & 0xff0000u) | (x << 24);
}

static int run(void) {
    const U values[] = {0, 1, 127, 128, 255, 256, 0x12345678u,
                        0x7fffffffu, 0x80000000u, 0xffffffffu};
    for (U i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
        U x = values[i], magnitude = x < 0x80000000u ? x : 0u - x;
        if (htonl(x) != swap32(x) || ntohl(x) != swap32(x)) return 1;
        if ((U)abs((int)x) != magnitude || (U)labs((long)x) != magnitude) return 2;
        if ((U)ffs((int)x) != first32(x) || (U)ffsl((long)x) != first32(x)) return 18;
    }
    for (U x = 0; x < 65536; ++x) {
        U swapped = ((x & 255) << 8) | (x >> 8);
        if (htons((unsigned short)x) != swapped || ntohs((unsigned short)x) != swapped) return 3;
        if ((U)ffs((int)x) != first32(x) || (U)ffsl((long)x) != first32(x)) return 18;
    }
    for (U i = 0; i < 1024; ++i) {
        U x = i < 512 ? i : (0xffffffffu - (i - 512));
        if ((U)toascii((int)x) != (x & 127)) return 4;
        if (isascii((int)x) != (x <= 127)) return 5;
        if (isdigit((int)x) != (48 <= x && x <= 57)) return 6;
        if (islower((int)x) != (97 <= x && x <= 122)) return 7;
        if (isupper((int)x) != (65 <= x && x <= 90)) return 8;
        if (isprint((int)x) != (32 <= x && x <= 126)) return 9;
        if (isgraph((int)x) != (33 <= x && x <= 126)) return 10;
    }
    B a[256], b[256];
    for (U alignment = 0; alignment < 4; ++alignment) {
        for (U n = 0; n < 160; ++n) {
            for (U j = 0; j < 256; ++j) a[j] = (B)(1 + j % 255);
            a[alignment + n] = 0;
            if (strlen((const char *)a + alignment) != n) return 11;
        }
    }
    for (U n = 0; n < 128; ++n) {
        for (U j = 0; j < 256; ++j) a[j] = b[j] = (B)(j * 17);
        if (memcmp(a, b, n) != 0) return 12;
        for (U first = 0; first < n; ++first) {
            B old = a[first];
            a[first] = 200; b[first] = 3;
            if (memcmp(a, b, n) != 197 || memcmp(b, a, n) != -197) return 13;
            a[first] = b[first] = old;
        }
    }
    for (U left = 0; left < 4; ++left) for (U right = 0; right < 4; ++right) {
        for (U n = 0; n < 128; ++n) {
            for (U j = 0; j < n; ++j) a[left+j] = b[right+j] = (B)(1+j%255);
            a[left+n] = b[right+n] = 0;
            if (strcmp((char *)a+left, (char *)b+right) != 0) return 20;
            for (U first = 0; first < n; ++first) {
                B old = a[left+first];
                a[left+first] = 200; b[right+first] = 3;
                if (strcmp((char *)a+left, (char *)b+right) != 197 ||
                    strcmp((char *)b+right, (char *)a+left) != -197) return 21;
                a[left+first] = b[right+first] = old;
            }
            b[right+n] = 100; b[right+n+1] = 0;
            if (strcmp((char *)a+left, (char *)b+right) != -100) return 22;
        }
    }
    for (U n = 0; n < 128; ++n) {
        for (U j = 0; j < n; ++j) a[j] = (B)(j%17);
        for (U value = 0; value < 256; ++value) {
            B *expected = (B *)0;
            for (U j = n; j > 0; --j) if (a[j-1] == value) { expected = a+j-1; break; }
            if (memrchr(a, (int)value-256, n) != expected) return 23;
        }
    }
    int filled[136];
    for (U offset = 0; offset < 4; ++offset) for (U n = 0; n <= 128; ++n) {
        for (U value = 0; value < 10; ++value) {
            for (U j = 0; j < 136; ++j) filled[j] = 0x13579bdf;
            if (wmemset(filled+offset, (int)values[value], n) != filled+offset) return 24;
            for (U j = 0; j < 136; ++j) {
                U expected = offset <= j && j < offset+n ? values[value] : 0x13579bdf;
                if ((U)filled[j] != expected) return 25;
            }
        }
    }
    int wide[] = {0, -1, 0x7fffffff, (int)0x80000000u, 42, -1};
    for (U n = 0; n <= 6; ++n) {
        for (U which = 0; which < 6; ++which) {
            int *expected = (int *)0;
            for (U j = 0; j < n; ++j) {
                if (wide[j] == wide[which]) { expected = wide + j; break; }
            }
            if (wmemchr(wide, wide[which], n) != expected) return 14;
        }
        if (wmemchr(wide, 12345, n) != (int *)0) return 15;
        if (wmemcmp(wide, wide, n) != 0) return 16;
    }
    for (U i = 0; i < 6; ++i) for (U j = 0; j < 6; ++j) {
        int expected = wide[i] < wide[j] ? -1 : wide[i] > wide[j] ? 1 : 0;
        if (wmemcmp(wide + i, wide + j, 1) != expected) return 17;
    }
    for (U lo = 0; lo < 10; ++lo) for (U hi = 0; hi < 10; ++hi) {
        U low = values[lo], high = values[hi];
        unsigned long long bits = ((unsigned long long)high << 32) | low;
        U expected = low ? first32(low) : high ? 32 + first32(high) : 0;
        if ((U)ffsll((long long)bits) != expected) return 19;
    }
    return 0;
}

static void say(const char *message, U length) {
    int result;
    __asm__ volatile("int $0x80" : "=a"(result) : "0"(4), "b"(1), "c"(message), "d"(length) : "memory");
}

__attribute__((noreturn, force_align_arg_pointer)) void _start(void) {
    int result = run();
    static const char pass[] = "CoqEtTu: native Alpine i386 checks passed\n";
    static const char fail[] = "CoqEtTu: native Alpine i386 check failed (see exit code)\n";
    if (result) say(fail, sizeof(fail) - 1); else say(pass, sizeof(pass) - 1);
    __asm__ volatile("int $0x80" : : "a"(1), "b"(result) : "memory");
    __builtin_unreachable();
}
