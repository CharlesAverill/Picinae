/* Execute the exact Alpine i386 ELF as an additional specification sanity check.
 * These checks complement the Rocq proofs; they do not validate the lifter.
 * Build without compiler builtins so each call reaches the musl binary.
 */
typedef unsigned int U;
typedef unsigned char B;
_Static_assert(sizeof(int) == 4 && sizeof(void *) == 4, "requires i386");

extern int toascii(int), isascii(int), isdigit(int), islower(int), isupper(int);
extern int isprint(int), isgraph(int), ispunct(int), abs(int);
extern int isalpha(int), isalnum(int), isblank(int), iscntrl(int), isspace(int);
extern int tolower(int), toupper(int), isxdigit(int);
extern int iswdigit(U), iswxdigit(U), iswcntrl(U), iswblank(U);
extern int wcscmp(const int *, const int *), wcsncmp(const int *, const int *, U);
extern long labs(long);
extern long long llabs(long long), imaxabs(long long);
extern U htonl(U), ntohl(U);
extern unsigned short htons(unsigned short), ntohs(unsigned short);
extern U strlen(const char *);
extern U strnlen(const char *, U);
extern void *wctrans(const char *), *wctrans_l(const char *, void *);
extern U wctype(const char *), wctype_l(const char *, void *);
extern U wcslen(const int *);
extern int *wcschr(const int *, int), *wcsrchr(const int *, int);
extern U wcsnlen(const int *, U);
extern int iswdigit_l(U, void *), iswxdigit_l(U, void *), iswblank_l(U, void *), iswcntrl_l(U, void *);
extern int tolower_l(int, void *), toupper_l(int, void *);
extern int isalnum_l(int, void *), ispunct_l(int, void *);
extern int isalpha_l(int, void *);
extern int isblank_l(int, void *);
extern int iscntrl_l(int, void *);
extern int isdigit_l(int, void *);
extern int isgraph_l(int, void *);
extern int islower_l(int, void *);
extern int isprint_l(int, void *);
extern int isspace_l(int, void *);
extern int isupper_l(int, void *);
extern int isxdigit_l(int, void *);

extern int memcmp(const void *, const void *, U);
extern int bcmp(const void *, const void *, U);
extern int strcmp(const char *, const char *);
extern int strcasecmp(const char *, const char *);
extern int strncasecmp(const char *, const char *, U);
extern int strncasecmp_l(const char *, const char *, U, void *);
extern int strcasecmp_l(const char *, const char *, void *);
extern char *index(const char *, int), *rindex(const char *, int);
extern char *strrchr(const char *, int), *strchrnul(const char *, int), *strchr(const char *, int);
extern char *strncat(char *, const char *, U);
extern int strcoll(const char *, const char *);
extern int wcscoll(const int *, const int *);
extern int strcoll_l(const char *, const char *, void *);
extern int wcscoll_l(const int *, const int *, void *);
extern void *memrchr(const void *, int, U);
extern void *memchr(const void *, int, U);
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

static int wide_reference(const int *a, const int *b, U count) {
    for (U i = 0; i < count; ++i) {
        if (a[i] < b[i]) return -1;
        if (a[i] > b[i]) return 1;
        if (!a[i]) return 0;
    }
    return 0;
}

/* This ELF ignores the locale word in these forwarding routines. */
static int locale_classifiers_match(U x, void *locale) {
    int upper = 65 <= x && x <= 90, lower = 97 <= x && x <= 122;
    int digit = 48 <= x && x <= 57;
    if ((U)tolower_l((int)x, locale) != (upper ? x+32 : x)) return 0;
    if ((U)toupper_l((int)x, locale) != (lower ? x-32 : x)) return 0;
    if (ispunct_l((int)x, locale) != ((33 <= x && x <= 126) && !(upper || lower || digit))) return 0;
    if (isalnum_l((int)x, locale) != (upper || lower || digit)) return 0;
    if (isalpha_l((int)x, locale) != (upper || lower)) return 0;
    if (isblank_l((int)x, locale) != (x == 9 || x == 32)) return 0;
    if (iscntrl_l((int)x, locale) != (x <= 31 || x == 127)) return 0;
    if (isdigit_l((int)x, locale) != (digit)) return 0;
    if (isgraph_l((int)x, locale) != (33 <= x && x <= 126)) return 0;
    if (islower_l((int)x, locale) != (lower)) return 0;
    if (isprint_l((int)x, locale) != (32 <= x && x <= 126)) return 0;
    if (isspace_l((int)x, locale) != ((9 <= x && x <= 13) || x == 32)) return 0;
    if (isupper_l((int)x, locale) != (upper)) return 0;
    if (isxdigit_l((int)x, locale) != (digit || (65 <= x && x <= 70) || (97 <= x && x <= 102))) return 0;
    return 1;
}

static U fold_byte(U c) {
    return c >= 65 && c <= 90 ? c+32 : c;
}

static int case_reference(const B *left, const B *right) {
    for (U i = 0; ; ++i) {
        U a = fold_byte(left[i]), b = fold_byte(right[i]);
        if (!left[i] || !right[i] || a != b) return (int)a-(int)b;
    }
}

static int bounded_case_reference(const B *left, const B *right, U count) {
    for (U i = 0; i < count; ++i) {
        U a = fold_byte(left[i]), b = fold_byte(right[i]);
        if (!left[i] || !right[i] || a != b) return (int)a-(int)b;
    }
    return 0;
}

static int name_equals(const B *input, const char *name) {
    for (U i = 0; ; ++i) {
        if (input[i] != (B)name[i]) return 0;
        if (!input[i]) return 1;
    }
}

static U transformation_reference(const B *input) {
    if (name_equals(input, "toupper")) return 1;
    if (name_equals(input, "tolower")) return 2;
    return 0;
}

static const char *classification_names[] = {"alnum", "alpha", "blank", "cntrl", "digit", "graph", "lower", "print", "punct", "space", "upper", "xdigit"};

static U classification_reference(const B *input) {
    for (U i = 0; i < 12; ++i)
        if (name_equals(input, classification_names[i])) return i+1;
    return 0;
}

static B *first_byte_or_nul_reference(B *s, int needle) {
    B target = (B)needle;
    for (U j = 0; ; ++j)
        if (!s[j] || s[j] == target) return s+j;
}

static B *first_byte_reference(B *s, int needle) {
    B target = (B)needle;
    for (U j = 0; ; ++j) {
        if (s[j] == target) return s+j;
        if (!s[j]) return (B *)0;
    }
}

static B *last_byte_reference(B *s, int needle) {
    B *last = (B *)0;
    B target = (B)needle;
    for (U j = 0; ; ++j) {
        B word = s[j];
        if (word == target) last = s+j;
        if (!word) break;
    }
    return last;
}

static int run(void) {
    const U values[] = {0, 1, 127, 128, 255, 256, 0x12345678u,
                        0x7fffffffu, 0x80000000u, 0xffffffffu};
    for (U i = 0; i < sizeof(values) / sizeof(values[0]); ++i) {
        U x = values[i], magnitude = x < 0x80000000u ? x : 0u - x;
        int alnum = (65 <= x && x <= 90) || (97 <= x && x <= 122) || (48 <= x && x <= 57);
        if (ispunct((int)x) != ((33 <= x && x <= 126) && !alnum)) return 56;
        for (U locale = 0; locale < 10; ++locale)
            if (!locale_classifiers_match(x, (void *)values[locale])) return 55;
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
        U upper = 65 <= x && x <= 90, lower = 97 <= x && x <= 122;
        U digit = 48 <= x && x <= 57;
        if (ispunct((int)x) != ((33 <= x && x <= 126) && !(upper || lower || digit))) return 56;
        if ((U)isalpha((int)x) != (upper || lower)) return 26;
        if ((U)isalnum((int)x) != (upper || lower || digit)) return 27;
        if ((U)isblank((int)x) != (x == 9 || x == 32)) return 28;
        if ((U)iscntrl((int)x) != (x <= 31 || x == 127)) return 29;
        if ((U)isspace((int)x) != ((9 <= x && x <= 13) || x == 32)) return 30;
        if ((U)tolower((int)x) != (upper ? x+32 : x)) return 31;
        if ((U)toupper((int)x) != (lower ? x-32 : x)) return 32;
        if ((U)isxdigit((int)x) != (digit || (65 <= x && x <= 70) || (97 <= x && x <= 102))) return 35;
        for (U locale = 0; locale < 10; ++locale)
            if (!locale_classifiers_match(x, (void *)values[locale])) return 55;
    }
    B a[256], b[256];
    for (U alignment = 0; alignment < 4; ++alignment) {
        for (U n = 0; n < 160; ++n) {
            for (U j = 0; j < 256; ++j) a[j] = (B)(1 + j % 255);
            a[alignment + n] = 0;
            if (strlen((const char *)a + alignment) != n) return 11;
            for (U bound = 0; bound <= n+3; ++bound) {
                U expected = n < bound ? n : bound;
                if (strnlen((const char *)a + alignment, bound) != expected) return 49;
            }
        }
    }
    for (U n = 0; n < 128; ++n) {
        for (U j = 0; j < 256; ++j) a[j] = b[j] = (B)(j * 17);
        if (memcmp(a, b, n) != 0) return 12;
        if (bcmp(a, b, n) != 0) return 38;
        for (U first = 0; first < n; ++first) {
            B old = a[first];
            a[first] = 200; b[first] = 3;
            if (memcmp(a, b, n) != 197 || memcmp(b, a, n) != -197) return 13;
            if (bcmp(a, b, n) != 197 || bcmp(b, a, n) != -197) return 39;
            a[first] = b[first] = old;
        }
    }
    for (U left = 0; left < 4; ++left) for (U right = 0; right < 4; ++right) {
        for (U n = 0; n < 128; ++n) {
            for (U j = 0; j < n; ++j) a[left+j] = b[right+j] = (B)(1+j%255);
            a[left+n] = b[right+n] = 0;
            if (strcoll((char *)a+left, (char *)b+right) != 0) return 105;
            if (strcmp((char *)a+left, (char *)b+right) != 0) return 20;
            for (U locale = 0; locale < 10; ++locale)
                if (strcoll_l((char *)a+left, (char *)b+right, (void *)values[locale]) != 0) return 57;
            for (U first = 0; first < n; ++first) {
                B old = a[left+first];
                a[left+first] = 200; b[right+first] = 3;
                if (strcmp((char *)a+left, (char *)b+right) != 197 ||
                    strcmp((char *)b+right, (char *)a+left) != -197) return 21;
                if (strcoll((char *)a+left, (char *)b+right) != 197 ||
                    strcoll((char *)b+right, (char *)a+left) != -197) return 106;
                for (U locale = 0; locale < 10; ++locale)
                    if (strcoll_l((char *)a+left, (char *)b+right, (void *)values[locale]) != 197 ||
                        strcoll_l((char *)b+right, (char *)a+left, (void *)values[locale]) != -197) return 58;
                a[left+first] = b[right+first] = old;
            }
            b[right+n] = 100; b[right+n+1] = 0;
            if (strcmp((char *)a+left, (char *)b+right) != -100) return 22;
            if (strcoll_l((char *)a+left, (char *)b+right, (void *)0xffffffffu) != -100) return 59;
            if (strcoll((char *)a+left, (char *)b+right) != -100) return 107;
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
    for (U offset = 0; offset < 4; ++offset) for (U n = 0; n < 128; ++n) {
        for (U j = 0; j < 256; ++j) a[j] = (B)(j*73+19);
        for (U value = 0; value < 256; ++value) {
            B *expected = (B *)0;
            for (U j = 0; j < n; ++j)
                if (a[offset+j] == value) { expected = a+offset+j; break; }
            if (memchr(a+offset, (int)value-256, n) != expected) return 46;
        }
        for (U first = 0; first < n; ++first) {
            for (U j = 0; j < 256; ++j) a[j] = 0xa5;
            a[offset+first] = 0x3c;
            a[offset+n-1] = 0x3c;
            if (memchr(a+offset, 0x123c, n) != a+offset+first) return 47;
        }
    }
    if (memchr((void *)0, 42, 0) != (void *)0) return 48;
    if (strnlen((const char *)0, 0) != 0) return 50;
    int wa[52], wb[52];
    const int wide_values[] = {-1, 1, (int)0x80000000u, 0x7fffffff, 42, -42};
    for (U n = 0; n < 48; ++n) {
        for (U j = 0; j < n; ++j) wa[j] = wb[j] = wide_values[j%6];
        wa[n] = wb[n] = 0;
        if (wcscoll(wa, wb) != 0) return 108;
        if (wcscmp(wa, wb) != 0 || wcsncmp(wa, wb, n+1) != 0) return 33;
        for (U locale = 0; locale < 10; ++locale)
            if (wcscoll_l(wa, wb, (void *)values[locale]) != 0) return 60;
        for (U first = 0; first < n; ++first) {
            int old = wa[first];
            for (U aindex = 0; aindex < 6; ++aindex) for (U bindex = 0; bindex < 6; ++bindex) {
                wa[first] = wide_values[aindex]; wb[first] = wide_values[bindex];
                if (wcscoll(wa, wb) != wide_reference(wa, wb, n+1)) return 109;
                if (wcscmp(wa, wb) != wide_reference(wa, wb, n+1)) return 33;
                for (U locale = 0; locale < 10; ++locale)
                    if (wcscoll_l(wa, wb, (void *)values[locale]) != wide_reference(wa, wb, n+1)) return 61;
                for (U count = 0; count <= n+2; ++count)
                    if (wcsncmp(wa, wb, count) != wide_reference(wa, wb, count)) return 34;
            }
            wa[first] = wb[first] = old;
        }
        wb[n] = -42; wb[n+1] = 0;
        if (wcscoll(wa, wb) != 1) return 110;
        if (wcscmp(wa, wb) != 1) return 33;
        if (wcscoll_l(wa, wb, (void *)0xffffffffu) != 1) return 62;
        for (U count = 0; count <= n+2; ++count)
            if (wcsncmp(wa, wb, count) != wide_reference(wa, wb, count)) return 34;
    }
    B transform[20], transform_saved[20];
    const char *transform_names[] = {"toupper", "tolower"};
    for (U offset = 0; offset < 4; ++offset) for (U name = 0; name < 2; ++name) {
        for (U changed = 0; changed < 8; ++changed) for (U value = 0; value < 256; ++value) {
            for (U i = 0; i < 20; ++i) transform[i] = 0xa5;
            for (U i = 0; i < 8; ++i) transform[offset+i] = (B)transform_names[name][i];
            transform[offset+changed] = (B)value;
            transform[offset+8] = 0;
            for (U i = 0; i < 20; ++i) transform_saved[i] = transform[i];
            if ((U)wctrans((char *)transform+offset) != transformation_reference(transform+offset)) return 87;
            for (U locale = 0; locale < 10; ++locale)
                if ((U)wctrans_l((char *)transform+offset, (void *)values[locale]) !=
                    transformation_reference(transform+offset)) return 89;
            for (U i = 0; i < 20; ++i) if (transform[i] != transform_saved[i]) return 88;
        }
    }
    for (U offset = 0; offset < 4; ++offset) for (U name = 0; name < 12; ++name) {
        U length = name == 11 ? 6 : 5;
        for (U changed = 0; changed <= length; ++changed) for (U value = 0; value < 256; ++value) {
            for (U i = 0; i < 20; ++i) transform[i] = 0xa5;
            for (U i = 0; i <= length; ++i) transform[offset+i] = (B)classification_names[name][i];
            transform[offset+changed] = (B)value;
            transform[offset+length+1] = 0;
            for (U i = 0; i < 20; ++i) transform_saved[i] = transform[i];
            if (wctype((char *)transform+offset) != classification_reference(transform+offset)) return 90;
            for (U locale = 0; locale < 10; ++locale)
                if (wctype_l((char *)transform+offset, (void *)values[locale]) !=
                    classification_reference(transform+offset)) return 92;
            for (U i = 0; i < 20; ++i) if (transform[i] != transform_saved[i]) return 91;
        }
    }
    if (strncasecmp((const char *)0, (const char *)0, 0) != 0 ||
        strncasecmp((const char *)0, "X", 0) != 0 || strncasecmp("Y", (const char *)0, 0) != 0) return 98;
    for (U locale = 0; locale < 10; ++locale)
        if (strncasecmp_l((const char *)0, (const char *)0, 0, (void *)values[locale]) != 0 ||
            strncasecmp_l((const char *)0, "X", 0, (void *)values[locale]) != 0 ||
            strncasecmp_l("Y", (const char *)0, 0, (void *)values[locale]) != 0) return 101;
    B append_dst[160], append_src[80], append_expected[160], append_saved[80];
    for (U doff = 0; doff < 4; ++doff) for (U soff = 0; soff < 4; ++soff)
        for (U dn = 0; dn <= 48; ++dn) for (U sn = 0; sn <= 48; ++sn) {
            const U counts[] = {0, 1, sn ? sn-1 : 0, sn, sn+1, 0xffffffffu};
            for (U ci = 0; ci < 6; ++ci) {
                for (U i = 0; i < 160; ++i) append_dst[i] = append_expected[i] = 0xa5;
                for (U i = 0; i < 80; ++i) append_src[i] = append_saved[i] = 0xe5;
                for (U i = 0; i < dn; ++i) append_dst[doff+i] = append_expected[doff+i] = (B)(1+(i*17)%255);
                append_dst[doff+dn] = append_expected[doff+dn] = 0;
                for (U i = 0; i < sn; ++i) append_src[soff+i] = append_saved[soff+i] = (B)(1+(i*73)%255);
                append_src[soff+sn] = append_saved[soff+sn] = 0;
                U copied = sn < counts[ci] ? sn : counts[ci];
                for (U i = 0; i < copied; ++i) append_expected[doff+dn+i] = append_src[soff+i];
                append_expected[doff+dn+copied] = 0;
                if ((B *)strncat((char *)append_dst+doff,
                                ci ? (char *)append_src+soff : (const char *)0, counts[ci]) != append_dst+doff ||
                    memcmp(append_dst, append_expected, 160) || memcmp(append_src, append_saved, 80)) return 111;
            }
        }
    B case_left[96], case_right[96], saved_left[96], saved_right[96];
    for (U aoff = 0; aoff < 4; ++aoff) for (U boff = 0; boff < 4; ++boff) {
        for (U sample = 0; sample < 2; ++sample) {
            U prefix = sample ? 17 : 0;
            for (U i = 0; i < 96; ++i) case_left[i] = case_right[i] = 0xa5;
            for (U i = 0; i < prefix; ++i) {
                case_left[aoff+i] = (B)(65+(i*7)%26);
                case_right[boff+i] = (B)(case_left[aoff+i]+(i%3 ? 32 : 0));
            }
            case_left[aoff+prefix+1] = case_right[boff+prefix+1] = 0;
            for (U a = 0; a < 256; ++a) for (U b = 0; b < 256; ++b) {
                case_left[aoff+prefix] = (B)a;
                case_right[boff+prefix] = (B)b;
                int expected = case_reference(case_left+aoff, case_right+boff);
                if (strcasecmp((char *)case_left+aoff, (char *)case_right+boff) != expected) return 93;
                const U bounds[] = {0, 1, prefix, prefix+1, prefix+2, 0xffffffffu};
                for (U ci = 0; ci < 6; ++ci) {
                    int bounded = bounded_case_reference(case_left+aoff, case_right+boff, bounds[ci]);
                    if (strncasecmp((char *)case_left+aoff, (char *)case_right+boff, bounds[ci]) != bounded) return 99;
                    if (ci == 0 || ci == 3 || ci == 5)
                        for (U locale = 0; locale < 10; ++locale)
                            if (strncasecmp_l((char *)case_left+aoff, (char *)case_right+boff,
                                             bounds[ci], (void *)values[locale]) != bounded) return 102;
                }
                for (U locale = 0; locale < 10; ++locale)
                    if (strcasecmp_l((char *)case_left+aoff, (char *)case_right+boff,
                                     (void *)values[locale]) != expected) return 96;
            }
        }
        for (U n = 0; n <= 64; ++n) {
            for (U i = 0; i < 96; ++i) case_left[i] = case_right[i] = 0xe5;
            for (U i = 0; i < n; ++i) {
                case_left[aoff+i] = (B)(65+(i*11)%26);
                case_right[boff+i] = (B)(case_left[aoff+i]+(i%2 ? 32 : 0));
            }
            case_left[aoff+n] = case_right[boff+n] = 0;
            for (U stop = 0; stop <= n; ++stop) {
                B old = case_right[boff+stop];
                case_right[boff+stop] = 0;
                for (U i = 0; i < 96; ++i) { saved_left[i] = case_left[i]; saved_right[i] = case_right[i]; }
                int expected = case_reference(case_left+aoff, case_right+boff);
                if (strcasecmp((char *)case_left+aoff, (char *)case_right+boff) != expected ||
                    strcasecmp((char *)case_right+boff, (char *)case_left+aoff) != -expected) return 94;
                for (U locale = 0; locale < 10; ++locale)
                    if (strcasecmp_l((char *)case_left+aoff, (char *)case_right+boff,
                                     (void *)values[locale]) != expected) return 97;
                if (strncasecmp((char *)case_left+aoff, (char *)case_right+boff, stop+1) !=
                        bounded_case_reference(case_left+aoff, case_right+boff, stop+1) ||
                    strncasecmp((char *)case_left+aoff, (char *)case_right+boff, 0xffffffffu) != expected) return 100;
                for (U locale = 0; locale < 10; ++locale)
                    if (strncasecmp_l((char *)case_left+aoff, (char *)case_right+boff,
                                     stop+1, (void *)values[locale]) !=
                            bounded_case_reference(case_left+aoff, case_right+boff, stop+1) ||
                        strncasecmp_l((char *)case_left+aoff, (char *)case_right+boff,
                                     0xffffffffu, (void *)values[locale]) != expected) return 103;
                if (memcmp(case_left, saved_left, 96) || memcmp(case_right, saved_right, 96)) return 95;
                case_right[boff+stop] = old;
            }
        }
    }
    B rsearch[144];
    for (U offset = 0; offset < 4; ++offset) for (U n = 0; n <= 128; ++n) {
        for (U j = 0; j < 144; ++j) rsearch[j] = (B)(1+(j*73)%255);
        rsearch[offset+n] = 0;
        for (U v = 0; v < 512; ++v) {
            int needle = (int)v-256;
            if ((B *)strrchr((char *)rsearch+offset, needle) !=
                last_byte_reference(rsearch+offset, needle)) return 72;
            if ((B *)rindex((char *)rsearch+offset, needle) !=
                last_byte_reference(rsearch+offset, needle)) return 104;
            if ((B *)strchrnul((char *)rsearch+offset, needle) !=
                first_byte_or_nul_reference(rsearch+offset, needle)) return 77;
            if ((B *)strchr((char *)rsearch+offset, needle) !=
                first_byte_reference(rsearch+offset, needle)) return 82;
            if ((B *)index((char *)rsearch+offset, needle) !=
                first_byte_reference(rsearch+offset, needle)) return 104;
        }
        for (U v = 0; v < 10; ++v) {
            if ((B *)strrchr((char *)rsearch+offset, (int)values[v]) !=
                last_byte_reference(rsearch+offset, (int)values[v])) return 73;
            if ((B *)rindex((char *)rsearch+offset, (int)values[v]) !=
                last_byte_reference(rsearch+offset, (int)values[v])) return 104;
            if ((B *)strchrnul((char *)rsearch+offset, (int)values[v]) !=
                first_byte_or_nul_reference(rsearch+offset, (int)values[v])) return 78;
            if ((B *)strchr((char *)rsearch+offset, (int)values[v]) !=
                first_byte_reference(rsearch+offset, (int)values[v])) return 83;
            if ((B *)index((char *)rsearch+offset, (int)values[v]) !=
                first_byte_reference(rsearch+offset, (int)values[v])) return 104;
        }
        for (U last = 0; last < n; ++last) {
            for (U j = 0; j < 144; ++j) rsearch[j] = 0xa5;
            rsearch[offset] = rsearch[offset+last] = 0xff;
            rsearch[offset+n] = 0;
            rsearch[offset+n+1] = 0xff;
            if ((B *)strrchr((char *)rsearch+offset, -1) != rsearch+offset+last ||
                (B *)strrchr((char *)rsearch+offset, 0x1234ff) != rsearch+offset+last) return 74;
            if ((B *)rindex((char *)rsearch+offset, -1) != rsearch+offset+last ||
                (B *)rindex((char *)rsearch+offset, 0x1234ff) != rsearch+offset+last) return 104;
            if ((B *)strrchr((char *)rsearch+offset, 256) != rsearch+offset+n) return 75;
            if ((B *)rindex((char *)rsearch+offset, 256) != rsearch+offset+n) return 104;
            rsearch[offset+n+1] = 2;
            if (strrchr((char *)rsearch+offset, 2) != (char *)0) return 76;
            if (rindex((char *)rsearch+offset, 2) != (char *)0) return 104;
        }
    }
    for (U offset = 0; offset < 4; ++offset) for (U n = 1; n <= 128; ++n) {
        for (U first = 0; first < n; ++first) {
            for (U j = 0; j < 144; ++j) rsearch[j] = 0x80;
            rsearch[offset+first] = rsearch[offset+n-1] = 0xff;
            rsearch[offset+n] = 0;
            rsearch[offset+n+1] = 2;
            if ((B *)strchrnul((char *)rsearch+offset, -1) != rsearch+offset+first) return 79;
            if ((B *)strchrnul((char *)rsearch+offset, 256) != rsearch+offset+n) return 80;
            if ((B *)strchrnul((char *)rsearch+offset, 2) != rsearch+offset+n) return 81;
            if ((B *)strchr((char *)rsearch+offset, -1) != rsearch+offset+first ||
                (B *)strchr((char *)rsearch+offset, 0x1234ff) != rsearch+offset+first) return 84;
            if ((B *)index((char *)rsearch+offset, -1) != rsearch+offset+first ||
                (B *)index((char *)rsearch+offset, 0x1234ff) != rsearch+offset+first) return 104;
            if ((B *)strchr((char *)rsearch+offset, 256) != rsearch+offset+n) return 85;
            if ((B *)index((char *)rsearch+offset, 256) != rsearch+offset+n) return 104;
            if (strchr((char *)rsearch+offset, 2) != (char *)0) return 86;
            if (index((char *)rsearch+offset, 2) != (char *)0) return 104;
        }
    }
    int search[80];
    const int search_values[] = {1, -1, (int)0x80000000u, 0x7fffffff, 0x100,
                                 0x10000, -42, 42, 0xff00};
    for (U offset = 0; offset < 4; ++offset) for (U n = 0; n <= 64; ++n) {
        for (U j = 0; j < 80; ++j) search[j] = search_values[(j*5)%9];
        search[offset+n] = 0;
        for (U v = 0; v < 10; ++v) {
            int needle = (int)values[v];
            int *expected = (int *)0;
            for (U j = 0; ; ++j) {
                int word = search[offset+j];
                if (word == needle) { expected = search+offset+j; break; }
                if (!word) break;
            }
            if (wcschr(search+offset, needle) != expected) return 63;
            int *last = (int *)0;
            for (U j = 0; ; ++j) {
                int word = search[offset+j];
                if (word == needle) last = search+offset+j;
                if (!word) break;
            }
            if (wcsrchr(search+offset, needle) != last) return 67;
        }
        for (U first = 0; first < n; ++first) {
            for (U j = 0; j < 80; ++j) search[j] = 0x100;
            search[offset+n] = 0;
            search[offset+first] = search[offset+n-1] = 0x12345678;
            if (wcschr(search+offset, 0x12345678) != search+offset+first) return 64;
            if (wcschr(search+offset, 0) != search+offset+n) return 65;
            search[offset+n+1] = -42;
            if (wcschr(search+offset, -42) != (int *)0) return 66;
            if (wcsrchr(search+offset, 0x12345678) != search+offset+n-1) return 68;
            if (wcsrchr(search+offset, 0) != search+offset+n) return 69;
            if (wcsrchr(search+offset, -42) != (int *)0) return 70;
        }
    }
    for (U offset = 0; offset < 4; ++offset) for (U n = 1; n <= 64; ++n) {
        for (U last = 0; last < n; ++last) {
            for (U j = 0; j < 80; ++j) search[j] = 0x100;
            search[offset] = search[offset+last] = (int)0x80000000u;
            search[offset+n] = 0;
            search[offset+n+1] = (int)0x80000000u;
            if (wcsrchr(search+offset, (int)0x80000000u) != search+offset+last) return 71;
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
    for (U offset = 0; offset < 4; ++offset) for (U n = 0; n <= 128; ++n) {
        for (U j = 0; j < 136; ++j) filled[j] = (int)(0x80000000u+j*257u);
        filled[offset+n] = 0;
        if (wcslen(filled+offset) != n) return 40;
        for (U bound = 0; bound <= n+3; ++bound) {
            U expected = n < bound ? n : bound;
            if (wcsnlen(filled+offset, bound) != expected) return 51;
        }
    }
    if (wcsnlen((const int *)0, 0) != 0) return 52;
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
        unsigned long long magnitude = bits < (1ull<<63) ? bits : 0ull-bits;
        if ((unsigned long long)llabs((long long)bits) != magnitude) return 36;
        if ((unsigned long long)imaxabs((long long)bits) != magnitude) return 37;
    }
    for (U c = 0; c <= 0x110000u; ++c) {
        int digit = 48 <= c && c <= 57;
        int hex = digit || (65 <= c && c <= 70) || (97 <= c && c <= 102);
        int control = c <= 31 || (127 <= c && c <= 159) ||
            (8232 <= c && c <= 8233) || (65529 <= c && c <= 65531);
        if (iswdigit(c) != digit) return 41;
        if (iswxdigit(c) != hex) return 42;
        if (iswcntrl(c) != control || iswcntrl_l(c, (void *)0xffffffffu) != control) return 43;
        if (iswblank(c) != (c == 9 || c == 32)) return 45;
        if (iswdigit_l(c, (void *)0xffffffffu) != digit ||
            iswxdigit_l(c, (void *)0xffffffffu) != hex ||
            iswblank_l(c, (void *)0xffffffffu) != (c == 9 || c == 32)) return 53;
    }
    for (U i = 0; i < 10; ++i) {
        U c = values[i];
        int digit = 48 <= c && c <= 57;
        int hex = digit || (65 <= c && c <= 70) || (97 <= c && c <= 102);
        int control = c <= 31 || (127 <= c && c <= 159) ||
            (8232 <= c && c <= 8233) || (65529 <= c && c <= 65531);
        if (iswdigit(c) != digit || iswxdigit(c) != hex || iswcntrl(c) != control ||
            iswblank(c) != (c == 9 || c == 32)) return 44;
        for (U locale = 0; locale < 10; ++locale) {
            if (iswcntrl_l(c, (void *)values[locale]) != control ||
                iswdigit_l(c, (void *)values[locale]) != digit ||
                iswxdigit_l(c, (void *)values[locale]) != hex ||
                iswblank_l(c, (void *)values[locale]) != (c == 9 || c == 32)) return 54;
        }
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
