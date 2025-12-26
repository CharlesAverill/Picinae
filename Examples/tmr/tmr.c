#include <stdlib.h>
#include <stdbool.h>

inline int CRYPTO_memcmp(const void *in_a, const void *in_b, size_t len)
{
    size_t i;
    const volatile unsigned char *a = in_a;
    const volatile unsigned char *b = in_b;
    unsigned char x = 0;

    for (i = 0; i < len; i++)
        x |= a[i] ^ b[i];

    return x;
}

bool check_password_tmr(const char* stored, const char* user, size_t len) {
    int a = CRYPTO_memcmp(stored, user, len);
    int b = CRYPTO_memcmp(stored, user, len);
    int c = CRYPTO_memcmp(stored, user, len);

    return (a & b) | (a & c) | (b & c);
}
