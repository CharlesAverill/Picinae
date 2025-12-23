#include <stdlib.h>

// https://github.com/openssl/openssl/blob/6f73fe1c688dc3e4c3815e8f33e5b672abeb28d3/crypto/cpuid.c#L198
// Constant-time memcmp implementation in OpenSSL
int CRYPTO_memcmp(const void *in_a, const void *in_b, size_t len)
{
    size_t i;
    const volatile unsigned char *a = in_a;
    const volatile unsigned char *b = in_b;
    unsigned char x = 0;

    for (i = 0; i < len; i++)
        x |= a[i] ^ b[i];

    return x;
}
