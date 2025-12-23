#include <stdlib.h>
#include <stdint.h>

/*
 * Multiplexer: returns x if ctl == 1, y if ctl == 0.
 * https://www.bearssl.org/gitweb/?p=BearSSL;a=blob;f=src/inner.h
 */
static inline uint32_t
MUX(uint32_t ctl, uint32_t x, uint32_t y)
{
        return y ^ (-ctl & (x ^ y));
}


/*
 * Conditional copy - copy src -> dst if ctl = 1
 * https://www.bearssl.org/gitweb/?p=BearSSL;a=blob;f=src/codec/ccopy.c
 */
void
br_ccopy(uint32_t ctl, void *dst, const void *src, size_t len)
{
        unsigned char *d;
        const unsigned char *s;

        d = dst;
        s = src;
        while (len -- > 0) {
                uint32_t x, y;

                x = *s ++;
                y = *d;
                *d = MUX(ctl, x, y);
                d ++;
        }
}
