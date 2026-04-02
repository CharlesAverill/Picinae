// Generated from Bedrock code. Avoid editing directly.
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), "signed size");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, "pointer fits in int");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, "two's complement");

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, "little-endian");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian");
#elif defined(_MSC_VER) && !defined(__clang__) &&	                          \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error "failed to confirm that target is little-endian"
#endif

// "An object shall have its stored value accessed only ... a character type."
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load(br_word_t a) {
  br_word_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline void _br_store1(br_word_t a, uint8_t v) {
  *((uint8_t *)a) = v;
}

static inline void _br_store2(br_word_t a, uint16_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store4(br_word_t a, uint32_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store(br_word_t a, br_word_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
	  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, low, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}

static br_word_t chacha20_quarter(br_word_t a, br_word_t b, br_word_t c, br_word_t d, br_word_t* _a, br_word_t* _b, br_word_t* _c);

void chacha20_block(br_word_t out, br_word_t key, br_word_t nonce, br_word_t countervalue) {
  br_word_t i, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15;
  x0 = (br_word_t)0x61707865;
  x1 = (br_word_t)0x3320646e ;
  x2 = (br_word_t)0x79622d32;
  x3 = (br_word_t)0x6b206574;
  x4 = _br_load4(key);
  x5 = _br_load4(key+4);
  x6 = _br_load4(key+8);
  x7 = _br_load4(key+12);
  x8 = _br_load4(key+16);
  x9 = _br_load4(key+20);
  x10 = _br_load4(key+24);
  x11 = _br_load4(key+28);
  x12 = countervalue;
  x13 = _br_load4(nonce);
  x14 = _br_load4(nonce+4);
  x15 = _br_load4(nonce+8);
  i = (br_word_t)0;
  while ((br_word_t)(i<(br_word_t)10)) {
    i = i+1;
    x12 = chacha20_quarter(x0, x4, x8, x12, &x0, &x4, &x8);
    x13 = chacha20_quarter(x1, x5, x9, x13, &x1, &x5, &x9);
    x14 = chacha20_quarter(x2, x6, x10, x14, &x2, &x6, &x10);
    x15 = chacha20_quarter(x3, x7, x11, x15, &x3, &x7, &x11);
    x15 = chacha20_quarter(x0, x5, x10, x15, &x0, &x5, &x10);
    x12 = chacha20_quarter(x1, x6, x11, x12, &x1, &x6, &x11);
    x13 = chacha20_quarter(x2, x7, x8, x13, &x2, &x7, &x8);
    x14 = chacha20_quarter(x3, x4, x9, x14, &x3, &x4, &x9);
  }
  x0 = x0+0x61707865;
  x1 = x1+0x3320646e ;
  x2 = x2+0x79622d32;
  x3 = x3+0x6b206574;
  x4 = x4+(_br_load4(key));
  x5 = x5+(_br_load4(key+4));
  x6 = x6+(_br_load4(key+8));
  x7 = x7+(_br_load4(key+12));
  x8 = x8+(_br_load4(key+16));
  x9 = x9+(_br_load4(key+20));
  x10 = x10+(_br_load4(key+24));
  x11 = x11+(_br_load4(key+28));
  x12 = x12+countervalue;
  x13 = x13+(_br_load4(nonce));
  x14 = x14+(_br_load4(nonce+4));
  x15 = x15+(_br_load4(nonce+8));
  _br_store4(out+0, (_br_load4(out+0))^x0);
  _br_store4(out+4, (_br_load4(out+4))^x1);
  _br_store4(out+8, (_br_load4(out+8))^x2);
  _br_store4(out+12, (_br_load4(out+12))^x3);
  _br_store4(out+16, (_br_load4(out+16))^x4);
  _br_store4(out+20, (_br_load4(out+20))^x5);
  _br_store4(out+24, (_br_load4(out+24))^x6);
  _br_store4(out+28, (_br_load4(out+28))^x7);
  _br_store4(out+32, (_br_load4(out+32))^x8);
  _br_store4(out+36, (_br_load4(out+36))^x9);
  _br_store4(out+40, (_br_load4(out+40))^x10);
  _br_store4(out+44, (_br_load4(out+44))^x11);
  _br_store4(out+48, (_br_load4(out+48))^x12);
  _br_store4(out+52, (_br_load4(out+52))^x13);
  _br_store4(out+56, (_br_load4(out+56))^x14);
  _br_store4(out+60, (_br_load4(out+60))^x15);
}

static br_word_t chacha20_quarter(br_word_t a, br_word_t b, br_word_t c, br_word_t d, br_word_t* _a, br_word_t* _b, br_word_t* _c) {
  a = a+b;
  d = d^a;
  d = d<<16;
  c = c+d;
  b = b^c;
  b = b<<12;
  a = a+b;
  d = d^a;
  d = d<<8;
  c = c+d;
  b = b^c;
  b = b<<7;
  *_a = a;
  *_b = b;
  *_c = c;
  return d;
}

#include "../../../timing_experiments.h"

void chacha20_encrypt(const uint8_t* plaintext, uint8_t* ciphertext,
                      size_t len, const br_word_t key,
                      const br_word_t nonce, br_word_t counter) {
    size_t offset = 0;
    uint8_t keystream[64];

    while (offset < len) {
        // Generate next 64-byte block
        START_TIMER;
        chacha20_block((br_word_t)keystream, key, nonce, counter++);
        PRINT_TIMER;

        // XOR plaintext with keystream
        size_t block_len = (len - offset) < 64 ? (len - offset) : 64;
        for (size_t i = 0; i < block_len; i++) {
            ciphertext[offset + i] = plaintext[offset + i] ^ keystream[i];
        }

        offset += block_len;
    }
}

int main() {
  neorv32_rte_setup();
  neorv32_uart0_setup(BAUD_RATE, 0);

  const char *msg = "Hello world!";
  size_t len = strlen(msg);

  for (int i = 0; i < 100; i++) {
    uint8_t ciphertext[len];
    uint8_t key[32] = {i};
    uint8_t nonce[12] = {i + 1};
    br_word_t counter = 1;

    chacha20_encrypt((const uint8_t*)msg, ciphertext, len, (br_word_t)key, (br_word_t)nonce, counter);
  }

  return 0;
}
