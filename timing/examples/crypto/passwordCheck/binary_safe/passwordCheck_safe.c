#include "../../../timing_experiments.h"

/* mimic CS:trace_level from the disassembly */
int trace_level = 0;

/* Minimal stubs for the tracing primitives visible in the disassembly.
   In the real program these would be proper logging/locking functions. */
void DpLock(void)   { /* stub - acquire lock */ }
void DpUnlock(void) { /* stub - release lock */ }
void DpTrace(void *ctx, const char *fmt, ...) {
    /* stub - do trace logging (variadic omitted for brevity) */
    (void)ctx;
    (void)fmt;
}

/* Return codes chosen to match the disassembly:
   0        => success (xor eax,eax)
   -94 (0xFFFFFFA2) => failure (mov eax,0FFFFFFA2h)
*/
int passwordCheck_safe(const unsigned char *stored, const unsigned char *user)
{
    /* Pointers correspond to rdi (stored) and rsi (user) in the disasm. */
    const unsigned char *p_expected = stored;
    const unsigned char *p_user = user;

    bool equal = true;

    for (;;) {
        unsigned int ecx = *p_expected;
        unsigned int eax = *p_user;

        equal &= (ecx == eax) | (ecx == 0);

        __asm__ volatile (
            "addi %[expected], %[expected], 1\n\t"   // p_expected++
            "snez t0, %[eax]\n\t"                    // t0 = (eax != 0)
            "add  %[user], %[user], t0\n\t"          // p_user += (eax != 0)
            : [expected] "+r" (p_expected),
              [user]     "+r" (p_user)
            : [eax]      "r"  (eax)
            : "t0", "memory"
        );

        if (eax == 0) break;  // check user byte before next iteration
    }

    if (!equal && trace_level >= 1) {
        DpLock();
        DpTrace(NULL, "%s: password check failed\n", "passwordCheck");
        DpUnlock();
    }

    return equal ? 0 : -94;
}

#define MAX_LEN 128
#define NUM_TESTS 10

#include <string.h>

static void make_random_password(unsigned char *buf, size_t len) {
    const char alphabet[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    for (size_t i = 0; i < len - 1; i++) {
        buf[i] = alphabet[rand() % (sizeof(alphabet) - 1)];
    }
    buf[len - 1] = '\0';
}

int main(void) {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);
    srand(42);

    unsigned char stored[MAX_LEN];
    unsigned char user[MAX_LEN * 2];

    puts("\n=== passwordCheck_safe timing ===\n");

    for (uint32_t len = 4; len <= MAX_LEN; len += 4) {
        for (uint32_t test = 0; test < NUM_TESTS; test++) {
            make_random_password(stored, len);

            // --------------------------
            // Case 1: Exact match
            // --------------------------
            strcpy((char*)user, (const char*)stored);
            printf("Len: %d\n", strlen((const char*)user));
            START_TIMER;
            passwordCheck_safe(stored, user);
            PRINT_TIMER;

            // --------------------------
            // Case 2: Mismatch (last byte flipped)
            // --------------------------
            strcpy((char*)user, (const char*)stored);
            user[len - 2] ^= 0x01;  // Flip one bit
            printf("Len: %d\n", strlen((const char*)user));
            START_TIMER;
            passwordCheck_safe(stored, user);
            PRINT_TIMER;

            // --------------------------
            // Case 3: Longer user input
            // --------------------------
            strcpy((char*)user, (const char*)stored);
            strcat((char*)user, "extra");
            printf("Len: %d\n", strlen((const char*)user));
            START_TIMER;
            passwordCheck_safe(stored, user);
            PRINT_TIMER;
        }
    }

    puts("Done\n");
    return 0;
}
