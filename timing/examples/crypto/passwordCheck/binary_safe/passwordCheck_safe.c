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

        p_expected++;
        p_user++;

        if (eax == 0 || ecx == 0) break;  // check user byte before next iteration
    }

    if (!equal && trace_level >= 1) {
        DpLock();
        DpTrace(NULL, "%s: password check failed\n", "passwordCheck");
        DpUnlock();
    }

    return equal ? 0 : -94;
}

/* --- tiny test harness --- */
int main(void)
{
    const unsigned char correct[] = "S3cr3t!";
    int rc;

    rc = passwordCheck_safe(correct, (const unsigned char *)"S3cr3t!");
    printf("match rc=%d\n", rc);

    rc = passwordCheck_safe(correct, (const unsigned char *)"S3cr3x!");
    printf("mismatch rc=%d\n", rc);

    rc = passwordCheck_safe(correct, (const unsigned char *)"S3cr3t!extra");
    printf("long user rc=%d\n", rc);

    return 0;
}
