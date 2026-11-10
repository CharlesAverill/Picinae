/* Minimal Cortex-M0 startup: vector table, .data/.bench copy, .bss zero. */
#include <stdint.h>

extern uint32_t _sidata[], _sdata[], _edata[], _sbss[], _ebss[], _estack[];
extern uint32_t _sibench[], _sbench[], _ebench[];
int main(void);

static void copy(uint32_t *src, uint32_t *dst, uint32_t *end)
{
    while (dst < end) *dst++ = *src++;
}

void Reset_Handler(void)
{
    __asm volatile ("cpsid i" ::: "memory");
    copy(_sidata, _sdata, _edata);
    if ((uintptr_t)_sibench != (uintptr_t)_sbench)   /* SRAM build */
        copy(_sibench, _sbench, _ebench);
    for (uint32_t *p = _sbss; p < _ebss; ) *p++ = 0;
    main();
    for (;;) { }
}

/* A fault leaves the mailbox magic unset/stale; the host times out. */
static void Fault_Handler(void) { for (;;) { } }

__attribute__((section(".isr_vector"), used))
static void (* const vectors[16])(void) = {
    (void (*)(void))_estack,
    Reset_Handler,
    Fault_Handler,   /* NMI */
    Fault_Handler,   /* HardFault */
};
