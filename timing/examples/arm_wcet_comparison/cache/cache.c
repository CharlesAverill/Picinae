#include <stdint.h>
#include <stdlib.h>

/* STM32F0DISCOVERY (Cortex-M0): no DWT cycle counter, so time with SysTick.
   SysTick is a 24-bit down-counter clocked from the core clock. */
#define SYST_CSR (*(volatile uint32_t*)0xE000E010)
#define SYST_RVR (*(volatile uint32_t*)0xE000E014)
#define SYST_CVR (*(volatile uint32_t*)0xE000E018)

static inline void systick_init(void) {
    SYST_CSR = 0;
    SYST_RVR = 0x00FFFFFF;
    SYST_CVR = 0;
    SYST_CSR = 0x5; /* CLKSOURCE = core clock, ENABLE, no interrupt */
}

/* Elapsed cycles between two SysTick reads (handles one wraparound) */
static inline uint32_t systick_elapsed(uint32_t start, uint32_t end) {
    return (start - end) & 0x00FFFFFF;
}

/* Inspect with a debugger after stuff() returns */
volatile uint32_t avg_cycles;

int __attribute__ ((noinline, noipa)) sum(int* arr, uint32_t size) {
    int x = 0;
    for (uint32_t i = 0; i < size; i++) {
        x += arr[i];
    }
    return x;
}

int __attribute__ ((noinline)) stuff(int* arr, int size) {
    uint32_t sum_cycles = 0;

    uint32_t extra_cycles = 0;
    int sum_acc = 0;
    int iters = 1000;

    systick_init();

    for (int j = 0; j < iters; j++) {
        for (int i = 0; i < size; i++) {
            arr[i] = rand();
        }

        uint32_t start, end, cycles1, cycles2;

        start = SYST_CVR;
        end = SYST_CVR;
        extra_cycles += systick_elapsed(start, end);

        start = SYST_CVR;
        int s1 = sum(arr, size);
        end = SYST_CVR;
        cycles1 = systick_elapsed(start, end);

        start = SYST_CVR;
        int s2 = sum(arr, size);
        end = SYST_CVR;
        cycles2 = systick_elapsed(start, end);

        sum_acc += s1 + s2;

        sum_cycles += cycles1 + cycles2;
    }

    uint32_t extra = extra_cycles / iters;
    avg_cycles = sum_cycles / (2 * iters) - extra;

    return sum_acc;
}

/*
int main(void) {
    static int arr[1000];

    stuff(arr, 1000);

    while (1);
}
*/
