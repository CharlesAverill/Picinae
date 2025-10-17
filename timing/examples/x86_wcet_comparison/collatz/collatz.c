#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

// static inline uint64_t rdtsc(void) {
//     unsigned int lo, hi;
//     __asm__ volatile ("rdtsc" : "=a"(lo), "=d"(hi));
//     return ((uint64_t)hi << 32) | lo;
// }

// Return whether n ends up in a collatz cycle 
int collatz(uint16_t n) {
    // int start = rdtsc();
    int i;
    for (i = 0; i < 55000; i++) {
        if (n % 2 == 0)
            n /= 2;
        else
            n = 3 * n + 1;

        if (n == 1)
            break;
    }

    if (n != 1) {
        for (int j = 0; j < 100; j++) {
            for (int i = 0; i < 100; i++) {
                n = n * i + n % i;
            }
        }
    } else {
        // int end = rdtsc();
        // printf("cycles: %d\n", end - start);
        return i;
    }
}

int main(int argc, char* argv[]) {
    collatz(5252);
    collatz(52527);
    fflush(stdout);
    return 0;
    for (int i = 0; i < 100; i++) {
        // printf("[Trial %d]\n", i);
        collatz(i);
    }
}
