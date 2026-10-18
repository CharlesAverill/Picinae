#include <stdint.h>
#include <stdbool.h>

// Return the number of steps for n to reach 1, or 0 if it does not within
// 55000 steps. The slow path doesn't affect the result, so the compiler
// removes it.
uint32_t collatz(uint16_t n) {
    // int start = rdtsc();
    uint32_t i;
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
            for (int i = 1; i < 100; i++) {
                n = n * i + n % i;
            }
        }
        return 0;
    } else {
        // int end = rdtsc();
        // printf("cycles: %d\n", end - start);
        return i;
    }
}

/*
int main(int argc, char* argv[]) {
    collatz(5252);
    collatz(52527);
    return 0;
    for (int i = 1; i < 100; i++) {
        // printf("[Trial %d]\n", i);
        collatz(i);
    }
}
*/
