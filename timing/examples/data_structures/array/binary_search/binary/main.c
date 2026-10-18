#include <stdlib.h>
#include "../../../../timing_experiments.h"
#include "binary_search.h"

#define MAX_LEN 1000

// Static so that len up to MAX_LEN fits (the stack is too small for it)
static uint32_t array[MAX_LEN];

static int cmp_u32(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    return (x > y) - (x < y);
}

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    for (uint32_t len = 1; len <= MAX_LEN; ++len) {
        for (uint32_t i = 0; i < len; i++)
            array[i] = rand();
        qsort(array, len, sizeof(uint32_t), cmp_u32);

        // Half the time search for an element of the array, otherwise a random key
        uint32_t key = (rand() % 2) ? array[rand() % len] : (uint32_t)rand();

	START_TIMER;
        uint32_t result = binary_search(array, len, key);
        PRINT_TIMER;

        char str[128];
        puts("Len: "); itoa(len, str, 10); puts(str);
        puts(", key: "); itoa(key, str, 10); puts(str);
        puts(result < len ? " found" : " not found\n");
	if (result < len) {
	        puts(" at index "); itoa(result, str, 10); puts(str); puts("\n");
	}
    }

    return 0;
}
