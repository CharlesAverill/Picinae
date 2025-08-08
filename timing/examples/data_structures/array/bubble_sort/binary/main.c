#include "../../../timing_experiments.h"
#include "bubble_sort.h"
#include <string.h>

#define MAX_LEN 100

inline void swap(uint32_t* x, uint32_t* y) {
    uint32_t temp = *x;
    *x = *y;
    *y = temp;
}

void bubble_sort_theta_n2_measure_swaps(uint32_t* arr, uint32_t size) {
    for (uint32_t i = 0; i < size; i++) {
        for (uint32_t j = 0; j < size - 1; j++) {
            if (arr[j] > arr[j + 1]) {
		printf("(%u, %u) ", i, j);
                swap(&arr[j], &arr[j + 1]);
            }
        }
    }
}

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    for (uint32_t len = 1; len <= MAX_LEN; ++len) {
        uint32_t array[MAX_LEN];
        for (uint32_t i = 0; i < len; i++) {
            array[i] = rand();
        }

	// Get swaps
	uint32_t dupe[MAX_LEN];
	memcpy(dupe, array, len);
	printf("Swaps: [");
	bubble_sort_theta_n2_measure_swaps(dupe, len);
	printf("]\n");

	START_TIMER;
        bubble_sort_theta_n2(array, len);
        PRINT_TIMER;

        char str[128];
        puts("Len: "); itoa(len, str, 10); puts(str); puts("\n");
    }

    return 0;
}

