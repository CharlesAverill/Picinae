#include "../../../timing_experiments.h"
#include "bubble_sort.h"

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    for (uint32_t len = 1; len <= 100; ++len) {
        uint32_t array[100];
        for (uint32_t i = 0; i < len; i++)
            array[i] = rand();

	    START_TIMER;
        uint32_t result = bubble_sort_theta_n2(array, len);
        PRINT_TIMER;

        char str[128];
        puts("Len: "); itoa(len, str, 10); puts(str);
    }

    return 0;
}

