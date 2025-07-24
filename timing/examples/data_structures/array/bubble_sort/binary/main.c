#include "../../../timing_experiments.h"
#include "bubble_sort.h"

void test_array(char[] prefix, uint32_t[] array, uint32_t len){
    START_TIMER;
    bubble_sort_theta_n2(array, len);
    PRINT_TIMER;

    char str[128];
    itoa(len, str, 10);
    puts(prefix); puts("Len: "); puts(str); puts("\n");
}

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    for (uint32_t len = 1; len <= 100; ++len) {
        uint32_t array[100];
        // Test random arrangement
        for (uint32_t i = 0; i < len; i++) {
            array[i] = rand();
        }
        test_array("RAND ", array, len);
        // Test best-case performance
        for (uint32_t i = 0; i < len; i++) {
            array[i] = i;
        }
        test_array("BEST ", array, len);
        // Test worst-case performance
        for (uint32_t i = 0; i < len; i++) {
            array[i] = len - i - 1;
        }
        test_array("WORST ", array, len);
    }

    return 0;
}

