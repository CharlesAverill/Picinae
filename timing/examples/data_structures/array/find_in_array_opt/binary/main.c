#include "../../../../timing_experiments.h"
#include "array_opt.h"

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    for (uint32_t len = 1; len <= 1000; ++len) {
        uint32_t array[1000];
        for (uint32_t i = 0; i < len; i++)
            array[i] = rand();

        int insert_index = -1;
        uint32_t key = rand();
        if (rand() % 2) {
            insert_index = rand() % len;
            array[insert_index] = key;
        }

	START_TIMER;
        uint32_t result = find_in_array(array, key, len);
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

