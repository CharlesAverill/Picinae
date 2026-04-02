#include "../../../timing_experiments.h"

#include <stddef.h>
#include <stdint.h>

void ct_swap(uint32_t secret, uint32_t *a, uint32_t *b, size_t len) {
	uint32_t delta;
	uint32_t mask = ~(secret-1);
	for (size_t i = 0; i < len; i++) {
		delta = (a[i] ^ b[i]) & mask;
		a[i] = a[i] ^ delta;
		b[i] = b[i] ^ delta;
	}
}

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);

    for (uint32_t len = 1; len <= 100; ++len) {
        uint32_t a[100];
        uint32_t b[100];

        // Fill arrays with random values
        for (uint32_t i = 0; i < len; i++) {
            a[i] = rand();
            b[i] = rand();
        }

        // Run both secret = 0 and secret = 1 cases
        for (uint32_t secret = 0; secret <= 1; ++secret) {
			printf("Len: %d\n", len);
            START_TIMER;
            ct_swap(secret, a, b, len);
            PRINT_TIMER;
        }
    }

    return 0;
}
