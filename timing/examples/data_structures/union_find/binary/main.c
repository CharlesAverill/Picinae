#include "../../timing_experiments.h"
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include "union_find.h" // Your DSU interface

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    srand(42);  // Reproducible randomness

    for (uint32_t n = 3; n <= 1000; ++n) {
        struct set *s = make_set(n);
	if (s == NULL) {
		puts("make_set failed");
		break;
	}

        // Pick two elements to union
        uint32_t x = 0;
	while (x == 0)
		x = rand() % n;
        uint32_t y = x;
	while (x == y || y == 0)
		y = rand() % n;

        // Time a single union operation
        START_TIMER;
        _union(x, y, s);
        PRINT_TIMER;

	char str[128];
        puts("Set size: "); itoa(n, str, 10); puts(str);
        puts(", Union: "); itoa(x, str, 10); puts(str);
        puts(" & "); itoa(y, str, 10); puts(str);
        
	free(s->parent); free(s->rank); free(s);
    }

    return 0;
}

