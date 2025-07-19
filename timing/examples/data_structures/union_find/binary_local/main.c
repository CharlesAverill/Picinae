#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include "union_find.h" // Your DSU interface

int main() {
    srand(42);  // Reproducible randomness

    for (uint32_t n = 3; n <= 1000; ++n) {
        struct set *s = make_set(n);

        // Pick two elements to union
        uint32_t x = 0;
	while (x == 0)
		x = rand() % n;
        uint32_t y = x;
	while (x == y || y == 0)
		y = rand() % n;

        // Time a single union operation
        _union(x, y, s);

	printf("Set size: %d, union: %d %d\n", n, x, y);
	free(s->parent); free(s->rank); free(s);
    }

    return 0;
}

