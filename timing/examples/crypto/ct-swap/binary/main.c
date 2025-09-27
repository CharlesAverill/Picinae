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
	ct_swap((uint32_t)0, (uint32_t*)0, (uint32_t*)0, (size_t)0);
}
