#include <stdint.h>

struct set {
	uint32_t size;
	uint32_t *parent;
	uint32_t *rank;
};

struct set* make_set(uint32_t n);
uint32_t find(uint32_t x, struct set *s);
void _union(uint32_t x, uint32_t y, struct set *s);
