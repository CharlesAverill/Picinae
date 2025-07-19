#include "union_find.h"
#include <stdlib.h>

struct set* make_set(uint32_t n) {
	uint32_t *parent = malloc(sizeof(uint32_t) * n);
	uint32_t *rank = malloc(sizeof(uint32_t) * n);

	for (uint32_t i = 0; i < n; i++) {
		parent[i] = i;
		rank[i] = 0;
	}

	struct set *s = malloc(sizeof(struct set));
	s->size = n;
	s->parent = parent;
	s->rank = rank;
	return s;
}	

uint32_t find(uint32_t x, struct set *s) {
	uint32_t root = x;

	while (root != s->parent[root])
		root = s->parent[root];

	while (root != s->parent[x]) {
		uint32_t tmp = s->parent[x];
		s->parent[x] = root;
		x = tmp;
	}

	return root;
}

void _union(uint32_t x, uint32_t y, struct set *s) {
	uint32_t root_x = find(x, s);
	uint32_t root_y = find(y, s);

	if (root_x == root_y)
		return;

	if (s->rank[root_x] < s->rank[root_y]) {
		s->parent[root_x] = root_y;
	} else if (s->rank[root_x] > s->rank[root_y]) {
		s->parent[root_y] = root_x;
	} else {
		s->parent[root_y] = root_x;
		s->rank[root_x]++;
	}
}
