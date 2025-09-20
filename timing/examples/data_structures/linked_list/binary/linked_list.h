#include "../../../timing_experiments.h"

typedef struct list_node {
   uint32_t value;
   struct list_node* next;
} list_node;

void insert_after_pos_in_list(list_node* l, list_node* value, uint32_t position);
list_node* find_in_list(list_node* l, uint32_t key);
void insert_in_sorted_list(list_node* l, list_node* value);
