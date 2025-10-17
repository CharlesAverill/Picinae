#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <limits.h>

typedef struct list_node {
   uint32_t value;
   struct list_node* next;
} list_node;

void insert_after_pos_in_list(list_node* l, list_node* value, uint32_t position);
list_node* find_in_list(list_node* l, uint32_t key);
void insert_in_sorted_list(list_node* l, list_node* value);


void insert_after_pos_in_list(list_node* l, list_node* value, uint32_t position) {
   if (l == NULL || value == NULL)
	return;

   for (uint32_t i = 0; i < position; i++) {
       if (l->next == NULL)
	       break;
       l = l->next;
   }
   value->next = l->next;
   l->next = value;
}

#pragma RVS [insert_after_pos_in_list@L1] loop_max_iter (130)

list_node* find_in_list(list_node* l, uint32_t key) {
    if (l == NULL)
	    return NULL;

    while (l != NULL) {
    	if (l->value == key)
            return l;
        l = l->next;
    }

    return NULL;
}

#pragma RVS [find_in_list@L1] loop_max_iter (130)

void insert_in_sorted_list(list_node* l, list_node* value) {
    list_node* iter = l;

    if (value->value == INT_MAX) {
        // Skip
    } else {
        /* Find first node > value */
        for (;
             iter->next->value <= value->value;
             iter = iter->next) {
            /* nothing inside loop */
        }
    }

    /* Insert newNode after iter */
    value->next = iter->next;
    iter->next = value;
}

#pragma RVS [find_in_list@L1] loop_max_iter (130)

#define LIST_SIZE 128  // large enough to exercise loops

static list_node nodes[LIST_SIZE + 2]; // +2 for sentinel and extra inserts

int main(void) {
    for (int idx = 0; idx < 1000; idx++) {
        /* Build a sorted linked list of size LIST_SIZE with ascending values */
        for (int i = 0; i < LIST_SIZE; i++) {
            nodes[i].value = i;
            nodes[i].next = &nodes[i+1];
        }
        // Sentinel node at the end
        nodes[LIST_SIZE].value = INT_MAX;
        nodes[LIST_SIZE].next = NULL;

        list_node* head = &nodes[0];

        /* Exercise insert_after_pos_in_list with worst-case position (deepest loop) */
        list_node* new1 = &nodes[LIST_SIZE+1];
        new1->value = 9999;
        insert_after_pos_in_list(head, new1, rand() % LIST_SIZE);

        /* Exercise find_in_list with worst-case key (not present, traverses full list) */
        volatile list_node* found = find_in_list(head, rand() % 2 == 0 ? INT_MAX : (rand() % LIST_SIZE));
        (void)found; // prevent optimization

        /* Exercise insert_in_sorted_list with worst-case (insert at end before sentinel) */
        list_node extra;
        extra.value = LIST_SIZE + 500; // bigger than all but sentinel
        insert_in_sorted_list(head, &extra);
    }

    return 0;
}
