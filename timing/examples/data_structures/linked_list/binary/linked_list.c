
#include "linked_list.h"
#include <limits.h>

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
