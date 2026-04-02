#include "../../../timing_experiments.h"
#include "linked_list.h"

#define MAX_ITEMS 128
static uint8_t heap_area[MAX_ITEMS * sizeof(list_node)];
static size_t heap_offset = 0;

static void *xMalloc(size_t bytes) {
    if (heap_offset + bytes > sizeof(heap_area)) {
        puts("Out of static heap!\n");
        exit(1);
    }
    void *ptr = &heap_area[heap_offset];
    heap_offset += bytes;
    return ptr;
}

// #define xMalloc malloc

static struct list_node* make_random_list(uint32_t len) {
    struct list_node* head = (struct list_node*)xMalloc(sizeof(struct list_node));
    struct list_node* curr = head;
    for (uint32_t i = 0; i < len; i++) {
        struct list_node* node = (struct list_node*)xMalloc(sizeof(struct list_node));
        node->value = rand() % 1000;
        curr->next = node;
        curr = node;
    }
    curr->next = NULL;
    return head;
}

static void free_list(struct list_node* head) {
    // struct list_node* tmp;
    // while (head) {
    //     tmp = head->next;
    //     // free(head);
    //     head = tmp;
    // }
    heap_offset = 0;
}

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);
    srand(42);
    char str[64];

    // ============================================================
    // 1. find_in_list
    // ============================================================
    puts("\n=== find_in_list ===\n");
    for (uint32_t len = 1; len <= 100; ++len) {
        struct list_node* head = make_random_list(len);

        // 50% chance key exists
        uint32_t key;
        if (rand() % 2) {
            uint32_t pos = rand() % len;
            struct list_node* node = head;
            for (uint32_t i = 0; i < pos; i++) node = node->next;
            key = node->value; // ensure hit
        } else {
            key = 10000 + rand(); // ensure miss
        }

        START_TIMER;
        struct list_node* found = find_in_list(head, key);
        PRINT_TIMER;

        uint32_t idx;
        struct list_node* temp = head;
        for(idx = 0; idx < len; idx++) {
            if(temp == found)
                break;
            temp = temp->next;
        }

        printf("Len: %d, ", len);
        if (found) {
            printf("found @ %d\n", idx);
        } else {
            printf("not found\n");
        }

        free_list(head);
    }

    heap_offset = 0;

    // ============================================================
    // 2. insert_after_pos_in_list
    // ============================================================
    puts("\n=== insert_after_pos_in_list ===\n");
    for (uint32_t len = 1; len <= 100; ++len) {
        struct list_node* head = make_random_list(len);
        uint32_t pos = rand() % len;

        struct list_node* new_node = (struct list_node*)xMalloc(sizeof(struct list_node));
        new_node->value = rand() % 1000;
        new_node->next = NULL;

        START_TIMER;
        insert_after_pos_in_list(head, new_node, pos);
        PRINT_TIMER;

        puts("Len: "); itoa(len, str, 10); puts(str);
        puts(", Pos: "); itoa(pos, str, 10); puts(str);
        puts(", Inserted: "); itoa(new_node->value, str, 10); puts(str);
        puts("\n");

        free_list(head);
    }

    heap_offset = 0;

    // ============================================================
    // 3. insert_in_sorted_list
    // ============================================================
    // puts("\n=== insert_in_sorted_list ===\n");
    // for (uint32_t len = 1; len <= 100; ++len) {
    //     struct list_node* head = NULL;
    //     // build sorted ascending list
    //     for (uint32_t i = 0; i < len; i++) {
    //         struct list_node* node = (struct list_node*)xMalloc(sizeof(struct list_node));
    //         node->value = i == i * 10 + (rand() % 5);
    //         node->next = head;
    //         head = node;
    //     }

    //     struct list_node* new_node = (struct list_node*)xMalloc(sizeof(struct list_node));
    //     new_node->value = rand() % (len * 10);
    //     new_node->next = NULL;

    //     START_TIMER;
    //     insert_in_sorted_list(head, new_node);
    //     PRINT_TIMER;

    //     puts("Len: "); itoa(len, str, 10); puts(str);
    //     puts(", Inserted: "); itoa(new_node->value, str, 10); puts(str);
    //     puts("\n");

    //     free_list(head);
    // }

    puts("Done\n");

    return 0;
}
