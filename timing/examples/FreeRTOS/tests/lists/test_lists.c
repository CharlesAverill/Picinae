#include "../../../timing_experiments.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_ITERS 200

// Accurate FreeRTOS-compatible structures (32-bit)
typedef struct xLIST_ITEM {
    uint32_t xItemValue;
    struct xLIST_ITEM *pxNext;
    struct xLIST_ITEM *pxPrevious;
    void *pvOwner;
    struct xLIST *pxContainer;
} ListItem_t;

typedef struct xLIST {
    uint32_t uxNumberOfItems;
    ListItem_t *pxIndex;
    ListItem_t xListEnd;
} List_t;

typedef uint32_t UBaseType_t;

// External list functions (assembly or linked from FreeRTOS)
extern void vListInitialise(List_t *pxList);
extern void vListInitialiseItem(ListItem_t *pxItem);
extern void vListInsert(List_t *pxList, ListItem_t *pxNewListItem);
extern void vListInsertEnd(List_t *pxList, ListItem_t *pxNewListItem);
extern UBaseType_t uxListRemove(ListItem_t *pxItem);

// -----------------------------------------------------------------------------
// Utility functions
// -----------------------------------------------------------------------------
#define MAX_ITEMS 1024
static uint8_t heap_area[MAX_ITEMS * sizeof(ListItem_t)];
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

// Allocate and initialise a new list item with a random value
static ListItem_t *new_item(void) {
    ListItem_t *item = (ListItem_t *)xMalloc(sizeof(ListItem_t));
    vListInitialiseItem(item);
    item->xItemValue = rand();
    return item;
}

// -----------------------------------------------------------------------------
// Individual tests
// -----------------------------------------------------------------------------
static void test_insert(void) {
    puts("\n=== Test: vListInsert ===\n");
    List_t testList;
    vListInitialise(&testList);

    for (uint32_t iter = 0; iter < NUM_ITERS; ++iter) {
        ListItem_t *item = new_item();
        printf("Iteration %u: inserting new item (value=%u)\n", iter, item->xItemValue);

        START_TIMER;
        vListInsert(&testList, item);
        PRINT_TIMER;
    }

    puts("Cleaning up inserted items...\n");
    // Remove and free all items in list
    ListItem_t *node = testList.xListEnd.pxNext;
    while (node != &(testList.xListEnd)) {
        ListItem_t *next = node->pxNext;
        uxListRemove(node);
        //free(node);
        node = next;
    }
}

static void test_insert_end(void) {
    puts("\n=== Test: vListInsertEnd ===\n");
    List_t testList;
    vListInitialise(&testList);

    for (uint32_t iter = 0; iter < NUM_ITERS; ++iter) {
        ListItem_t *item = new_item();
        printf("Iteration %u: inserting new item at end (value=%u)\n", iter, item->xItemValue);

        START_TIMER;
        vListInsertEnd(&testList, item);
        PRINT_TIMER;
    }

    puts("Cleaning up inserted items...\n");
    ListItem_t *node = testList.xListEnd.pxNext;
    while (node != &(testList.xListEnd)) {
        ListItem_t *next = node->pxNext;
        uxListRemove(node);
        //free(node);
        node = next;
    }
}

static void test_remove(void) {
    puts("\n=== Test: uxListRemove ===\n");
    List_t testList;
    vListInitialise(&testList);

    // Prepopulate the list with items
    ListItem_t *allItems[NUM_ITERS];
    for (uint32_t i = 0; i < NUM_ITERS; ++i) {
        allItems[i] = new_item();
        vListInsertEnd(&testList, allItems[i]);
    }

    // Randomly remove items
    for (uint32_t iter = 0; iter < NUM_ITERS; ++iter) {
        uint32_t idx = rand() % NUM_ITERS;
        ListItem_t *item = allItems[idx];
        // if (rand() % 10 == 0) {
        //     item->pxContainer->pxIndex = item;
        // }
        if (item && item->pxContainer != NULL) {
            printf("Iteration %u: removing item[%u] (value=%u) (nxtctr=l := %d)\n",
                   iter, idx, item->xItemValue, (item->pxContainer)->pxIndex == item);
            START_TIMER;
            uxListRemove(item);
            PRINT_TIMER;
            //free(item);
            allItems[idx] = NULL;
        }
    }

    // Free any remaining unremoved items
    for (uint32_t i = 0; i < NUM_ITERS; ++i) {
        //if (allItems[i]) free(allItems[i]);
    }
}

static void test_reinitialise(void) {
    puts("\n=== Test: vListInitialise (reinit) ===\n");
    List_t testList;

    for (uint32_t iter = 0; iter < NUM_ITERS; ++iter) {
        printf("Iteration %u: reinitialising list\n", iter);
        START_TIMER;
        vListInitialise(&testList);
        PRINT_TIMER;
    }
}

static void test_initialise_item(void) {
    puts("\n=== test: vListInitialiseItem ===\n");
    ListItem_t testItem;

    for (uint32_t iter = 0; iter < NUM_ITERS; ++iter) {
        printf("Iteration %u: initialising item\n", iter);
        START_TIMER;
        vListInitialiseItem(&testItem);
        PRINT_TIMER;
    }
}

// -----------------------------------------------------------------------------
// Main entry point
// -----------------------------------------------------------------------------
int main(void) {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);
    srand(42);

    puts("Starting FreeRTOS list operation timing tests (dynamic items)...\n");

    test_insert();
    heap_offset = 0;
    test_insert_end();
    heap_offset = 0;
    test_remove();
    heap_offset = 0;
    test_reinitialise();
    heap_offset = 0;
    test_initialise_item();

    puts("\nTiming tests complete.\n");
    return 0;
}

