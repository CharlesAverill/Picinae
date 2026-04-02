#include "../../../timing_experiments.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>  // for offsetof
#include <neorv32.h>

#define NUM_ITERS 200

static uint32_t uxSchedulerSuspended __attribute__((aligned(4))) = 0;
static uint32_t xYieldPendings __attribute__((aligned(4))) = 0;
static uint32_t uxTopReadyPriority __attribute__((aligned(4))) = 0;

// External assembly implementation
extern void vTaskSwitchContext(void);

// List item structure (define first)
typedef struct ListItem {
    uint32_t xItemValue;       // offset 0
    struct ListItem *pxNext;   // offset 4
    struct ListItem *pxPrevious; // offset 8
    void *pvOwner;             // offset 12
    void *pvContainer;         // offset 16
} ListItem;  // Total size: 20 bytes

// Fake TCB struct with proper stack overflow markers
// Real FreeRTOS TCB has stack markers at offset 48
typedef struct FakeTCB {
    uint32_t pxTopOfStack;        // offset 0
    ListItem xStateListItem;      // offset 4  (20 bytes)
    ListItem xEventListItem;      // offset 24 (20 bytes)
    uint32_t uxPriority;          // offset 44
    // Stack overflow check markers at offset 48
    uint32_t xDummy1[4];             // offset 48
    uint32_t padding[10];         // extra padding for safety
} __attribute__((aligned(4))) FakeTCB;

static FakeTCB tcbPool[32];

// List structure  
typedef struct List {
    uint32_t uxNumberOfItems;
    ListItem *pxIndex;
    ListItem xListEnd;
} List;

static List readyLists[10];

static FakeTCB *pxCurrentTCB __attribute__((aligned(4))) = {0};
static List *pxReadyTasksLists[10] __attribute__((aligned(4))) = {0};

static void init_tcb_pool(void) {
    for (int i = 0; i < 32; i++) {
        // Initialize ListItems to safe values
        tcbPool[i].xStateListItem.xItemValue = 0;
        tcbPool[i].xStateListItem.pxNext = NULL;
        tcbPool[i].xStateListItem.pxPrevious = NULL;
        tcbPool[i].xStateListItem.pvOwner = &tcbPool[i];
        tcbPool[i].xStateListItem.pvContainer = NULL;
        
        tcbPool[i].xEventListItem.xItemValue = 0;
        tcbPool[i].xEventListItem.pxNext = NULL;
        tcbPool[i].xEventListItem.pxPrevious = NULL;
        tcbPool[i].xEventListItem.pvOwner = &tcbPool[i];
        tcbPool[i].xEventListItem.pvContainer = NULL;
        
        tcbPool[i].uxPriority = 0;
        
        // Initialize stack overflow markers at offset 48
        // Verify offset is correct
        uint32_t *markers = tcbPool[i].xDummy1;
        markers[0] = 0;
        markers[1] = 0;
        markers[2] = 0;
        markers[3] = 0;
        
        tcbPool[i].pxTopOfStack = 0xDEADBEEF;  // dummy stack pointer
    }
    
    // Verify offset calculation
    printf("TCB size: %lu bytes\n", sizeof(FakeTCB));
    printf("xDummy1 offset: %lu (should be 48)\n", 
           offsetof(FakeTCB, xDummy1));
}

static void init_ready_lists(void) {
    for (int i = 0; i < 10; i++) {
        readyLists[i].uxNumberOfItems = 1;
        readyLists[i].xListEnd.pxNext = &readyLists[i].xListEnd;
        readyLists[i].xListEnd.pxPrevious = &readyLists[i].xListEnd;
        readyLists[i].pxIndex = &readyLists[i].xListEnd;
        
        // Point to a TCB
        readyLists[i].xListEnd.pvOwner = &tcbPool[i % 32];
    }
}

static void test_vTaskSwitchContext(void) {
    puts("\n=== Test: vTaskSwitchContext ===\n");

    printf("%p\n", &pxCurrentTCB);
    
    init_tcb_pool();
    init_ready_lists();

    printf("%p\n", &pxCurrentTCB);
    
    const uint32_t suspended = 0;
        for (uint32_t topPrio = 0; topPrio <= 9; topPrio++) {
            for (uint32_t tcb_idx = 0; tcb_idx < 5; tcb_idx++) {  // reduced iterations
                
                /* Set scheduler state */
                uxSchedulerSuspended = suspended;
                xYieldPendings = 0;
                uxTopReadyPriority = (1 << topPrio);  // bitmap, not index
                pxCurrentTCB = &tcbPool[tcb_idx];
                
                // Set up ready lists pointers
                for (int i = 0; i < 10; i++) {
                    pxReadyTasksLists[i] = &readyLists[i];
                }
                
                printf("Test: suspended=%u, topPrio=%u, tcb=%u\n",
                       suspended, topPrio, tcb_idx);

                *((*pxCurrentTCB).xDummy1) = 0;
                printf("%p\n", *((*pxCurrentTCB).xDummy1));
                
                /* Pass ADDRESSES of variables to assembly */
                asm volatile (
                    "mv s7, %0\n\t"
                    "mv s8, %1\n\t"
                    "mv s9, %2\n\t"
                    "mv s10, %3\n\t"
                    "mv s11, %4\n\t"
                    :
                    : "r"(&suspended),
                      "r"(&xYieldPendings),
                      "r"(&uxTopReadyPriority),
                      "r"(&pxCurrentTCB),
                      "r"(&pxReadyTasksLists)
                    : "s7","s8","s9","s10","s11"
                );
                
                START_TIMER;
                vTaskSwitchContext();
                PRINT_TIMER;
            }
        }
    
    puts("\nTiming tests complete.\n");
}

int main(void) {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);
    
    srand(42);
    puts("Starting vTaskSwitchContext timing tests...\n");
    
    test_vTaskSwitchContext();
    
    puts("\nAll tests complete.\n");
    return 0;
}
