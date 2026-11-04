/* Platform fixture only. All kernel implementations come from official source. */
#include <stdint.h>
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"
#include "semphr.h"
#include "event_groups.h"
#include "stream_buffer.h"
#include "timers.h"

extern uint32_t _sidata, _sdata, _edata, _sbss, _ebss, _estack;
extern void SVC_Handler(void), PendSV_Handler(void), SysTick_Handler(void);
void Reset_Handler(void);
static void Default_Handler(void) { for (;;) { __asm volatile ("wfi"); } }

/* Core vectors only; external IRQ wiring is a board integration contract. */
__attribute__((used, section(".isr_vector")))
const uintptr_t fixture_vectors[16] = {
    (uintptr_t)&_estack, (uintptr_t)Reset_Handler,
    (uintptr_t)Default_Handler, (uintptr_t)Default_Handler,
    0, 0, 0, 0, 0, 0, 0, (uintptr_t)SVC_Handler,
    0, 0, (uintptr_t)PendSV_Handler, (uintptr_t)SysTick_Handler
};

volatile unsigned fixture_assert_line;
const char * volatile fixture_assert_file;
void fixture_assert_fail(const char *file, unsigned line)
{
    __asm volatile ("cpsid i" ::: "memory");
    fixture_assert_file = file;
    fixture_assert_line = line;
    for (;;) { __asm volatile ("wfi"); }
}

void vApplicationGetIdleTaskMemory(StaticTask_t **tcb, StackType_t **stack,
                                  uint32_t *depth)
{
    static StaticTask_t idle_tcb;
    static StackType_t idle_stack[configMINIMAL_STACK_SIZE];
    *tcb = &idle_tcb; *stack = idle_stack; *depth = configMINIMAL_STACK_SIZE;
}

void vApplicationGetTimerTaskMemory(StaticTask_t **tcb, StackType_t **stack,
                                   uint32_t *depth)
{
    static StaticTask_t timer_tcb;
    static StackType_t timer_stack[configTIMER_TASK_STACK_DEPTH];
    *tcb = &timer_tcb; *stack = timer_stack; *depth = configTIMER_TASK_STACK_DEPTH;
}

static StaticTask_t worker_tcb;
static StackType_t worker_stack[configMINIMAL_STACK_SIZE];
static StaticQueue_t queue_storage, mutex_storage;
static uint8_t queue_bytes[4 * sizeof(uint32_t)];
static StaticEventGroup_t event_storage;
static StaticStreamBuffer_t stream_storage;
static uint8_t stream_bytes[65];
static StaticTimer_t timer_storage;
static QueueHandle_t fixture_queue;
static SemaphoreHandle_t fixture_mutex;
static EventGroupHandle_t fixture_events;
static StreamBufferHandle_t fixture_stream;

static void timer_callback(TimerHandle_t timer)
{
    (void)timer;
    (void)xEventGroupSetBits(fixture_events, 1U);
}

static void worker(void *argument)
{
    uint32_t value = 0;
    (void)argument;
    for (;;) {
        if (xSemaphoreTake(fixture_mutex, 0) == pdTRUE) {
            (void)xQueueSend(fixture_queue, &value, 0);
            (void)xQueueReceive(fixture_queue, &value, 0);
            (void)xStreamBufferSend(fixture_stream, &value, sizeof(value), 0);
            (void)xStreamBufferReceive(fixture_stream, &value, sizeof(value), 0);
            (void)xSemaphoreGive(fixture_mutex);
        }
        ++value;
        vTaskDelay(1);
    }
}

static void fixture_main(void)
{
    fixture_queue = xQueueCreateStatic(4, sizeof(uint32_t), queue_bytes, &queue_storage);
    fixture_mutex = xSemaphoreCreateMutexStatic(&mutex_storage);
    fixture_events = xEventGroupCreateStatic(&event_storage);
    fixture_stream = xStreamBufferCreateStatic(sizeof(stream_bytes), 1, stream_bytes, &stream_storage);
    TimerHandle_t timer = xTimerCreateStatic("fixture-timer", 100, pdTRUE, 0,
                                             timer_callback, &timer_storage);
    configASSERT(fixture_queue && fixture_mutex && fixture_events && fixture_stream && timer);
    configASSERT(xTaskCreateStatic(worker, "fixture-worker", configMINIMAL_STACK_SIZE,
                                  0, 1, worker_stack, &worker_tcb));
    configASSERT(xTimerStart(timer, 0) == pdPASS);
    vTaskStartScheduler();
    fixture_assert_fail(__FILE__, __LINE__);
}

void Reset_Handler(void)
{
    uint32_t *src = &_sidata;
    for (uint32_t *dst = &_sdata; dst < &_edata; ) *dst++ = *src++;
    for (uint32_t *dst = &_sbss; dst < &_ebss; ) *dst++ = 0;
    fixture_main();
}
