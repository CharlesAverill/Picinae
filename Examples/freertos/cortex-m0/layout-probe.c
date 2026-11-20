/* Compile-only probes: include each unmodified private definition in its own TU.
 * These objects NEVER enter the firmware. Read constants, never run ARM code. */
#include <stddef.h>
#include <stdint.h>
#if defined(PROBE_tasks)
#include "tasks.c"
#elif defined(PROBE_queue)
#include "queue.c"
#elif defined(PROBE_event_groups)
#include "event_groups.c"
#elif defined(PROBE_stream_buffer)
#include "stream_buffer.c"
#elif defined(PROBE_timers)
#include "timers.c"
#endif
#define SIZE(t) { #t ".sizeof", sizeof(t) }, { #t ".alignof", _Alignof(t) }
#define FIELD(t, f) { #t "." #f, offsetof(t, f) }
struct layout_record { char name[80]; uint32_t value; };
_Static_assert(sizeof(struct layout_record) == 84, "layout record format");
__attribute__((used, section(".picinae_layout")))
const struct layout_record fixture_layout[] = {
#if defined(PROBE_tasks)
    SIZE(TCB_t), FIELD(TCB_t, pxTopOfStack), FIELD(TCB_t, xStateListItem),
    FIELD(TCB_t, xEventListItem), FIELD(TCB_t, uxPriority), FIELD(TCB_t, pxStack),
    FIELD(TCB_t, pcTaskName), FIELD(TCB_t, uxBasePriority), FIELD(TCB_t, uxMutexesHeld),
    FIELD(TCB_t, ulNotifiedValue), FIELD(TCB_t, ucNotifyState), FIELD(TCB_t, ucDelayAborted),
    SIZE(StaticTask_t), SIZE(StackType_t), SIZE(TickType_t), SIZE(BaseType_t),
    SIZE(UBaseType_t), SIZE(void *),
    SIZE(TimeOut_t), FIELD(TimeOut_t, xOverflowCount), FIELD(TimeOut_t, xTimeOnEntering),
    SIZE(ListItem_t), FIELD(ListItem_t, xItemValue), FIELD(ListItem_t, pxNext),
    FIELD(ListItem_t, pxPrevious), FIELD(ListItem_t, pvOwner), FIELD(ListItem_t, pxContainer),
    SIZE(MiniListItem_t), FIELD(MiniListItem_t, xItemValue),
    FIELD(MiniListItem_t, pxNext), FIELD(MiniListItem_t, pxPrevious),
    SIZE(List_t), FIELD(List_t, uxNumberOfItems), FIELD(List_t, pxIndex), FIELD(List_t, xListEnd),
#elif defined(PROBE_queue)
    SIZE(Queue_t), SIZE(StaticQueue_t), FIELD(Queue_t, pcHead), FIELD(Queue_t, pcWriteTo),
    FIELD(Queue_t, u.xQueue.pcTail), FIELD(Queue_t, u.xQueue.pcReadFrom),
    FIELD(Queue_t, u.xSemaphore.xMutexHolder), FIELD(Queue_t, u.xSemaphore.uxRecursiveCallCount),
    FIELD(Queue_t, xTasksWaitingToSend), FIELD(Queue_t, xTasksWaitingToReceive),
    FIELD(Queue_t, uxMessagesWaiting), FIELD(Queue_t, uxLength), FIELD(Queue_t, uxItemSize),
    FIELD(Queue_t, cRxLock), FIELD(Queue_t, cTxLock),
#elif defined(PROBE_event_groups)
    SIZE(EventGroup_t), SIZE(StaticEventGroup_t), FIELD(EventGroup_t, uxEventBits),
    FIELD(EventGroup_t, xTasksWaitingForBits),
#elif defined(PROBE_stream_buffer)
    SIZE(StreamBuffer_t), SIZE(StaticStreamBuffer_t), FIELD(StreamBuffer_t, xTail),
    FIELD(StreamBuffer_t, xHead), FIELD(StreamBuffer_t, xLength),
    FIELD(StreamBuffer_t, xTriggerLevelBytes), FIELD(StreamBuffer_t, xTaskWaitingToReceive),
    FIELD(StreamBuffer_t, xTaskWaitingToSend), FIELD(StreamBuffer_t, pucBuffer),
    FIELD(StreamBuffer_t, ucFlags), FIELD(StreamBuffer_t, uxNotificationIndex),
#elif defined(PROBE_timers)
    SIZE(Timer_t), SIZE(StaticTimer_t), FIELD(Timer_t, pcTimerName),
    FIELD(Timer_t, xTimerListItem), FIELD(Timer_t, xTimerPeriodInTicks),
    FIELD(Timer_t, pvTimerID), FIELD(Timer_t, pxCallbackFunction), FIELD(Timer_t, ucStatus),
#endif
};
