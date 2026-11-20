/* Picinae e04 extraction fixture; this configuration is part of the binary ABI. */
#ifndef PICINAE_FREERTOS_CONFIG_H
#define PICINAE_FREERTOS_CONFIG_H

#define configENABLE_MPU                         0
/* Cortex-M0 has no architectural VTOR. Supply vectors at address zero. */
#define configCHECK_HANDLER_INSTALLATION         0
#define configCPU_CLOCK_HZ                       12000000UL
#define configTICK_RATE_HZ                       1000U
#define configTICK_TYPE_WIDTH_IN_BITS            TICK_TYPE_WIDTH_32_BITS
#define configNUMBER_OF_CORES                    1
#define configUSE_PREEMPTION                     1
#define configUSE_TIME_SLICING                    1
#define configMAX_PRIORITIES                      5U
#define configMINIMAL_STACK_SIZE                 256U
#define configMAX_TASK_NAME_LEN                  16U
#define configUSE_PORT_OPTIMISED_TASK_SELECTION   0
#define configUSE_TICKLESS_IDLE                   0
#define configIDLE_SHOULD_YIELD                   1
#define configSUPPORT_STATIC_ALLOCATION          1
#define configSUPPORT_DYNAMIC_ALLOCATION         0
#define configKERNEL_PROVIDED_STATIC_MEMORY      0
#define configUSE_TASK_NOTIFICATIONS             1
#define configTASK_NOTIFICATION_ARRAY_ENTRIES    1
#define configUSE_MUTEXES                        1
#define configUSE_RECURSIVE_MUTEXES              1
#define configUSE_COUNTING_SEMAPHORES            1
#define configUSE_QUEUE_SETS                     0
#define configQUEUE_REGISTRY_SIZE                0
#define configUSE_EVENT_GROUPS                   1
#define configUSE_STREAM_BUFFERS                 1
#define configUSE_SB_COMPLETED_CALLBACK          0
#define configUSE_TIMERS                         1
#define configTIMER_TASK_PRIORITY                2U
#define configTIMER_QUEUE_LENGTH                 8U
#define configTIMER_TASK_STACK_DEPTH             256U
#define configUSE_TRACE_FACILITY                 0
#define configUSE_STATS_FORMATTING_FUNCTIONS     0
#define configGENERATE_RUN_TIME_STATS            0
#define configUSE_NEWLIB_REENTRANT               0
#define configUSE_POSIX_ERRNO                    0
#define configNUM_THREAD_LOCAL_STORAGE_POINTERS  0
#define configUSE_IDLE_HOOK                      0
#define configUSE_TICK_HOOK                      0
#define configCHECK_FOR_STACK_OVERFLOW           0
#define configUSE_MALLOC_FAILED_HOOK             0
#define configUSE_CO_ROUTINES                    0
#define configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES 0
#define INCLUDE_vTaskPrioritySet                 1
#define INCLUDE_uxTaskPriorityGet                1
#define INCLUDE_vTaskDelete                      1
#define INCLUDE_vTaskSuspend                     1
#define INCLUDE_xTaskResumeFromISR               1
#define INCLUDE_vTaskDelay                       1
#define INCLUDE_xTaskDelayUntil                  1
#define INCLUDE_xTaskAbortDelay                  1
#define INCLUDE_xTaskGetCurrentTaskHandle        1
#define INCLUDE_xTaskGetSchedulerState           1
#define INCLUDE_xTaskGetHandle                   1
#define INCLUDE_xSemaphoreGetMutexHolder         1
#define INCLUDE_eTaskGetState                    1
#define INCLUDE_uxTaskGetStackHighWaterMark       1
#define INCLUDE_uxTaskGetStackHighWaterMark2      1
#define INCLUDE_xTimerPendFunctionCall           1
#define INCLUDE_xTimerGetTimerDaemonTaskHandle   1

#ifndef __ASSEMBLER__
void fixture_assert_fail(const char *file, unsigned line) __attribute__((noreturn));
#define configASSERT(condition) do { if (!(condition)) fixture_assert_fail(__FILE__, __LINE__); } while (0)
#endif
#endif
