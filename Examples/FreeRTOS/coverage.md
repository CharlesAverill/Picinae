# FreeRTOS extraction coverage

Exact ELF `5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca`. 41/41 extracted; 0/41 rejected.
24/41 have transitive calls to strictly rejected helpers. Full e05 is PARTIAL.
Extraction and kernel decode/typing checks are not functional correctness proofs.

| Row | Function | Entry | Extraction | First strict rejection | Closure prerequisites | Rejected helpers in closure |
|---|---|---|---|---|---|---|
| r01 | [vListInitialiseItem](vListInitialiseItem.json) | `0x00000056` | extracted | — | 0 | — |
| r02 | [vListInitialise](vListInitialise.json) | `0x00000040` | extracted | — | 0 | — |
| r03 | [vListInsertEnd](vListInsertEnd.json) | `0x0000005c` | extracted | — | 0 | — |
| r04 | [uxListRemove](uxListRemove.json) | `0x000000a0` | extracted | — | 0 | — |
| r05 | [vListInsert](vListInsert.json) | `0x00000072` | extracted | — | 0 | — |
| r06 | [uxTaskGetNumberOfTasks](uxTaskGetNumberOfTasks.json) | `0x0000059c` | extracted | — | 0 | — |
| r07 | [xTaskGetCurrentTaskHandle](xTaskGetCurrentTaskHandle.json) | `0x000012dc` | extracted | — | 0 | — |
| r08 | [xTaskGetTickCount](xTaskGetTickCount.json) | `0x00000584` | extracted | — | 0 | — |
| r09 | [xTaskGetTickCountFromISR](xTaskGetTickCountFromISR.json) | `0x00000590` | extracted | — | 0 | — |
| r10 | [vTaskSuspendAll](vTaskSuspendAll.json) | `0x00000574` | extracted | — | 0 | — |
| r11 | [vTaskMissedYield](vTaskMissedYield.json) | `0x000009c0` | extracted | — | 0 | — |
| r12 | [uxTaskPriorityGet](uxTaskPriorityGet.json) | `0x00000284` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r13 | [uxTaskResetEventItemValue](uxTaskResetEventItemValue.json) | `0x00001524` | extracted | — | 0 | — |
| r14 | [vTaskInternalSetTimeOutState](vTaskInternalSetTimeOutState.json) | `0x00000908` | extracted | — | 0 | — |
| r15 | [vTaskSetTimeOutState](vTaskSetTimeOutState.json) | `0x000008d4` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r16 | [xTaskGenericNotifyStateClear](xTaskGenericNotifyStateClear.json) | `0x000018ec` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r17 | [ulTaskGenericNotifyValueClear](ulTaskGenericNotifyValueClear.json) | `0x00001934` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r18 | [pvTaskIncrementMutexHeldCount](pvTaskIncrementMutexHeldCount.json) | `0x0000153c` | extracted | — | 0 | — |
| r19 | [xTaskGetSchedulerState](xTaskGetSchedulerState.json) | `0x000012fc` | extracted | — | 0 | — |
| r20 | [uxQueueMessagesWaiting](uxQueueMessagesWaiting.json) | `0x00002040` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r21 | [uxQueueSpacesAvailable](uxQueueSpacesAvailable.json) | `0x00002064` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r22 | [xQueueGetMutexHolder](xQueueGetMutexHolder.json) | `0x00001f0c` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r23 | [xQueueGetMutexHolderFromISR](xQueueGetMutexHolderFromISR.json) | `0x00001f38` | extracted | — | 1 | fixture_assert_fail |
| r24 | [eTaskGetState](eTaskGetState.json) | `0x000001e0` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r25 | [prvTaskIsTaskSuspended](prvTaskIsTaskSuspended.json) | `0x000003e4` | extracted | — | 1 | fixture_assert_fail |
| r26 | [prvResetNextTaskUnblockTime](prvResetNextTaskUnblockTime.json) | `0x00000c6c` | extracted | — | 0 | — |
| r27 | [prvSearchForNameWithinSingleList](prvSearchForNameWithinSingleList.json) | `0x000005d0` | extracted | — | 0 | — |
| r28 | [vTaskSwitchContext](vTaskSwitchContext.json) | `0x00000654` | extracted | — | 1 | fixture_assert_fail |
| r29 | [xQueueGenericSend](xQueueGenericSend.json) | `0x0000287c` | extracted | — | 22 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r30 | [xQueueReceive](xQueueReceive.json) | `0x00002410` | extracted | — | 21 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r31 | [xQueueGenericSendFromISR](xQueueGenericSendFromISR.json) | `0x0000214c` | extracted | — | 9 | fixture_assert_fail, ulSetInterruptMask, vClearInterruptMask |
| r32 | [xQueueReceiveFromISR](xQueueReceiveFromISR.json) | `0x00002250` | extracted | — | 7 | fixture_assert_fail, ulSetInterruptMask, vClearInterruptMask |
| r33 | [vTaskDelay](vTaskDelay.json) | `0x00001ac8` | extracted | — | 11 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r34 | [xTaskIncrementTick](xTaskIncrementTick.json) | `0x00000e30` | extracted | — | 2 | fixture_assert_fail |
| r35 | [xTaskCreateStatic](xTaskCreateStatic.json) | `0x00000aec` | extracted | — | 12 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r36 | [xEventGroupSetBits](xEventGroupSetBits.json) | `0x00002b48` | extracted | — | 9 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r37 | [xEventGroupClearBits](xEventGroupClearBits.json) | `0x00002af4` | extracted | — | 3 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical |
| r38 | [xStreamBufferSend](xStreamBufferSend.json) | `0x000031ec` | extracted | — | 24 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r39 | [xStreamBufferReceive](xStreamBufferReceive.json) | `0x0000339c` | extracted | — | 20 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r40 | [xTimerGenericCommandFromTask](xTimerGenericCommandFromTask.json) | `0x00003748` | extracted | — | 23 | fixture_assert_fail, vPortEnterCritical, vPortExitCritical, vPortYield |
| r41 | [xTimerGenericCommandFromISR](xTimerGenericCommandFromISR.json) | `0x000037ac` | extracted | — | 10 | fixture_assert_fail, ulSetInterruptMask, vClearInterruptMask |

## Strictly rejected reachable helpers

Each helper was separately submitted to the unchanged e03 frontend; all exited 1 with empty stdout.

| Helper | All missing instruction semantics (absolute address, halfword opcode, assembly) |
|---|---|
| fixture_assert_fail | `0x0000419c: b672` cpsid	i; `0x000041a6: bf30` wfi |
| ulSetInterruptMask | `0x00004090: f3ef 8010` mrs	r0, PRIMASK; `0x00004094: b672` cpsid	i |
| vClearInterruptMask | `0x00004098: f380 8810` msr	PRIMASK, r0 |
| vPortEnterCritical | `0x00003e68: b672` cpsid	i; `0x00003e72: f3bf 8f4f` dsb	sy; `0x00003e76: f3bf 8f6f` isb	sy |
| vPortExitCritical | `0x00003e98: b662` cpsie	i |
| vPortYield | `0x00003e58: f3bf 8f4f` dsb	sy; `0x00003e5c: f3bf 8f6f` isb	sy |

SysTick/PendSV/SVC and first-task boundaries are inventoried separately in
[asynchronous-boundaries.json](asynchronous-boundaries.json); ordinary BL edges do not close NVIC-triggered execution.
