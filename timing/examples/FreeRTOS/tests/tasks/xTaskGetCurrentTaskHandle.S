    .section .text
    .globl xTaskGetCurrentTaskHandle
    .type xTaskGetCurrentTaskHandle, @function

xTaskGetCurrentTaskHandle:
	lw a0, -1896(gp)
	ret

	.size xTaskGetCurrentTaskHandle, .-xTaskGetCurrentTaskHandle

