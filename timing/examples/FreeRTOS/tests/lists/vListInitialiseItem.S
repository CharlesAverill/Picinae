    .section .text
    .globl vListInitialiseItem
    .type vListInitialiseItem, @function

vListInitialiseItem:
	sw zero, 16(a0)
	ret

	.size vListInitialiseItem, .-vListInitialiseItem

