.syntax unified
.cpu cortex-m0
.thumb
.text
.global mask_fixture
.type mask_fixture, %function
.thumb_func
mask_fixture:
    mrs r0, primask
    cpsid i
    msr primask, r0
    cpsie i
    mrs lr, primask
    msr primask, lr
    bx lr
.size mask_fixture, .-mask_fixture
