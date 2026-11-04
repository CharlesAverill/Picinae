ldr q0, [x0, #0]
ldr q0, [x0, #16]
ldr q0, [x0, #65520]
ldr q0, [x0, #-256]!
ldr q0, [x0], #-256
ldr q0, [x0, #0]!
ldr q0, [x0], #0
ldr q0, [x0, #255]!
ldr q0, [x0], #255
ldr q0, [x30, #0]
ldr q0, [x30, #16]
ldr q0, [x30, #65520]
ldr q0, [x30, #-256]!
ldr q0, [x30], #-256
ldr q0, [x30, #0]!
ldr q0, [x30], #0
ldr q0, [x30, #255]!
ldr q0, [x30], #255
ldr q0, [sp, #0]
ldr q0, [sp, #16]
ldr q0, [sp, #65520]
ldr q0, [sp, #-256]!
ldr q0, [sp], #-256
ldr q0, [sp, #0]!
ldr q0, [sp], #0
ldr q0, [sp, #255]!
ldr q0, [sp], #255
ldr q31, [x0, #0]
ldr q31, [x0, #16]
ldr q31, [x0, #65520]
ldr q31, [x0, #-256]!
ldr q31, [x0], #-256
ldr q31, [x0, #0]!
ldr q31, [x0], #0
ldr q31, [x0, #255]!
ldr q31, [x0], #255
ldr q31, [x30, #0]
ldr q31, [x30, #16]
ldr q31, [x30, #65520]
ldr q31, [x30, #-256]!
ldr q31, [x30], #-256
ldr q31, [x30, #0]!
ldr q31, [x30], #0
ldr q31, [x30, #255]!
ldr q31, [x30], #255
ldr q31, [sp, #0]
ldr q31, [sp, #16]
ldr q31, [sp, #65520]
ldr q31, [sp, #-256]!
ldr q31, [sp], #-256
ldr q31, [sp, #0]!
ldr q31, [sp], #0
ldr q31, [sp, #255]!
ldr q31, [sp], #255
ldr q31, [x0, x0, lsl #0]
ldr q31, [x0, x0, lsl #4]
ldr q31, [x0, x30, lsl #0]
ldr q31, [x0, x30, lsl #4]
ldr q0, [x0, w30, uxtw #0]
ldr q0, [x0, w30, uxtw #4]
ldr q0, [x0, w30, sxtw #0]
ldr q0, [x0, w30, sxtw #4]
ldr q0, [x0, x30, sxtx #0]
ldr q0, [x0, x30, sxtx #4]
ldp q0, q31, [x1, #-1024]
ldp q0, q31, [x1, #-1024]!
ldp q0, q31, [x1], #-1024
ldp q0, q31, [x1, #0]
ldp q0, q31, [x1, #0]!
ldp q0, q31, [x1], #0
ldp q0, q31, [x1, #1008]
ldp q0, q31, [x1, #1008]!
ldp q0, q31, [x1], #1008
ldp q0, q31, [sp, #-1024]
ldp q0, q31, [sp, #-1024]!
ldp q0, q31, [sp], #-1024
ldp q0, q31, [sp, #0]
ldp q0, q31, [sp, #0]!
ldp q0, q31, [sp], #0
ldp q0, q31, [sp, #1008]
ldp q0, q31, [sp, #1008]!
ldp q0, q31, [sp], #1008
ldp q31, q0, [x1, #-1024]
ldp q31, q0, [x1, #-1024]!
ldp q31, q0, [x1], #-1024
ldp q31, q0, [x1, #0]
ldp q31, q0, [x1, #0]!
ldp q31, q0, [x1], #0
ldp q31, q0, [x1, #1008]
ldp q31, q0, [x1, #1008]!
ldp q31, q0, [x1], #1008
ldp q31, q0, [sp, #-1024]
ldp q31, q0, [sp, #-1024]!
ldp q31, q0, [sp], #-1024
ldp q31, q0, [sp, #0]
ldp q31, q0, [sp, #0]!
ldp q31, q0, [sp], #0
ldp q31, q0, [sp, #1008]
ldp q31, q0, [sp, #1008]!
ldp q31, q0, [sp], #1008
ldp q1, q2, [x1, #-1024]
ldp q1, q2, [x1, #-1024]!
ldp q1, q2, [x1], #-1024
ldp q1, q2, [x1, #0]
ldp q1, q2, [x1, #0]!
ldp q1, q2, [x1], #0
ldp q1, q2, [x1, #1008]
ldp q1, q2, [x1, #1008]!
ldp q1, q2, [x1], #1008
ldp q1, q2, [sp, #-1024]
ldp q1, q2, [sp, #-1024]!
ldp q1, q2, [sp], #-1024
ldp q1, q2, [sp, #0]
ldp q1, q2, [sp, #0]!
ldp q1, q2, [sp], #0
ldp q1, q2, [sp, #1008]
ldp q1, q2, [sp, #1008]!
ldp q1, q2, [sp], #1008
ldp q0,q0,[x0]
ldr d0,[x0]
str q0,[x0]
ldur q0,[x0,#-1]
eor v0.16b,v1.16b,v2.16b
ldr q0, label
label: nop
ret
