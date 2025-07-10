#include "find_in_array.h"

uint32_t find_in_array(uint32_t* arr, uint32_t key, uint32_t size) {
    uint32_t i = 0;

    /*
    GCC really liked turning this into a do-while loop, 
    which makes the iterator harder to reason about
    
    for (int i = 0; i < size; i++)
        if (arr[i] == key)
            break;
    */
    __asm__ volatile (
        "1:\n"
        "bgeu   %[i], %[size], 2f\n"         // if (i >= size) goto end
        "slli   t0, %[i], 2\n"               // t0 = i * 4
        "add    t1, %[arr], t0\n"            // t1 = arr + i * 4
        "lw     t2, 0(t1)\n"                 // t2 = arr[i]
        "beq    t2, %[key], 2f\n"            // if (arr[i] == key) break
        "addi   %[i], %[i], 1\n"             // i++
        "j      1b\n"                        // jump back to loop start
        "2:\n"
        : [i] "+r" (i)                         // output: i is updated
        : [arr] "r" (arr), [key] "r" (key), [size] "r" (size)  // inputs
        : "t0", "t1", "t2", "memory", "cc"    // clobbered
    );

    return i;
}
