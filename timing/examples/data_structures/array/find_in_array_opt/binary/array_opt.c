#include "array_opt.h"

uint32_t find_in_array(uint32_t* arr, uint32_t key, uint32_t size) {
    uint32_t i = 0;

    for (i = 0; i < size; i++) {
        if (arr[i] == key)
            break;
    }

    return i;
}
