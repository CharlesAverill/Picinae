#include "bubble_sort.h"

inline void swap(uint32_t* x, uint32_t* y) {
    uint32_t temp = *x;
    *x = *y;
    *y = temp;
}

void bubble_sort_theta_n2(uint32_t* arr, uint32_t size) {
    for (uint32_t i = 0; i < size; i++) {
        for (uint32_t j = 0; j < size - 1; j++) {
            if (arr[j] > arr[j + 1]) {
                swap(&arr[j], &arr[j + 1]);
            }
        }
    }
}
