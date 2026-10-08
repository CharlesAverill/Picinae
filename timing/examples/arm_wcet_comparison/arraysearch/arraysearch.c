#include <stdint.h>

uint16_t find(uint64_t *arr, uint16_t size, uint64_t key) {
    uint32_t i;
    for (i = 0; i < size; i++) {
        if (arr[i] == key)
            return i;
    }
    return -1;
}
/*
int main(int argc, char *argv[]) {
    uint64_t arr[1000];
    
    for (int i = 0 ; i < 1000; i++) {
    	arr[i] = i * 3 + 57 * i;
    }
    
    for (int i = 10; i < 1000; i++) {
    	find(arr, i, arr[(i + 99 + i * 100) % 1000]);
    }
}
*/
