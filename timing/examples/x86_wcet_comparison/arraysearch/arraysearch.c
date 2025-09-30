#include <stdint.h>
#include <stdlib.h>

int find(uint32_t *arr, uint16_t size, uint32_t key) {
    int i;
    for (i = 0; i < size; i++) {
        if (arr[i] == key)
            return i;
    }

    return -1;
}

int main(int argc, char *argv[]) {
    uint32_t arr[1000];
    
    for (int i = 0 ; i < 1000; i++) {
    	arr[i] = i * 3 + 57 * i;
    }
    
    for (int i = 10; i < 1000; i++) {
    	find(arr, i, arr[(i + 99 + i * 100) % 1000]);
    }
}
