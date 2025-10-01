#include <stdlib.h>
#include <stdio.h>

int sum(int* arr, int size) {
    int x = 0;
    for (int i = 0; i < size; i++) {
        x += arr[i];
    }
    return x;
}

int main(int argc, char* argv[]) {
    int arr[1000];
    
    for (int j = 0; j < 100; j++) {
    	for(int i = 0; i < 1000; i++) {
	        arr[i] = rand();
	    }
	
	    printf("%d\n", sum(arr, 1000));
	    printf("%d\n", sum(arr, 1000));	
    }
}
