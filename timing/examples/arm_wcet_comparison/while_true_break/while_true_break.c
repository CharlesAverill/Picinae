#include <stdint.h>
#include <stdbool.h>

uint32_t while_true_break(uint32_t n) {
    while (true) {
        if ((uint32_t)n + (uint32_t)n >= (uint32_t)n * (uint32_t)n)
            break;

        n--;
    }

    return n;
}

/*
int main(int argc, char* argv[]) {
    for (int i = 0; i < 1000; i++) {
    	while_true_break(i);
    }
}
*/
