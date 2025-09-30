#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>

int while_true_break(int n) {
    while (true) {
        if (n + n >= n * n)
            break;

        n--;
    }

    return n;
}

int main(int argc, char* argv[]) {
    for (int i = 0; i < 1000; i++) {
    	while_true_break(i);
    }
}
