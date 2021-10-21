#include <stdio.h>

extern void *mmap (void *__addr, size_t __len, int __prot,
		   int __flags, int __fd, __off_t __offset);

int main() {
  puts("Allocating some memory");
  int *mem = mmap(0, 0x1000, 7, 0x22, -1, 0);
  if (!mem) {
    puts("mmap failed!");
    return -1;
  }
  *mem = 0x8067; // jr ra

  puts("Attempting to jump to somewhere unsafe!");
  ((void(*)())(void*)mem)();

  puts("Uh oh... we did not catch unsafe call!");
}
