#include <stdio.h>

int main(int argc, char **argv) {
  printf("%s: Hello, World: %d; ARGV at %p\n", argv[0], argc, argv);
  return 0;
}
