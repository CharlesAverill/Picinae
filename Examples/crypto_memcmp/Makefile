.PHONY: memcmp_ft.vc

RISCV_PREFIX=riscv32-unknown-elf-
GCC=$(RISCV_PREFIX)gcc
FLAGS=  -O1 \
  -fno-inline \
  -fno-builtin \
  -fno-tree-vectorize \
  -fno-unroll-loops \
  -nostdlib \
  -ffreestanding \
  -march=rv32imd \
  -S

default: memcmp.S

memcmp.S:
	$(GCC) $(FLAGS) memcmp.c -o memcmp.S

memcmp_ft.o: memcmp_ft.S
	$(GCC) memcmp_ft.S -c -o memcmp_ft.o

memcmp_ft.v: memcmp_ft.o
	OBJDUMP=$(RISCV_PREFIX)objdump ../../riscv_lifter.sh memcmp_ft.o memcmp_ft > memcmp_ft.v
	@coq_makefile -f _CoqProject -o Makefile.coq > /dev/null 2>&1
	make -f Makefile.coq

clean:
	rm memcmp.S *.o memcmp_ft.v
