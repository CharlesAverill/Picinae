RISCV_PREFIX=riscv32-unknown-elf-
GCC=$(RISCV_PREFIX)gcc
FLAGS=  -O3 \
  -fno-builtin \
  -fno-tree-vectorize \
  -fno-unroll-loops \
  -nostdlib \
  -ffreestanding \
  -march=rv32imd \
  -S

default: br_ccopy.S

br_ccopy.S:
	$(GCC) $(FLAGS) br_ccopy.c -o br_ccopy.S

br_ccopy_ft.o: br_ccopy_ft.S
	$(GCC) br_ccopy_ft.S -c -o br_ccopy_ft.o

br_ccopy_ft.v: br_ccopy_ft.o
	OBJDUMP=$(RISCV_PREFIX)objdump ../../riscv_lifter.sh br_ccopy_ft.o br_ccopy_ft > br_ccopy_ft.v
	@coq_makefile -f _CoqProject -o Makefile.coq > /dev/null 2>&1
	make -f Makefile.coq

clean:
	rm br_ccopy.S *.o br_ccopy_ft.v
