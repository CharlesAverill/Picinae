RISCV_PREFIX=riscv32-unknown-elf-
GCC=$(RISCV_PREFIX)gcc
FLAGS=  -O1 \
  -fno-builtin \
  -fno-tree-vectorize \
  -fno-unroll-loops \
  -nostdlib \
  -ffreestanding \
  -march=rv32imd \
  -S

default: tmr.S

tmr.S:
	$(GCC) $(FLAGS) tmr.c -o tmr.S

tmr_ft.o: tmr_ft.S
	$(GCC) tmr_ft.S -c -o tmr_ft.o

tmr_ft.v: tmr_ft.o
	OBJDUMP=$(RISCV_PREFIX)objdump ../../riscv_lifter.sh tmr_ft.o tmr_ft > tmr_ft.v
	@coq_makefile -f _CoqProject -o Makefile.coq > /dev/null 2>&1
	make -f Makefile.coq

clean:
	rm tmr.S *.o tmr_ft.v
