RISCV_PREFIX=riscv32-unknown-elf-
GCC=$(RISCV_PREFIX)gcc
LD=$(RISCV_PREFIX)ld
FLAGS=  -O1 \
  -march=rv32imd \
  -mabi=ilp32d \
  -S

default: tmr.S

tmr.S:
	$(GCC) $(FLAGS) tmr.c -o tmr.S

tmr_ft: tmr_ft.S
	$(GCC) tmr_ft.S -o tmr_ft

tmr_ft.v: tmr_ft
	OBJDUMP=$(RISCV_PREFIX)objdump ../../riscv_lifter.sh tmr_ft tmr_ft > tmr_ft.v
	@coq_makefile -f _CoqProject -o Makefile.coq > /dev/null 2>&1
	make -f Makefile.coq

clean:
	rm tmr.S *.o tmr_ft.v *.vo* tmr_ft *.glob .*.aux .lia.cache .Makefile.coq.d
