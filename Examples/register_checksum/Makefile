RISCV_PREFIX=riscv32-unknown-elf-
GCC=$(RISCV_PREFIX)gcc

register_checksum.o: register_checksum.S
	$(GCC) register_checksum.S -c -march=rv32imd -o register_checksum.o

register_checksum.v: register_checksum.o
	OBJDUMP=$(RISCV_PREFIX)objdump ../../riscv_lifter.sh register_checksum.o register_checksum > register_checksum.v
	@coq_makefile -f _CoqProject -o Makefile.coq > /dev/null 2>&1
	make -f Makefile.coq

clean:
	rm *.o register_checksum.v *.vo*
