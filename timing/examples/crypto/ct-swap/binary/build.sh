mkdir build

riscv-none-elf-gcc -c ~/education/utd/lab/neorv32/sw/common/crt0.S -o ./build/crt0.S.o -march=rv32imd_zicsr_zifencei

make exe RISCV_PREFIX=riscv-none-elf-
