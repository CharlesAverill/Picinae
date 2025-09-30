# Application makefile.
# Use this makefile to configure all relevant CPU / compiler options.

# Override the default CPU ISA
MARCH = rv32i_zicsr_zifencei_zicntr

# Override the default RISC-V GCC prefix
RISCV_PREFIX ?= /home/charles/Desktop/riscv-none-elf/bin/riscv-none-elf-

# Override default optimization goal
EFFORT = -O3

# Add extended debug symbols
USER_FLAGS += -ggdb -gdwarf-3

# Adjust processor IMEM size
USER_FLAGS += -Wl,--defsym,__neorv32_rom_size=16k

# Adjust processor DMEM size
USER_FLAGS += -Wl,--defsym,__neorv32_ram_size=8k

# Linker flags
USER_FLAGS += -ffunction-sections
USER_FLAGS += -Wl,--gc-sections

# Adjust maximum heap size
#USER_FLAGS += -Wl,--defsym,__neorv32_heap_size=1k

# Additional sources
#APP_SRC += $(wildcard ./*.c)
#APP_INC += -I .

# Set path to NEORV32 root directory
NEORV32_HOME ?= /home/charles/Desktop/projects/rocq/neorv32

# Include the main NEORV32 makefile
include $(NEORV32_HOME)/sw/common/common.mk

