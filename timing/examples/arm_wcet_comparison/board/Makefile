# Builds the measurement firmware for the STM32F072B-DISCO.
#
#   make            flash build (code in flash, 0 wait states) -> build/flash/timing.elf
#   make MEM=sram   same, but the functions and harness run from SRAM
#   make flash      build and write it to the board (st-flash)
#   make verify     check the functions are byte-identical to the analyzed ELFs
#
# The functions under test are compiled from ../<dir>/*.c with exactly the
# flags in those directories' Makefiles, and verify.py checks the result.

MEM ?= flash
BUILD = build/$(MEM)

CC      = arm-none-eabi-gcc
OBJCOPY = arm-none-eabi-objcopy
SIZE    = arm-none-eabi-size

# Must match ../*/Makefile
BENCH_CFLAGS = -Wall -O2 -mcpu=cortex-m0 -mthumb
# The driver code is not timed
CFLAGS  = -Wall -Wextra -O2 -g -mcpu=cortex-m0 -mthumb -ffreestanding -ffunction-sections
LDFLAGS = -nostdlib -mcpu=cortex-m0 -mthumb -Wl,-L. -Wl,-T,link_$(MEM).ld -Wl,--gc-sections \
          -Wl,-Map,$(BUILD)/timing.map
LDLIBS  = -lgcc

BENCH_OBJS = $(BUILD)/cache.o $(BUILD)/while_true_break.o $(BUILD)/arraysearch.o \
             $(BUILD)/collatz.o $(BUILD)/linked_list.o
OBJS = $(BUILD)/startup.o $(BUILD)/main.o $(BUILD)/harness.o $(BENCH_OBJS)

all: $(BUILD)/timing.bin

$(BUILD):
	mkdir -p $@

$(BUILD)/cache.o:            ../cache/cache.c                       | $(BUILD)
$(BUILD)/while_true_break.o: ../while_true_break/while_true_break.c | $(BUILD)
$(BUILD)/arraysearch.o:      ../arraysearch/arraysearch.c           | $(BUILD)
$(BUILD)/collatz.o:          ../collatz/collatz.c                   | $(BUILD)
$(BUILD)/linked_list.o:      ../llsearch/linked_list.c              | $(BUILD)
$(BENCH_OBJS):
	$(CC) $(BENCH_CFLAGS) -c -o $@ $<

$(BUILD)/%.o: %.c | $(BUILD)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BUILD)/harness.o: harness.S | $(BUILD)
	$(CC) -mcpu=cortex-m0 -mthumb -c -o $@ $<

$(BUILD)/timing.elf: $(OBJS) link_$(MEM).ld common.ld memory.ld
	$(CC) $(LDFLAGS) -o $@ $(OBJS) $(LDLIBS)
	$(SIZE) $@

$(BUILD)/timing.bin: $(BUILD)/timing.elf
	$(OBJCOPY) -O binary $< $@

verify: $(BUILD)/timing.elf
	python3 -I verify.py $<

flash: $(BUILD)/timing.bin verify
	st-flash --reset write $< 0x08000000

clean:
	rm -rf build

.PHONY: all verify flash clean
