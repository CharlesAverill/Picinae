# Build each <name>.c into a linked <name>.elf for the STM32F0DISCOVERY
# (Cortex-M0)

CC = arm-none-eabi-gcc
CFLAGS = -Wall -O2 -mcpu=cortex-m0 -mthumb
# Place code at the start of the STM32F0's flash and keep only what is used
LDFLAGS = -nostdlib -Wl,--entry=insert_after_pos_in_list -Wl,-Ttext=0x08000000 -Wl,--gc-sections
LDLIBS = -lgcc
SOURCES = $(wildcard *.c)
OBJECTS = $(SOURCES:.c=.o)
BINARIES = $(SOURCES:.c=.elf)

# Default target: build all linked binaries
all: $(BINARIES)

# Pattern rule: build each object from its .c file
%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Pattern rule: link each object into an ELF
%.elf: %.o
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

# Clean up objects and binaries
.PHONY: clean
clean:
	rm -f $(OBJECTS) $(BINARIES)
