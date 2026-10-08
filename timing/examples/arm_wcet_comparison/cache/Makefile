# Build each <name>.c into <name>.o for the STM32F0DISCOVERY (Cortex-M0)

CC = arm-none-eabi-gcc
CFLAGS = -Wall -O2 -mcpu=cortex-m0 -mthumb
SOURCES = $(wildcard *.c)
OBJECTS = $(SOURCES:.c=.o)

# Default target: build all objects
all: $(OBJECTS)

# Pattern rule: build each object from its .c file
%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Clean up objects
.PHONY: clean
clean:
	rm -f $(OBJECTS)
