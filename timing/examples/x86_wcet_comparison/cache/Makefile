# Simple Makefile: build <name>.c into <name> and run with `make run name=<program>`

CC = gcc
CFLAGS = -O2
SOURCES = $(wildcard *.c)
BINARIES = $(SOURCES:.c=)

# Default target: build all programs
all: $(BINARIES)

# Pattern rule: build each program from its .c file
%: %.c
	$(CC) $(CFLAGS) -o $@ $<

# Run target: compile and run in one go
.PHONY: run
run:
	@if [ -z "$(name)" ]; then \
		echo "No name provided. Building and running all programs..."; \
		for bin in $(BINARIES); do \
			$(MAKE) $$bin; \
			echo "$$bin"; \
			./$$bin; \
			echo "RC: $$?"; \
			echo ""; \
		done; \
	else \
		$(MAKE) $(name) && ./$(name); \
		echo "RC: $$?"; \
	fi

# Clean up binaries
.PHONY: clean
clean:
	rm -f $(BINARIES)
