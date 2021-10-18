# SOURCES = hello.s hello-var.s hello-main.s hello-invalid.s exit-42.s
# TARGETS = $(patsubst %.s, %, $(SOURCES))
# OBJECTS = $(patsubst %.s, %.o, $(TARGETS))

TARGETS = hello hello-var hello-invalid exit-42 jump hello-libc
PATCHED = $(patsubst %, %.patched, $(TARGETS))

CC=riscv32-unknown-linux-gnu-gcc
AS=riscv32-unknown-linux-gnu-as
LD=riscv32-unknown-linux-gnu-ld
CFLAGS=-static

all: $(PATCHED)

clean:
	rm -f $(TARGETS:%=%.patched)
	rm -f *.o

.PHONY: all clean

hello-libc.orig: hello-libc.c
	riscv32-unknown-linux-gnu-gcc -static -o $@ $<

%.orig: %.o
	$(LD) -o $@ $<

$(PATCHED): %.patched: %.orig
	bap riscv-cfi -v -i $< -o $@ -m $*.map

