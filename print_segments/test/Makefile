# SOURCES = hello.s hello-var.s hello-main.s hello-invalid.s exit-42.s
# TARGETS = $(patsubst %.s, %, $(SOURCES))
# OBJECTS = $(patsubst %.s, %.o, $(TARGETS))

LIBC_TARGETS = hello-libc test-cfi
ASM_TARGETS = hello hello-var hello-invalid exit-42 jump jal jal_min
TARGETS = $(ASM_TARGETS) $(LIBC_TARGETS)
PATCHED = $(patsubst %, %.patched, $(TARGETS))

CC=riscv32-unknown-linux-gnu-gcc
AS=riscv32-unknown-linux-gnu-as
LD=riscv32-unknown-linux-gnu-ld
CFLAGS=-static

all: $(PATCHED)

clean:
	rm -f $(TARGETS:%=%.map) $(TARGETS:%=%.orig) $(TARGETS:%=%.patched)
	rm -f *.o

.PHONY: all clean

$(LIBC_TARGETS:%=%.orig): %.orig: %.c
	$(CC) -static -o $@ $<

$(ASM_TARGETS:%=%.orig): %.orig: %.o
	$(LD) -o $@ $<

$(PATCHED): %.patched: %.orig
	bap riscv-cfi --handler-linux-abort -v -i $< -o $@ -m $*.map

