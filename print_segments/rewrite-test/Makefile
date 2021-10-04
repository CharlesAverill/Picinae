# SOURCES = hello.s hello-var.s hello-main.s hello-invalid.s exit-42.s
# TARGETS = $(patsubst %.s, %, $(SOURCES))
# OBJECTS = $(patsubst %.s, %.o, $(TARGETS))

TARGETS = hello hello-var hello-invalid exit-42
OBJECTS = $(patsubst %, %.o, $(TARGETS))
TABLES = $(patsubst %, %.table, $(TARGETS))
TEXTS = $(patsubst %, %.text, $(TARGETS))
PATCHED = $(patsubst %, %.patched, $(TARGETS))

all: $(TARGETS) $(PATCHED) hello-main

clean:
	rm -f $(TARGETS) hello-main
	rm -f *.o

.PHONY: all clean

$(TARGETS): %: %.o
	riscv32-unknown-linux-gnu-ld -o $@ $<

$(OBJECTS): %.o: %.s
	riscv32-unknown-linux-gnu-as -o $@ $<

$(PATCHED): %.patched: % %.table %.text %.entry
	../glue/glue.py $< $<.table $<.text `cat $<.entry`

%.table %.text %.entry: %
	bap segments $< $<.table $<.text > $<.entry

hello-main: hello-main.s
	riscv32-unknown-linux-gnu-gcc -static -o hello-main hello-main.s
