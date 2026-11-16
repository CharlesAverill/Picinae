SHELL := /bin/bash
ROCQ ?= rocq
ROOT := ../..
FLAGS := -q -R $(ROOT) Picinae
SOURCES := $(wildcard x86/*.v)
PROOFS := $(wildcard x86/*_proof.v)
OBJECTS := $(SOURCES:.v=.vo)
MODULES := $(patsubst x86/%.v,Picinae.coqettu.codex.x86.%,$(SOURCES))
MUSL_LIB := $(abspath ../alpine_musl/x86/lib)

.PHONY: all check core provenance smoke adapter-check
all: $(OBJECTS)

# Build the shared Picinae prerequisites using the repository's configuration.
core:
	ulimit -v 8000000; $(MAKE) -C $(ROOT) Picinae_i386.vo Picinae_numbers.vo

x86/%.vo: x86/%.v
	ulimit -v 8000000; $(ROCQ) c $(FLAGS) $<

$(PROOFS:.v=.vo): x86/%_proof.vo: x86/%_proof.v x86/%_i386.vo x86/i386_common.vo x86/i386_bits.vo
	ulimit -v 8000000; $(ROCQ) c $(FLAGS) $<

x86/i386_ascii.vo: x86/i386_bits.vo
x86/isalpha_proof.vo x86/isalnum_proof.vo x86/isblank_proof.vo x86/iscntrl_proof.vo x86/isspace_proof.vo x86/tolower_proof.vo x86/toupper_proof.vo: x86/i386_ascii.vo
x86/wmemset_proof.vo: x86/i386_memory.vo x86/i386_strings.vo
x86/strlen_proof.vo: x86/i386_strings.vo
x86/wmemchr_proof.vo: x86/i386_strings.vo
x86/memcmp_proof.vo: x86/i386_strings.vo x86/i386_stack.vo x86/i386_compare.vo
x86/wmemcmp_proof.vo: x86/i386_strings.vo x86/i386_stack.vo x86/i386_compare.vo
x86/wmemcmp_proof.vo: x86/i386_signed.vo
x86/i386_signed.vo: x86/i386_bits.vo
x86/i386_compare.vo: x86/i386_bits.vo
x86/i386_reverse.vo: x86/i386_stack2.vo
x86/i386_stack2.vo: x86/i386_stack.vo
x86/i386_stringcmp.vo: x86/i386_strings.vo x86/i386_compare.vo x86/i386_stack2.vo
x86/strcmp_proof.vo: x86/i386_stringcmp.vo x86/i386_stack2.vo
x86/memrchr_proof.vo: x86/i386_reverse.vo x86/i386_stack2.vo x86/i386_strings.vo
x86/i386_bsf.vo: x86/i386_rep.vo
x86/ffs_proof.vo: x86/i386_bsf.vo
x86/ffsl_proof.vo: x86/i386_bsf.vo
x86/ffsll_proof.vo: x86/i386_bsf.vo x86/i386_stack.vo

x86/audit.vo: x86/audit.v $(patsubst %.v,%.vo,$(wildcard x86/*_proof.v))
	ulimit -v 8000000; $(ROCQ) c $(FLAGS) x86/audit.v

provenance:
	python3 verify_provenance.py --manifest .build/lift_manifest.json

.build/native_smoke: x86/native_smoke.c $(MUSL_LIB)/libc.musl-x86.so.1
	mkdir -p .build
	$(CC) -m32 -O2 -Wall -Wextra -Werror -fno-builtin -fno-stack-protector -fno-pie -no-pie -nostdlib \
	  -mno-sse -mno-mmx -Wl,-e,_start -Wl,-z,noexecstack \
	  -Wl,--dynamic-linker=$(MUSL_LIB)/libc.musl-x86.so.1 -Wl,-rpath,$(MUSL_LIB) \
	  x86/native_smoke.c $(MUSL_LIB)/libc.musl-x86.so.1 -o $@

smoke: provenance .build/native_smoke
	./.build/native_smoke

adapter-check:
	python3 -m unittest discover -s tests -p 'test_*.py'

check: all provenance adapter-check
	ulimit -v 8000000; python3 check_assumptions.py
	ulimit -v 8000000; $(ROCQ) check -silent -R $(ROOT) Picinae $(MODULES)
