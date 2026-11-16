# Build the lifted musl x86_64 programs, the shared library and the proofs.
# Requires Picinae (../../..) to be built first.
VFILES := $(sort $(wildcard programs/*.v)) lib/x64_common.v lib/x64_memcpy_sets.v lib/x64_fill_sets.v \
          $(filter-out lib/x64_common.v lib/x64_memcpy_sets.v lib/x64_fill_sets.v,$(sort $(wildcard lib/*.v))) \
          $(sort $(wildcard proofs/*.v))

all: Makefile.coq
	ulimit -s unlimited; ulimit -v 12000000; $(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject Makefile $(VFILES)
	rocq makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
