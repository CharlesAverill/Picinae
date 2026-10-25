# Build the lifted programs and proofs in this directory.
# Requires Picinae (../..) to be built first.
VFILES := amd64_common.v amd64_cstring.v amd64_ieee.v amd64_termios.v amd64_memcpy_sets.v amd64_memcpy_lemmas.v $(sort $(wildcard *_amd64.v)) $(sort $(wildcard amd64_*_proof.v))

all: Makefile.coq
	ulimit -s unlimited; $(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject Makefile $(VFILES)
	rocq makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean:
	if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean
