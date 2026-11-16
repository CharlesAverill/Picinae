# Build all Grok Bot (agent coqettu) aarch64 musl proofs.
# Picinae itself is used pre-built through the symlinks in picinae/.
# Every rocq/coqc process is memory-capped (8 GB) so a runaway tactic
# fails instead of swapping.
all: Makefile.coq
	bash -c 'ulimit -v 8000000; $(MAKE) -f Makefile.coq'

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# Print the axioms every main theorem depends on (must be none beyond
# Picinae's own).
assumptions: Makefile.coq
	touch proofs/Assumptions.v
	bash -c 'ulimit -v 8000000; $(MAKE) -f Makefile.coq'

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

.PHONY: all clean assumptions
