# Makefile originally taken from coq-club

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf *.html
	

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o $@
	#rocq makefile -f _CoqProject -o $@

docs: all
	@VFILES=$$(grep '^.*\.v$$' _CoqProject); \
	if [ -n "$$VFILES" ]; then \
	    coqdoc --html $$VFILES; \
	else \
	    echo "No Coq files found in _CoqProject"; \
	fi

_CoqProject: ;

Makefile: ;

phony: ;

cfi_riscv_extraction.v: ;

include Makefile.coq.conf
print_segments/extraction.ml: cfi_riscv_extraction.v $(COQMF_VFILES:%.v=%.vo)
	coqc -R . Picinae $< > $@

.PHONY: all clean phony

