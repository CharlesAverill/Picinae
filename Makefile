.PHONY: arch strlen tests all clean

all: arch tests strlen
	coqc xform_proofs.v

arch:
	coqc Picinae_core.v
	coqc Picinae_theory.v
	coqc Picinae_statics.v
	coqc Picinae_i386.v
	coqc Picinae_amd64.v
	coqc Picinae_armv7.v
	
strlen:
	coqc strlen_i386.v
	coqc strlen_proofs.v

tests:
	$(MAKE) -C tests all
	
clean:
	rm -rf *.vo *.glob .*.aux
	$(MAKE) -C tests clean