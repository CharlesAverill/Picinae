.PHONY: arch strlen all clean

all: arch strlen
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

clean:
	rm -rf *.vo *.glob .*.aux