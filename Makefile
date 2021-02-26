PICBASE=Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_slogic.vo

.PHONY: all clean picbase arm armcode armproof armpic i386 i386pic i386code i386proof riscv riscvpic riscvcode riscvproof
all: arm i386 riscv

%.vo : %.v
	coqc $< -o $@

picbase: Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier.vo Picinae_slogic.vo
Picinae_theory.vo: Picinae_core.vo
Picinae_statics.vo: Picinae_theory.vo
Picinae_finterp.vo: Picinae_statics.vo
Picinae_simplifier.vo: Picinae_finterp.vo
Picinae_slogic.vo: Picinae_theory.vo

# ARM proofs
arm: armpic armcode armproof
armpic: picbase Picinae_armv7.vo
armcode: strlen_arm.vo memset_arm.vo
armproof: strlen_arm_proofs.vo memset_arm_proofs.vo

Picinae_armv7.vo: picbase
strlen_arm_proofs.vo: armpic strlen_arm.vo
memset_arm_proofs.vo: armpic memset_arm.vo

# i386 proofs
i386: i386pic i386code i386proof
i386pic: picbase Picinae_i386.vo
i386code: strlen_i386.vo strcmp_i386.vo strtok_i386.vo
i386proof: strlen_proofs.vo strcmp_proofs.vo strtok_proofs.vo

Picinae_i386.vo: picbase
strlen_proofs.vo: i386pic strlen_i386.vo
strcmp_proofs.vo: i386pic strcmp_i386.vo
strtok_proofs.vo: i386pic strtok_i386.vo

# RISC-V proofs
riscv: riscvpic
riscvpic: picbase Picinae_riscv.vo

Picinae_riscv.vo: picbase

clean:
	rm *.vo *.glob
