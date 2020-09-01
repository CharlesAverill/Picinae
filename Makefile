PICBASE=Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_slogic.vo

.PHONY: all clean arm armcode armproof armpic i386 i386pic i386code i386proof riscv riscvpic riscvcode riscvproof
all: arm i386 riscv

%.vo : %.v
	coqc $< -o $@

Picinae_theory.vo: Picinae_core.vo
Picinae_statics.vo: Picinae_theory.vo
Picinae_finterp.vo: Picinae_statics.vo
Picinae_slogic.vo: Picinae_finterp.vo

# ARM proofs
ARMPIC=$(PICBASE) Picinae_armv7.vo
ARMCODE=strlen_arm.vo memset_arm.vo
ARMPROOF=strlen_arm_proofs.vo memset_arm_proofs.vo
arm: armpic $(ARMCODE) $(ARMPROOF)
armpic: $(ARMPIC)

Picinae_armv7.vo: $(PICBASE)
strlen_arm_proofs.vo: $(ARMPIC) strlen_arm.vo
memset_arm_proofs.vo: $(ARMPIC) memset_arm.vo

# i386 proofs
I386PIC=$(PICBASE) Picinae_i386.vo
I386CODE=strlen_i386.vo strcmp_i386.vo strtok_i386.vo
I386PROOF=strlen_proofs.vo strcmp_proofs.vo strtok_proofs.vo

i386: i386pic $(I386CODE) $(I386PROOF)
i386pic: $(I386PIC)
Picinae_i386.vo: $(PICBASE)
strlen_proofs.vo: $(I386PIC) strlen_i386.vo
strcmp_proofs.vo: $(I386PIC) strcmp_i386.vo
strtok_proofs.vo: $(I386PIC) strtok_i386.vo

# RISC-V proofs
RISCVPIC=$(PICBASE) Picinae_i386.vo
riscv: riscvpic
riscvpic: $(PICBASE) Picinae_riscv.vo

Picinae_riscv.vo: $(PICBASE)

clean:
	rm *.vo *.glob
