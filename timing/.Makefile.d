TimingAutomation.vo TimingAutomation.glob TimingAutomation.v.beautified TimingAutomation.required_vo: TimingAutomation.v ../Picinae_core.vo ../Picinae_statics.vo ../Picinae_finterp.vo ../Picinae_theory.vo ../Picinae_simplifier_base.vo ../Picinae_simplifier_v1_1.vo ../Picinae_ISA.vo
TimingAutomation.vos TimingAutomation.vok TimingAutomation.required_vos: TimingAutomation.v ../Picinae_core.vos ../Picinae_statics.vos ../Picinae_finterp.vos ../Picinae_theory.vos ../Picinae_simplifier_base.vos ../Picinae_simplifier_v1_1.vos ../Picinae_ISA.vos
riscv/CPUTimingBehavior.vo riscv/CPUTimingBehavior.glob riscv/CPUTimingBehavior.v.beautified riscv/CPUTimingBehavior.required_vo: riscv/CPUTimingBehavior.v 
riscv/CPUTimingBehavior.vos riscv/CPUTimingBehavior.vok riscv/CPUTimingBehavior.required_vos: riscv/CPUTimingBehavior.v 
riscv/RISCVTiming.vo riscv/RISCVTiming.glob riscv/RISCVTiming.v.beautified riscv/RISCVTiming.required_vo: riscv/RISCVTiming.v ../Picinae_riscv.vo riscv/CPUTimingBehavior.vo TimingAutomation.vo
riscv/RISCVTiming.vos riscv/RISCVTiming.vok riscv/RISCVTiming.required_vos: riscv/RISCVTiming.v ../Picinae_riscv.vos riscv/CPUTimingBehavior.vos TimingAutomation.vos
riscv/NEORV32.vo riscv/NEORV32.glob riscv/NEORV32.v.beautified riscv/NEORV32.required_vo: riscv/NEORV32.v riscv/CPUTimingBehavior.vo ../Picinae_core.vo
riscv/NEORV32.vos riscv/NEORV32.vok riscv/NEORV32.required_vos: riscv/NEORV32.v riscv/CPUTimingBehavior.vos ../Picinae_core.vos
memsolve.vo memsolve.glob memsolve.v.beautified memsolve.required_vo: memsolve.v riscv/RISCVTiming.vo
memsolve.vos memsolve.vok memsolve.required_vos: memsolve.v riscv/RISCVTiming.vos
