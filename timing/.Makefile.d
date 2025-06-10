riscvTiming.vo riscvTiming.glob riscvTiming.v.beautified riscvTiming.required_vo: riscvTiming.v ../Picinae_core.vo ../Picinae_riscv.vo
riscvTiming.vio: riscvTiming.v ../Picinae_core.vio ../Picinae_riscv.vio
riscvTiming.vos riscvTiming.vok riscvTiming.required_vos: riscvTiming.v ../Picinae_core.vos ../Picinae_riscv.vos
timing_auto.vo timing_auto.glob timing_auto.v.beautified timing_auto.required_vo: timing_auto.v riscvTiming.vo
timing_auto.vio: timing_auto.v riscvTiming.vio
timing_auto.vos timing_auto.vok timing_auto.required_vos: timing_auto.v riscvTiming.vos
memsolve.vo memsolve.glob memsolve.v.beautified memsolve.required_vo: memsolve.v riscvTiming.vo
memsolve.vio: memsolve.v riscvTiming.vio
memsolve.vos memsolve.vok memsolve.required_vos: memsolve.v riscvTiming.vos
examples/RTOSDemo_NoAsserts_Clz.vo examples/RTOSDemo_NoAsserts_Clz.glob examples/RTOSDemo_NoAsserts_Clz.v.beautified examples/RTOSDemo_NoAsserts_Clz.required_vo: examples/RTOSDemo_NoAsserts_Clz.v 
examples/RTOSDemo_NoAsserts_Clz.vio: examples/RTOSDemo_NoAsserts_Clz.v 
examples/RTOSDemo_NoAsserts_Clz.vos examples/RTOSDemo_NoAsserts_Clz.vok examples/RTOSDemo_NoAsserts_Clz.required_vos: examples/RTOSDemo_NoAsserts_Clz.v 
