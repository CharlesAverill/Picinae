riscvTiming.vo riscvTiming.glob riscvTiming.v.beautified riscvTiming.required_vo: riscvTiming.v ../Picinae_core.vo ../Picinae_riscv.vo
riscvTiming.vio: riscvTiming.v ../Picinae_core.vio ../Picinae_riscv.vio
riscvTiming.vos riscvTiming.vok riscvTiming.required_vos: riscvTiming.v ../Picinae_core.vos ../Picinae_riscv.vos
timing_auto.vo timing_auto.glob timing_auto.v.beautified timing_auto.required_vo: timing_auto.v riscvTiming.vo
timing_auto.vio: timing_auto.v riscvTiming.vio
timing_auto.vos timing_auto.vok timing_auto.required_vos: timing_auto.v riscvTiming.vos
memsolve.vo memsolve.glob memsolve.v.beautified memsolve.required_vo: memsolve.v riscvTiming.vo
memsolve.vio: memsolve.v riscvTiming.vio
memsolve.vos memsolve.vok memsolve.required_vos: memsolve.v riscvTiming.vos
examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.vo examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.glob examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.v.beautified examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.required_vo: examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.v 
examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.vio: examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.v 
examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.vos examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.vok examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.required_vos: examples/FreeRTOS/RTOSDemo_NoAsserts_Clz.v 
examples/data_structures/array/find_in_array/array.vo examples/data_structures/array/find_in_array/array.glob examples/data_structures/array/find_in_array/array.v.beautified examples/data_structures/array/find_in_array/array.required_vo: examples/data_structures/array/find_in_array/array.v ../Picinae_riscv.vo
examples/data_structures/array/find_in_array/array.vio: examples/data_structures/array/find_in_array/array.v ../Picinae_riscv.vio
examples/data_structures/array/find_in_array/array.vos examples/data_structures/array/find_in_array/array.vok examples/data_structures/array/find_in_array/array.required_vos: examples/data_structures/array/find_in_array/array.v ../Picinae_riscv.vos
examples/data_structures/linked_list/linked_list.vo examples/data_structures/linked_list/linked_list.glob examples/data_structures/linked_list/linked_list.v.beautified examples/data_structures/linked_list/linked_list.required_vo: examples/data_structures/linked_list/linked_list.v ../Picinae_riscv.vo
examples/data_structures/linked_list/linked_list.vio: examples/data_structures/linked_list/linked_list.v ../Picinae_riscv.vio
examples/data_structures/linked_list/linked_list.vos examples/data_structures/linked_list/linked_list.vok examples/data_structures/linked_list/linked_list.required_vos: examples/data_structures/linked_list/linked_list.v ../Picinae_riscv.vos
