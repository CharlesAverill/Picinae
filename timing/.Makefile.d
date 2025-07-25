TimingAutomation.vo TimingAutomation.glob TimingAutomation.v.beautified TimingAutomation.required_vo: TimingAutomation.v ../Picinae_core.vo ../Picinae_statics.vo ../Picinae_finterp.vo ../Picinae_theory.vo ../Picinae_simplifier_base.vo ../Picinae_simplifier_v1_1.vo
TimingAutomation.vio: TimingAutomation.v ../Picinae_core.vio ../Picinae_statics.vio ../Picinae_finterp.vio ../Picinae_theory.vio ../Picinae_simplifier_base.vio ../Picinae_simplifier_v1_1.vio
TimingAutomation.vos TimingAutomation.vok TimingAutomation.required_vos: TimingAutomation.v ../Picinae_core.vos ../Picinae_statics.vos ../Picinae_finterp.vos ../Picinae_theory.vos ../Picinae_simplifier_base.vos ../Picinae_simplifier_v1_1.vos
riscv/CPUTimingBehavior.vo riscv/CPUTimingBehavior.glob riscv/CPUTimingBehavior.v.beautified riscv/CPUTimingBehavior.required_vo: riscv/CPUTimingBehavior.v 
riscv/CPUTimingBehavior.vio: riscv/CPUTimingBehavior.v 
riscv/CPUTimingBehavior.vos riscv/CPUTimingBehavior.vok riscv/CPUTimingBehavior.required_vos: riscv/CPUTimingBehavior.v 
riscv/RISCVTiming.vo riscv/RISCVTiming.glob riscv/RISCVTiming.v.beautified riscv/RISCVTiming.required_vo: riscv/RISCVTiming.v ../Picinae_riscv.vo riscv/CPUTimingBehavior.vo TimingAutomation.vo
riscv/RISCVTiming.vio: riscv/RISCVTiming.v ../Picinae_riscv.vio riscv/CPUTimingBehavior.vio TimingAutomation.vio
riscv/RISCVTiming.vos riscv/RISCVTiming.vok riscv/RISCVTiming.required_vos: riscv/RISCVTiming.v ../Picinae_riscv.vos riscv/CPUTimingBehavior.vos TimingAutomation.vos
riscv/NEORV32.vo riscv/NEORV32.glob riscv/NEORV32.v.beautified riscv/NEORV32.required_vo: riscv/NEORV32.v riscv/CPUTimingBehavior.vo ../Picinae_core.vo
riscv/NEORV32.vio: riscv/NEORV32.v riscv/CPUTimingBehavior.vio ../Picinae_core.vio
riscv/NEORV32.vos riscv/NEORV32.vok riscv/NEORV32.required_vos: riscv/NEORV32.v riscv/CPUTimingBehavior.vos ../Picinae_core.vos
memsolve.vo memsolve.glob memsolve.v.beautified memsolve.required_vo: memsolve.v riscv/RISCVTiming.vo
memsolve.vio: memsolve.v riscv/RISCVTiming.vio
memsolve.vos memsolve.vok memsolve.required_vos: memsolve.v riscv/RISCVTiming.vos
examples/FreeRTOS/RTOSDemo.vo examples/FreeRTOS/RTOSDemo.glob examples/FreeRTOS/RTOSDemo.v.beautified examples/FreeRTOS/RTOSDemo.required_vo: examples/FreeRTOS/RTOSDemo.v ../Picinae_riscv.vo
examples/FreeRTOS/RTOSDemo.vio: examples/FreeRTOS/RTOSDemo.v ../Picinae_riscv.vio
examples/FreeRTOS/RTOSDemo.vos examples/FreeRTOS/RTOSDemo.vok examples/FreeRTOS/RTOSDemo.required_vos: examples/FreeRTOS/RTOSDemo.v ../Picinae_riscv.vos
examples/data_structures/array/find_in_array/array.vo examples/data_structures/array/find_in_array/array.glob examples/data_structures/array/find_in_array/array.v.beautified examples/data_structures/array/find_in_array/array.required_vo: examples/data_structures/array/find_in_array/array.v ../Picinae_riscv.vo
examples/data_structures/array/find_in_array/array.vio: examples/data_structures/array/find_in_array/array.v ../Picinae_riscv.vio
examples/data_structures/array/find_in_array/array.vos examples/data_structures/array/find_in_array/array.vok examples/data_structures/array/find_in_array/array.required_vos: examples/data_structures/array/find_in_array/array.v ../Picinae_riscv.vos
examples/data_structures/array/find_in_array_opt/array_opt.vo examples/data_structures/array/find_in_array_opt/array_opt.glob examples/data_structures/array/find_in_array_opt/array_opt.v.beautified examples/data_structures/array/find_in_array_opt/array_opt.required_vo: examples/data_structures/array/find_in_array_opt/array_opt.v ../Picinae_riscv.vo
examples/data_structures/array/find_in_array_opt/array_opt.vio: examples/data_structures/array/find_in_array_opt/array_opt.v ../Picinae_riscv.vio
examples/data_structures/array/find_in_array_opt/array_opt.vos examples/data_structures/array/find_in_array_opt/array_opt.vok examples/data_structures/array/find_in_array_opt/array_opt.required_vos: examples/data_structures/array/find_in_array_opt/array_opt.v ../Picinae_riscv.vos
examples/data_structures/array/bubble_sort/bubble_sort.vo examples/data_structures/array/bubble_sort/bubble_sort.glob examples/data_structures/array/bubble_sort/bubble_sort.v.beautified examples/data_structures/array/bubble_sort/bubble_sort.required_vo: examples/data_structures/array/bubble_sort/bubble_sort.v ../Picinae_riscv.vo
examples/data_structures/array/bubble_sort/bubble_sort.vio: examples/data_structures/array/bubble_sort/bubble_sort.v ../Picinae_riscv.vio
examples/data_structures/array/bubble_sort/bubble_sort.vos examples/data_structures/array/bubble_sort/bubble_sort.vok examples/data_structures/array/bubble_sort/bubble_sort.required_vos: examples/data_structures/array/bubble_sort/bubble_sort.v ../Picinae_riscv.vos
examples/data_structures/linked_list/linked_list.vo examples/data_structures/linked_list/linked_list.glob examples/data_structures/linked_list/linked_list.v.beautified examples/data_structures/linked_list/linked_list.required_vo: examples/data_structures/linked_list/linked_list.v ../Picinae_riscv.vo
examples/data_structures/linked_list/linked_list.vio: examples/data_structures/linked_list/linked_list.v ../Picinae_riscv.vio
examples/data_structures/linked_list/linked_list.vos examples/data_structures/linked_list/linked_list.vok examples/data_structures/linked_list/linked_list.required_vos: examples/data_structures/linked_list/linked_list.v ../Picinae_riscv.vos
examples/data_structures/union_find/union_find.vo examples/data_structures/union_find/union_find.glob examples/data_structures/union_find/union_find.v.beautified examples/data_structures/union_find/union_find.required_vo: examples/data_structures/union_find/union_find.v ../Picinae_riscv.vo
examples/data_structures/union_find/union_find.vio: examples/data_structures/union_find/union_find.v ../Picinae_riscv.vio
examples/data_structures/union_find/union_find.vos examples/data_structures/union_find/union_find.vok examples/data_structures/union_find/union_find.required_vos: examples/data_structures/union_find/union_find.v ../Picinae_riscv.vos
