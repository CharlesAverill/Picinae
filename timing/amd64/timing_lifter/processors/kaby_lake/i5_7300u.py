# https://uops.info/table.html Kaby Lake
# This just encodes the maximum execution time for each instruction
# So timing properties should be written
#    cycle_count_of_trace t <= x
def time_of_instr(mnemonic: str, args: List[X86Var]) -> str :
    match mnemonic:
        case "push":
            return "12"
        case "mov":
            return "207"
        case "jmp":
            return "44"
        case "shl":
            return "16"
        case "add":
            return "11"
        case "cmp":
            return "6"
        case "jle":
            return "12"
        case "pop":
            return "11"
        case "ret":
            return "18"
