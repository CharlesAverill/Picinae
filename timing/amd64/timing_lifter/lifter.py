import subprocess
import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional
from dataclasses import dataclass

# Base class (mainly for typing)
class X86Var:
    pass

@dataclass
class Reg(X86Var):
    name: str

    def __repr__(self):
        return self.name.upper()
    
    def __str__(self):
        return self.__repr__()

@dataclass
class Mem(X86Var):
    expr: str
    size: Optional[str] = None

    def unicode_of_size(self):
        if self.size == "byte":
            return "Ⓑ"
        elif self.size == "word":
            return "Ⓦ"
        elif self.size == "dword":
            return "Ⓓ"
        elif self.size == "qword":
            return "Ⓠ"
        else:
            return "UNKNOWN_SIZE"

    def __repr__(self):
        return f"mem{self.unicode_of_size()}[{self.expr}]"

    def __str__(self):
        return self.__repr__()


@dataclass
class Imm(X86Var):
    value: str


def operand_to_string(op: X86Var) -> str:
    match op:
        case Reg(name):
            return f"(reg {name})"
        case Mem(expr, size):
            return f"(mem \"{expr}\" {size})"
        case Imm(value):
            return f"(imm {value})"
        case _:
            return "(unk)"


def parse_operand(op: str) -> X86Var:
    op = op.strip()

    # immediate
    if op.startswith("$"):
        return Imm(op[1:])

    # memory with optional size qualifiers
    size_prefixes = ["byte ptr", "word ptr", "dword ptr", "qword ptr"]
    for prefix in size_prefixes:
        if op.lower().startswith(prefix):
            expr = op[len(prefix):].strip()[1:-1]
            return Mem(expr, size=prefix.split()[0])  # "byte"/"word"/"dword"/"qword"

    # heuristic: has parentheses → memory operand
    if "(" in op:
        return Mem(op)

    # otherwise treat as register
    return Reg(op)



def get_disassembly(binary: str) -> str:
    """Run objdump and return full disassembly text."""
    result = subprocess.run(
        ["objdump", "-d", "-M", "intel", binary, "-M", "no-aliases"],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
    )
    result.check_returncode()
    return result.stdout


def extract_function(disasm: str, func: str) -> List[Tuple[str, str, List[X86Var]]]:
    """Return list of (addr, mnemonic, args) for a function."""
    pattern = re.compile(rf"<{func}>:")
    lines = disasm.splitlines()
    out = []
    in_func = False

    for line in lines:
        if not in_func and pattern.search(line):
            in_func = True
            continue
        if in_func:
            if line.strip() == "" or re.match(r"^[0-9a-f]+ <", line):  # next symbol
                break
            m = re.match(r"\s*([0-9a-f]+):\s+[0-9a-f ]+\s+([a-z]+)\s*(.*)", line)
            if m:
                addr = m.group(1)
                mnemonic = m.group(2)
                args = [parse_operand(op) for op in m.group(3).split(",") if op.strip()]
                out.append((addr, mnemonic, args))
    return out


def generate_rocq(binary: str, functions: List[str]):
    disasm = get_disassembly(binary)

    for func in functions:
        instrs = extract_function(disasm, func)
        print(f"Definition {func}_time_of_addr (s : store) (a : addr) : N :=")
        print("  match a with")
        for addr, mnemonic, args in instrs:
            print(f"  | 0x{addr} => {time_of_instr(mnemonic, args)} (* {mnemonic} {', '.join([str(a) for a in args])} *)")
        print("  | _ => 0")
        print("  end.\n")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("Usage: python lifter.py BIN_PATH CPU_PATH FUNCTION...")
        exit(1)

    path = Path(sys.argv[1])
    cpu = Path(sys.argv[2])
    functions = sys.argv[3:]

    with open(cpu, "r") as file:
        exec(file.read())

    generate_rocq(path, functions)
