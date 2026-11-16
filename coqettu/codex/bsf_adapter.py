"""Recognize Ghidra 12's exact register-to-register i386 BSF p-code graph.

No generic back edge is accepted. A recognized graph scans a 32-bit source
from bit zero, so 32 guarded iterations suffice. Once a set bit is found,
the counter is unchanged by any remaining guarded iterations. Only temporary
values are recomputed; Picinae resets them at the instruction boundary.
"""


def key(vn):
    return None if vn is None else (vn["space"], vn["offset"], vn["size"])


def is_bsf32(ops):
    if [op["mnemonic"] for op in ops] != [
        "COPY", "INT_EQUAL", "INT_EQUAL", "CBRANCH", "INT_RIGHT", "INT_AND",
        "INT_NOTEQUAL", "CBRANCH", "INT_ADD", "BRANCH", "COPY",
    ]:
        return False
    outputs = [key(op["output"]) for op in ops]
    inputs = [[key(vn) for vn in op["inputs"]] for op in ops]
    counter, flag, zero_test, _, shifted, low_bit, found = outputs[:7]
    if any(vn is None for vn in [counter, flag, zero_test, shifted, low_bit, found, outputs[10]]):
        return False
    if len(inputs[1]) != 2:
        return False
    source = inputs[1][0]
    registers = {("register", offset, 4) for offset in range(0, 32, 4)}
    if source not in registers or outputs[10] not in registers or flag != ("register", 0x206, 1):
        return False
    temporaries = [(counter, 4), (zero_test, 1), (shifted, 4), (low_bit, 4), (found, 1)]
    if any(vn[0] != "unique" or vn[2] != size for vn, size in temporaries):
        return False
    ranges = [(vn[1], vn[1] + vn[2]) for vn, _ in temporaries]
    if any(max(a, c) < min(b, d) for i, (a, b) in enumerate(ranges) for c, d in ranges[i + 1:]):
        return False
    return outputs == [counter, flag, zero_test, None, shifted, low_bit, found, None, counter, None, outputs[10]] and inputs == [
        [("const", 0, 4)],
        [source, ("const", 0, 4)],
        [flag, ("const", 1, 1)],
        [("const", 7, 4), zero_test],
        [source, counter],
        [shifted, ("const", 1, 4)],
        [low_bit, ("const", 0, 4)],
        [("const", 3, 4), found],
        [counter, ("const", 1, 4)],
        [("const", 0xFFFFFFFB, 4)],
        [counter],
    ]
