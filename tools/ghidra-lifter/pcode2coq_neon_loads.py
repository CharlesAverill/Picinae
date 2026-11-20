"""Opt-in fixed-Z256 Q-load profile; no scalable SVE or function soundness claim.

Only exact Ghidra 11.4.2 LDR/LDP Q encoding/DAG pairs enter vector lowering.
The scalar default is deliberately unmodified. D64 and Q128 are slices of the
existing Z256 cells, never independent architectural state.
"""
from pcode2coq_scalar import ScalarLifter, Unsupported, seq


class NeonLoadLifter(ScalarLifter):
    PROFILE = 'aarch64-neon-q-loads-fixed-z256-v1'

    def vector_register(self, vn):
        offset, size = int(vn.getOffset()), int(vn.getSize())
        index, byte = divmod(offset - 0x5000, 32)
        if not 0 <= index < 32 or (byte, size) not in {(0, 8), (0, 16), (0, 32), (16, 8), (24, 8)}:
            raise Unsupported('unsupported fixed-Z256 register slice')
        # The upper64 slices are unnamed in pinned SLEIGH. Validate their
        # enclosing named base explicitly rather than inventing Q/D cells.
        base = self.lang.getRegister('z' + str(index))
        if (base is None or str(base.getName()).lower() != 'z' + str(index)
                or int(base.getBitLength()) != 256
                or int(base.getAddress().getOffset()) != 0x5000 + 32 * index
                or str(base.getBaseRegister().getName()).lower() != 'z' + str(index)
                or int(base.getBaseRegister().getBitLength()) != 256
                or int(base.getBaseRegister().getAddress().getOffset()) != 0x5000 + 32 * index):
            raise Unsupported('pinned Z256 base metadata mismatch')
        actual = self.lang.getRegister(vn.getAddress(), size)
        if byte == 0 and actual is None:
            raise Unsupported('missing pinned low vector slice metadata')
        if actual is not None:
            b = actual.getBaseRegister()
            if (str(b.getName()).lower(), int(b.getBitLength()), int(b.getAddress().getOffset())) != (
                    'z' + str(index), 256, 0x5000 + 32 * index):
                raise Unsupported('pinned vector slice metadata mismatch')
        return f'R_Z{index}', 256, byte * 8

    def register(self, vn):
        if 0x5000 <= int(vn.getOffset()) < 0x5400:
            return self.vector_register(vn)
        return super().register(vn)

    def instruction(self, insn):
        raw = bytes(int(b) & 255 for b in insn.getBytes())
        if len(raw) != 4 or int(insn.getLength()) != 4:
            raise Unsupported('non-A64 encoding length')
        bits = int.from_bytes(raw, 'little')
        kind = None
        if bits & 0xffc00000 == 0x3dc00000:
            kind, mode, offset = 'ldr', 'offset', ((bits >> 10) & 4095) * 16
        elif bits & 0xffe00c00 in (0x3cc00400, 0x3cc00c00):
            kind = 'ldr'
            mode = 'post' if bits & 0xc00 == 0x400 else 'pre'
            imm = (bits >> 12) & 511
            offset = imm - 512 if imm & 256 else imm
        elif bits & 0xffe00c00 == 0x3ce00800:
            kind, mode, offset = 'ldr', 'register', 0
        elif bits & 0xffc00000 in (0xad400000, 0xadc00000, 0xacc00000):
            kind = 'ldp'
            mode = {0xad400000: 'offset', 0xadc00000: 'pre', 0xacc00000: 'post'}[bits & 0xffc00000]
            imm = (bits >> 15) & 127
            offset = (imm - 128 if imm & 64 else imm) * 16
        if kind is None:
            # Never dispatch scalar instructions through vector-aware register().
            return ScalarLifter(self.lang, self.base).instruction(insn)
        if str(insn.getMnemonicString()).lower() != kind:
            raise Unsupported('Q load mnemonic/encoding mismatch')
        rd, rn, rt2 = bits & 31, (bits >> 5) & 31, (bits >> 10) & 31
        if kind == 'ldp' and rd == rt2:
            raise Unsupported('overlapping Q pair is constrained unpredictable')
        expected = []
        t = lambda i: ('t', i, 8)
        c = lambda value, size=8: ('c', value % (1 << (size * 8)), size)
        r = lambda index, size=8: ('r', 'R_SP' if index == 31 else f'R_X{index}', 64, 0, size)
        z = lambda index, byte=0, size=16: ('r', f'R_Z{index}', 256, byte*8, size)
        def emit(code, out, *args):
            expected.append((code, out, tuple(args)))
        if mode == 'register':
            rm, option, shift = (bits >> 16) & 31, (bits >> 13) & 7, 4 if bits & 0x1000 else 0
            if rm == 31 or option not in (2, 3, 6, 7):
                raise Unsupported('unsupported Q load index/extension')
            if option in (2, 6):
                emit('INT_ZEXT' if option == 2 else 'INT_SEXT', t(0), r(rm, 4))
                emit('INT_LEFT', t(1), t(0), c(shift, 1))
                emit('INT_ADD', t(2), r(rn), t(1))
                address = t(2)
            else:
                emit('INT_LEFT', t(0), r(rm), c(shift, 1))
                emit('INT_ADD', t(1), r(rn), t(0))
                address = t(1)
        elif mode == 'pre':
            emit('INT_ADD', r(rn), r(rn), c(offset))
            address = r(rn)
        else:
            emit('COPY' if mode == 'post' or offset == 0 else 'INT_ADD', t(0), r(rn),
                 *(() if mode == 'post' or offset == 0 else (c(offset),)))
            address = t(0)
            if mode == 'post':
                emit('INT_ADD', r(rn), r(rn), c(offset))
        def load(index, address):
            emit('LOAD', z(index), c(0x1b1), address)
            emit('COPY', z(index, 16, 8), c(0))
            emit('COPY', z(index, 24, 8), c(0))
        load(rd, address)
        if kind == 'ldp':
            # After the first load and its upper zeroes, using the same
            # snapshotted/effective base, not the post-writeback base.
            emit('INT_ADD', t(1) if mode != 'pre' else t(0), address, c(16))
            load(rt2, t(1) if mode != 'pre' else t(0))
        self.temps, self.ranges, self.initialized = {}, [], set()
        slots = {}
        def node(v):
            if v is None:
                return None
            size = int(v.getSize())
            if size <= 0:
                raise Unsupported('zero width Q-load node')
            if v.isUnique():
                self.temp(v)  # Reject overlapping ranges even before matching.
                key = int(v.getOffset()), size
                return 't', slots.setdefault(key, len(slots)), size
            if v.isRegister():
                name, width, offset = self.register(v)
                # Scalar metadata must also agree with pinned physical offsets.
                if name.startswith('R_X') and int(v.getOffset()) != 0x4000 + int(name[3:])*8:
                    raise Unsupported('pinned X register offset mismatch')
                if name == 'R_SP' and int(v.getOffset()) != 8:
                    raise Unsupported('pinned SP offset mismatch')
                return 'r', name, width, offset, size
            if v.isConstant():
                return c(int(v.getOffset()), size)
            raise Unsupported('unsupported Q load node')
        ops = list(insn.getPcode())
        actual = [(str(o.getMnemonic()), node(o.getOutput()), tuple(node(v) for v in o.getInputs())) for o in ops]
        if actual != expected:
            raise Unsupported('Q load encoding/raw DAG mismatch')
        # Lower the entire checked raw sequence, including writeback, slice
        # merges and both explicit upper64 zero writes. No synthetic Nop.
        self.temps, self.ranges, self.initialized = {}, [], set()
        return seq([self.statement(o) for o in ops])
