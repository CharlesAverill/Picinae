"""Explicit composition of reviewed e25/e26/e27/e28 sequential projections.

Dispatch once; a failed family gate never falls back to another translator.
No new encodings, instructions, or semantic correctness claims.
"""
from pcode2coq_x64 import X64Lifter, Unsupported
from pcode2coq_x64_copy import CopyLifter, MOVES
from pcode2coq_x64_rep import X64RepLifter, ENCODINGS


class IntegratedLifter(CopyLifter, X64RepLifter):
    def __init__(self, language, cet_disabled=False, bmi1=None, abm=None):
        if type(cet_disabled) is not bool or bmi1 not in (None, 'unspecified', 'present', 'absent') or abm not in (None, 'unspecified', 'present', 'absent'):
            raise Unsupported('invalid explicit feature profile')
        X64Lifter.__init__(self, language, cet_disabled, bmi1, abm)

    def instruction(self, insn):
        self.temps, self.ranges, self.initialized = {}, [], set()
        try:
            name = str(insn.getMnemonicString()).upper()
            raw = bytes(int(b) & 255 for b in insn.getBytes())
            if name in MOVES:
                return CopyLifter.instruction(self, insn)
            if raw in ENCODINGS:
                return X64RepLifter.instruction(self, insn)
            # Includes guarded scans via the e28 dynamic import. No generic
            # vector API or relaxed scalar prefix/control-flow permission.
            return X64Lifter.instruction(self, insn)
        finally:
            # Reuse after success OR failure cannot carry instruction locals.
            self.temps, self.ranges, self.initialized = {}, [], set()
