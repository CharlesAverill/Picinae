"""Finite decoder/metadata checks, independent of any pcode2coq driver."""
import unittest

from amd64_vector_layout import register_view, register_slice, vector_operand, writemask


class LayoutTests(unittest.TestCase):
    def test_every_vector_view_aliases_one_cell(self):
        for slot in range(32):
            for prefix, size in (("XMM", 16), ("YMM", 32), ("ZMM", 64)):
                view = register_view(f"{prefix}{slot}", size)
                self.assertEqual(view, register_slice(0x1200 + slot * 64, size))
                self.assertEqual((view.bank, view.slot, view.low_bit, view.physical_bits),
                                 ("R_ZMM", slot, 0, 512))

    def test_mask_width_and_high_byte(self):
        for slot in range(8):
            self.assertEqual(register_view(f"K{slot}", 8), register_slice(2100 + slot*8, 8))
        top = register_slice(2100 + 7*8 + 7, 1)
        self.assertEqual((top.slot, top.low_bit, top.bits, top.physical_bits), (7, 56, 8, 64))

    def test_vector_high_lane(self):
        top = register_slice(0x1200 + 31*64 + 63, 1)
        self.assertEqual((top.slot, top.low_bit, top.bits), (31, 504, 8))

    def test_reject_unknown_names_and_widths(self):
        for name, size in (("ZMM32", 64), ("K8", 8), ("XMM01", 16), ("zmm0", 64),
                           ("ZMM0", 32), ("YMM31", 64), ("K1", 1), ("RAX", 8),
                           ("XMM0", True), ("ZMM-1", 64)):
            with self.assertRaises(ValueError):
                register_view(name, size)

    def test_reject_invalid_varnodes(self):
        for offset, size in ((0x11ff, 1), (0x1a00, 1), (0x123f, 2), (2163, 2),
                             (2164, 1), (0x1200, 0), (0x1200, -1), (True, 8)):
            with self.assertRaises(ValueError):
                register_slice(offset, size)

    def test_encoding_reach(self):
        vector_operand("XMM15", 16, "legacy")
        vector_operand("YMM15", 32, "vex")
        vector_operand("YMM31", 32, "evex")
        vector_operand("ZMM31", 64, "evex")
        for name, size, enc in (("YMM0", 32, "legacy"), ("XMM16", 16, "legacy"),
                                ("YMM16", 32, "vex"), ("ZMM0", 64, "vex"),
                                ("K1", 8, "evex"), ("XMM0", 16, "unknown")):
            with self.assertRaises(ValueError):
                vector_operand(name, size, enc)

    def test_mask_policy(self):
        self.assertEqual(writemask(0), {"slot": None, "policy": "unmasked"})
        self.assertEqual(writemask(7), {"slot": 7, "policy": "merge"})
        self.assertEqual(writemask(1, True), {"slot": 1, "policy": "zero"})
        self.assertEqual(writemask(1, memory_destination=True)["policy"], "merge")
        for args in ((0, True, False), (1, True, True), (8, False, False),
                     (-1, False, False), (True, False, False)):
            with self.assertRaises(ValueError):
                writemask(*args)


if __name__ == "__main__":
    unittest.main(verbosity=2)
