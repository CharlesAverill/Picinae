"""Checks for the narrowly scoped bounded-BSF p-code adaptation."""
import copy
import json
import random
import unittest
from pathlib import Path

from bsf_adapter import is_bsf32

OPS = json.loads((Path(__file__).parent / "bsf32_pcode.json").read_text())["instruction"]["ops"]


def reference(value):
    if not value:
        return 0  # Ghidra's modeled choice for the architecturally undefined result.
    bit = 0
    while not ((value >> bit) & 1):
        bit += 1
    return bit


def bounded(value):
    bit = 0
    if value:
        for _ in range(32):
            if not ((value >> bit) & 1):
                bit += 1
    return bit


class BSFAdapterTests(unittest.TestCase):
    def test_accepts_captured_graph(self):
        self.assertTrue(is_bsf32(OPS))

    def test_all_general_register_source_destination_pairs(self):
        for source in range(0, 32, 4):
            for destination in range(0, 32, 4):
                ops = copy.deepcopy(OPS)
                ops[1]["inputs"][0]["offset"] = source
                ops[4]["inputs"][0]["offset"] = source
                ops[10]["output"]["offset"] = destination
                self.assertTrue(is_bsf32(ops))

    def test_rejects_changed_branches_constants_and_dataflow(self):
        for index, field, operand in [
            (0, "inputs", 0), (1, "inputs", 1), (2, "inputs", 1),
            (3, "inputs", 0), (4, "inputs", 1), (5, "inputs", 1),
            (6, "inputs", 1), (7, "inputs", 0), (8, "inputs", 1),
            (9, "inputs", 0), (10, "inputs", 0),
        ]:
            ops = copy.deepcopy(OPS)
            ops[index][field][operand]["offset"] += 1
            self.assertFalse(is_bsf32(ops), (index, field, operand))

    def test_rejects_wrong_width_flag_or_overlapping_temporaries(self):
        for index in (0, 1, 2, 4, 5, 6, 10):
            ops = copy.deepcopy(OPS)
            ops[index]["output"]["size"] *= 2
            self.assertFalse(is_bsf32(ops), index)
        ops = copy.deepcopy(OPS)
        ops[1]["output"]["offset"] += 1
        self.assertFalse(is_bsf32(ops))
        ops = copy.deepcopy(OPS)
        # Preserve all dataflow references while making two temporaries alias.
        alias = ops[0]["output"]["offset"] + 1
        ops[4]["output"]["offset"] = alias
        ops[5]["inputs"][0]["offset"] = alias
        self.assertFalse(is_bsf32(ops))

    def test_guarded_iterations_match_original_scan(self):
        values = list(range(65536)) + [1 << i for i in range(32)]
        generator = random.Random(0xC0E77)
        values += [generator.getrandbits(32) for _ in range(4096)]
        for value in values:
            self.assertEqual(bounded(value), reference(value), hex(value))


if __name__ == "__main__":
    unittest.main()
