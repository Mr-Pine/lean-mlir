"""Negative checks for the narrow compiler-region normalization boundary."""
from pathlib import Path
import unittest
from verify import normalized_region

ROOT = Path(__file__).resolve().parent


class RegionIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.original = (ROOT / "generated/agave_serial_field_mul.mlir").read_text()
        self.lift = (ROOT.parent / "Proof/SerialFieldMul/Lift.lean").read_text()

    def test_exact_lift_matches_after_syntax_normalization(self):
        self.assertEqual(normalized_region(self.original), normalized_region(self.lift))

    def test_changed_limb_offset_does_not_match(self):
        changed = self.lift.replace("rawConstantIndices = array<i32: 8>",
                                    "rawConstantIndices = array<i32: 9>", 1)
        self.assertNotEqual(normalized_region(self.original), normalized_region(changed))

    def test_removed_overflow_promise_does_not_match(self):
        changed = self.lift.replace("#llvm.overflow<nuw>", "#llvm.overflow<none>", 1)
        self.assertNotEqual(normalized_region(self.original), normalized_region(changed))

    def test_changed_arithmetic_does_not_match(self):
        changed = self.lift.replace('"llvm.mul"', '"llvm.add"', 1)
        self.assertNotEqual(normalized_region(self.original), normalized_region(changed))

    def test_changed_width_does_not_match(self):
        changed = self.lift.replace("(i128, i128) -> i128", "(i128, i128) -> i64", 1)
        self.assertNotEqual(normalized_region(self.original), normalized_region(changed))


if __name__ == "__main__":
    unittest.main()
