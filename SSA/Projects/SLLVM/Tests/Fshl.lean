/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.intr.fshl`

The funnel shift left: the high operand and the low operand concatenated,
shifted left, and the top `w` bits kept. `fd_curve25519_scalar_reduce` emits it
for the `(lo >> (64-n)) | (hi << n)` idiom its 21-bit unpacking uses.
-/

namespace LeanMLIR.SLLVM.Tests.Fshl
open LeanMLIR
open InstCombine (LLVM)

def funnel : Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8, SLLVM.Ty.bitvec 8])
    .pure [SLLVM.Ty.bitvec 8] := [sllvm| {
  ^entry(%a : i8, %b : i8, %n : i8):
    %r = "llvm.intr.fshl"(%a, %b, %n) : (i8, i8, i8) -> i8
    "llvm.return"(%r) : (i8) -> ()
}]

/-- `fshl a b 0 = a`: nothing of `b` reaches the top half. -/
example : (funnel.denote (Ctxt.Valuation.ofHVector
    [(.value 0#8 : LLVM.IntW 8), .value 0b11110000#8, .value 0b10101010#8]ₕ)).head
      = .value 0b10101010#8 := rfl

/-- One bit of the low operand shifts in. -/
example : (funnel.denote (Ctxt.Valuation.ofHVector
    [(.value 1#8 : LLVM.IntW 8), .value 0b11110000#8, .value 0b10101010#8]ₕ)).head
      = .value 0b01010101#8 := rfl

/-- The amount is taken modulo the width: `n = 8` wraps to `0`, so the result
is `a` -- not `b`, and not poison as an over-long `shl` would be. -/
example : (funnel.denote (Ctxt.Valuation.ofHVector
    [(.value 8#8 : LLVM.IntW 8), .value 0b11110000#8, .value 0b10101010#8]ₕ)).head
      = .value 0b10101010#8 := rfl

/-- Poison in the shift amount is poison out. -/
example : (funnel.denote (Ctxt.Valuation.ofHVector
    [(.poison : LLVM.IntW 8), .value 0b11110000#8, .value 0b10101010#8]ₕ)).head
      = .poison := rfl

end LeanMLIR.SLLVM.Tests.Fshl
