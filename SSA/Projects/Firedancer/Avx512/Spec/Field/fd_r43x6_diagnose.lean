/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_diagnose
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Spec.Util.fd_long_if

/-!
# What `fd_r43x6_diagnose` is specified to compute

`-1` if the reduced element is zero, and its low bit otherwise -- the sign
test point decompression branches on. It runs the same chain as
`fd_r43x6_is_nonzero` (`reduce`, a biased carry propagate at `2^20` followed
by the conditional subtract of `p`) and reads bit 0 off the end instead of
comparing the six limbs against zero.

`-1` rather than `0` for the zero case is what makes decompression's
`x_0 != x_mod_2` test reject a zero `x` with the sign bit set; the reference
implementation and Dalek differ there, and this is where the difference is
visible.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The `int` the C returns. -/
def diagnose (x : Fin R43x6.limbCount → ℤ) : BitVec 32 :=
  if isNonzero x = 0 then -1#32 else BitVec.ofInt 32 (reduce x 0 % 2)

/-- The region denotes to it, on a signed input the carry chains do not
overflow at -- the `s62` the header asks for. -/
abbrev fd_r43x6_diagnose_spec (x : Vector (BitVec 64) 8) : Prop :=
  R43x6.S62 (x.take R43x6.limbCount) →
    (fd_r43x6_diagnose.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))).head
      = .value (diagnose (R43x6.extractLimbs x))

end Firedancer.Avx512
