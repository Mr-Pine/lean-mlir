/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Tactic
import SSA.Projects.Firedancer.Avx512.Mlir.fd_long_if
import SSA.Projects.Firedancer.Avx512.Spec.fd_long_if

/-!
# `fd_long_if` denotes to `fdLongIf`

The region is five instructions and the derivation is a case split on whether
the argument is poison. It is stated separately from
`fd_r43x6_is_nonzero` because that is how it will be *used*: `Com` has no
calls, so the standing workaround is to inline the callee, and a lemma about
the callee is what makes the inlining a rewrite rather than a re-derivation.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- **Denotation of `fd_long_if`**: the specialised conditional subtract,
poison in and poison out. -/
theorem denote_fd_long_if (c : LLVM.IntW 32) :
    fd_long_if.denote (Ctxt.Valuation.singleton c) =
      ([fdLongIf c]ₕ : HVector TyDenote.toType [SLLVM.Ty.arith (.bitvec (.concrete 64))]) := by
  simp only [fd_long_if]
  simp_peephole
  cases c using PoisonOr.casesOn' with
  | poison => rfl
  | value v =>
    simp only [Ctxt.Valuation.singleton, LLVM.const?, fdLongIf, LLVM.select,
      LLVM.icmp, LLVM.icmp?, LLVM.icmp']
    by_cases h : v = 0#32
    · subst h; rfl
    · have hb : (v == 0#32) = false := by simpa using h
      simp [BitVec.ofBool, hb, h]

end Firedancer.Avx512
