/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Tactic
import SSA.Projects.Firedancer.Avx512.Spec.Util.fd_int_if

/-!
# `fd_int_if` conforms to its spec

The region is five instructions and pure, so the derivation is `fd_long_if`'s
-- a case split on whether the condition is poison -- and the function-call
layer on top of it is empty: nothing is allocated, so the frame `runFunction`
pops is the one it entered with.

`denote_fd_int_if` is stated separately because that is how the caller uses
it: `Com` has no calls, so `fd_r43x6_diagnose` inlines the callee, and a
lemma about the callee makes the inlining a rewrite.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- **Denotation of `fd_int_if`**: the specialised select, poison in and
poison out. -/
theorem denote_fd_int_if (c t : LLVM.IntW 32) :
    fd_int_if.denote (Ctxt.Valuation.ofPair t c) =
      ([fdIntIf c t]ₕ : HVector TyDenote.toType [SLLVM.Ty.arith (.bitvec (.concrete 32))]) := by
  simp only [fd_int_if]
  simp_peephole
  cases c using PoisonOr.casesOn' with
  | poison => rfl
  | value v =>
    simp only [LLVM.const?, fdIntIf, LLVM.select, LLVM.icmp, LLVM.icmp?, LLVM.icmp']
    by_cases h : v = 0#32
    · subst h; rfl
    · have hb : (v == 0#32) = false := by simpa using h
      simp [BitVec.ofBool, hb, h]

theorem fd_int_if_conforms (c t : LLVM.IntW 32) (s : GlobalState) (hs : s.WF) :
    fd_int_if_spec c t s := by
  refine ⟨s.popFrame s.mem, run_runFunction ?_, hs.popFrame_equiv⟩
  simp [denote_fd_int_if]

end Firedancer.Avx512
