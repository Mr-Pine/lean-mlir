/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_pow22523_2
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

/-!
# One `fd_r43x6_pow22523_2` call, peeled

`Step/fd_r43x6_repsqr_mul2.lean`'s shape for the ladder's caller: the
conformance theorem packaged as a run equation plus a `Wrote2`, and then in the
continuation form a walk can afford.

The kernel writes two `wwl_t` out-parameters, so what it leaves is `Wrote2` --
which is also what lets the two `load`s after the call read the exponentials
back out of the slots.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **One `fd_r43x6_pow22523_2( za, xa, zb, xb )` call**, in the form
`peel_call` takes it. -/
theorem pow22523_2_step (za zb : Pointer) (xa xb : Vector (BitVec 64) 8)
    {u : GlobalState} (hu : u.WF)
    (hza : IsVecPtr u.mem za) (hzb : IsVecPtr u.mem zb) (hne : za.id ≠ zb.id)
    (hxa : R43x6.U47 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hxb : R43x6.U47 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0) :
    ∃ (u' : GlobalState) (oa ob : Vector (BitVec 64) 8),
      StateT.run (runFunction (fd_r43x6_pow22523_2.denote (Ctxt.Valuation.ofHVector
          [xb.map PoisonOr.value, .value zb, xa.map PoisonOr.value, .value za]ₕ))) u
        = .value ([]ₕ, u')
      ∧ vecValue oa = vecValue xa ^ (2 ^ 252 - 3)
      ∧ vecValue ob = vecValue xb ^ (2 ^ 252 - 3)
      ∧ Wrote2 za zb oa ob u u' := by
  obtain ⟨u', hrun, oa, ob, heq, hva, hvb, h44a, h44b, z6a, z7a, z6b, z7b⟩ :=
    fd_r43x6_pow22523_2_conforms za zb xa xb u hu hza hzb hne hxa hxa6 hxa7 hxb hxb6 hxb7
  have hwf : ({ alloc := u.alloc, mem := (u.mem.splice za (vecBV oa)).splice zb (vecBV ob), globals := u.globals } : GlobalState).WF := hu.splice.splice
  refine ⟨u', oa, ob, hrun, hva, hvb, ?_⟩
  refine { wf := GlobalState.WF.of_equiv hwf (GlobalState.Equiv.symm heq)
           globals := heq.globals
           other := ?other
           mem := heq
           ptrA := ?ptrA, ptrB := ?ptrB, valA := ?valA, valB := ?valB
           u44A := h44a, u44B := h44b
           z6A := z6a, z7A := z7a, z6B := z6b, z7B := z7b }
  case other =>
    intro c hca hcb
    rw [heq.live c, live?_splice_ne (fun h => hcb h.symm),
      live?_splice_ne (fun h => hca h.symm)]
  case ptrA =>
    exact ⟨fits_of_live?_eq (heq.live za.id) (fits_splice (fits_splice hza.1)), hza.2⟩
  case ptrB =>
    exact ⟨fits_of_live?_eq (heq.live zb.id) (fits_splice (fits_splice hzb.1)), hzb.2⟩
  case valA =>
    refine readVec_eq_of ?_
    rw [readVec?_of_live?_eq (heq.live za.id), readVec?_splice_ne (Ne.symm hne)]
    exact readVec?_splice_self oa hza
  case valB =>
    refine readVec_eq_of ?_
    rw [readVec?_of_live?_eq (heq.live zb.id)]
    exact readVec?_splice_self ob ⟨fits_splice hzb.1, hzb.2⟩

/-- **`pow22523_2_step` in continuation form**, for the same reason
`repsqr_mul2_step'` has one: an `obtain` against a walk's goal reverts it. -/
theorem pow22523_2_step' (za zb : Pointer) (xa xb : Vector (BitVec 64) 8)
    {u : GlobalState} (hu : u.WF)
    (hza : IsVecPtr u.mem za) (hzb : IsVecPtr u.mem zb) (hne : za.id ≠ zb.id)
    (hxa : R43x6.U47 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hxb : R43x6.U47 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0)
    {P : Prop}
    (k : ∀ (u' : GlobalState) (oa ob : Vector (BitVec 64) 8),
      StateT.run (runFunction (fd_r43x6_pow22523_2.denote (Ctxt.Valuation.ofHVector
          [xb.map PoisonOr.value, .value zb, xa.map PoisonOr.value, .value za]ₕ))) u
        = .value ([]ₕ, u') →
      vecValue oa = vecValue xa ^ (2 ^ 252 - 3) →
      vecValue ob = vecValue xb ^ (2 ^ 252 - 3) →
      Wrote2 za zb oa ob u u' → P) : P := by
  obtain ⟨u', oa, ob, h₁, h₂, h₃, h₄⟩ :=
    pow22523_2_step za zb xa xb hu hza hzb hne hxa hxa6 hxa7 hxb hxb6 hxb7
  exact k u' oa ob h₁ h₂ h₃ h₄

end Firedancer.Avx512
