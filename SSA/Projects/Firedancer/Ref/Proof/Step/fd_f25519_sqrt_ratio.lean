/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_sqrt_ratio

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One `fd_f25519_sqrt_ratio( dst, su, sv )` call, peeled. Not in
`mul_step`'s shape, for two reasons: the call hands back the `i32` flag rather
than a pointer, and what it leaves at `dst` is an existential root with three
properties rather than one value.

`@fd_f25519_sqrtm1` comes in as a hypothesis because the *callee* addresses
it, at its own `%6` -- this region never mentions the symbol. That is what
`Wrote.globals` buys: the `addr` half has to survive every step of the walk to
get here. -/
theorem sqrtRatio_step {dst su sv pm1 : Pointer} {w : GlobalState} (hw : w.WF)
    (hd : IsFieldElemPtr w.mem dst)
    (h₀ : IsFieldElemPtr w.mem su) (h₁ : IsFieldElemPtr w.mem sv)
    (hm1 : FieldGlobal w "fd_f25519_sqrtm1" pm1 _root_.sqrtm1) (hm1d : pm1.id ≠ dst.id)
    {x₀ x₁ : ZMod _root_.p} (hv₀ : readFieldElem h₀ = x₀) (hv₁ : readFieldElem h₁ = x₁)
    (hb₀ : LimbBounds h₀) (hb₁ : LimbBounds h₁)
    (hud : su.id ≠ dst.id) (hvd : sv.id ≠ dst.id) :
    ∃ w' : GlobalState, ∃ hw' : Wrote dst w w', ∃ root : ZMod _root_.p,
      StateT.run (runFunction (fd_f25519_sqrt_ratio.denote
          (Ctxt.Valuation.ofHVector [.value sv, .value su, .value dst]ₕ))) w
        = .value ([(.value (if ∃ z : ZMod _root_.p, z ^ 2 * x₁ = x₀ then 1#32 else 0#32)
            : LLVM.IntW 32)]ₕ, w')
      ∧ readFieldElem hw'.ptr = root
      -- `fd_f25519_abs` leaves the non-negative representative
      ∧ root.val % 2 = 0
      ∧ ((∃ z : ZMod _root_.p, z ^ 2 * x₁ = x₀) → root ^ 2 * x₁ = x₀)
      ∧ (x₁ = 0 → root = 0)
      ∧ BiasBounds hw'.ptr ∧ limbSum hw'.ptr < 2 ^ 256 - 38 := by
  obtain ⟨out, heven, hsq, hzero, hbnd, hsum, w', hrun, heq⟩ :=
    fd_f25519_sqrt_ratio_conforms dst su sv w hw
      ⟨pm1, hm1.ptr, hm1.addr, hm1.value, hm1.bnd, hm1d⟩ hd h₀ h₁ hb₀ hb₁ hud hvd
  rw [hv₀, hv₁] at hrun hsq
  rw [hv₁] at hzero
  have hwrote : Wrote dst w w' := Wrote.of_splice hw hd heq
  -- the root as the spec states it -- read out of the spliced state, not `w'`
  have hroot : readFieldElem hwrote.ptr
      = readFieldElem (m := w.mem.splice dst (packLimbs out)) (isFieldElemPtr_splice hd) :=
    readFieldElem_eq_splice hd heq
  refine ⟨w', hwrote, readFieldElem hwrote.ptr, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hroot]; exact heven
  · intro h; rw [hroot]; exact hsq h
  · intro h; rw [hroot]; exact hzero h
  · exact biasBounds_of_splice heq (biasBounds_readLimb? _ hbnd)
  · rw [limbSum_of_splice hd heq]; exact hsum

end Firedancer.Ref
