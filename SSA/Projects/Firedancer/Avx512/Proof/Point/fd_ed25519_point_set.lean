/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

/-!
# `fd_ed25519_point_set` conformance

Three whole-vector load/store pairs at 0, 64 and 128 bytes. Each load reads
`a`'s block, which the preceding stores into `r`'s block leave alone.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_point_set_conforms (r a : Pointer) (s : GlobalState) (hs : s.WF)
    (hne : r.id ≠ a.id) (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) :
    fd_ed25519_point_set_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_set_spec, Cfg.denote]
  refine ⟨_, run_runFunction (s' := { s with mem := s.mem.writeQuad r (readQuad ha) }) ?run,
    ?equiv⟩
  -- no allocas, so `popFrame` kills no live block
  case equiv =>
    exact GlobalState.Equiv.symm (killFrom_equiv_of_none fun q hq =>
      live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (hs q hq))))

  case run =>
    denote_expose

    obtain ⟨ablk, hablkE, halen⟩ := ha.1
    have halive : s.mem.live? a.id = some ablk := by simp [MemoryState.live?, hablkE]
    have h64 : (64 : BitVec 64).toNat = 64 := rfl
    have h128 : (128 : BitVec 64).toNat = 128 := rfl

    -- `%0`: `v03`, stored to `r`
    peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, a, hablkE, s
    rw [unflatten_readQuad_v03 ha halive]
    refine name_of ({ s with mem := s.mem.splice r (vecBV (readQuad ha).v03) })
      fun s₁ hs₁ => ?_
    peel_store (readQuad ha).v03, r, hr.1, s as s₁ := hs₁
    have f₁ : Fits s₁.mem r (3 * 8 * 64) := hs₁ ▸ fits_splice hr.1

    -- `%1 … %3`: `v14`, stored 64 bytes into `r`
    peel_gep 64 with a, ha.1, s as aField
    have hoffA : aField.offsetInBits = a.offsetInBits + 512 := by
      have hb := ha.2
      simp only [aField, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
      omega
    have hE₁ : s₁.mem[aField.id]? = some (.live ablk) := by
      rw [hs₁]
      exact (getElem?_splice_ne (m := s.mem) (p := r) (x := vecBV (readQuad ha).v03)
        (q := aField.id) hne).trans hablkE
    peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField, hE₁, s₁
    rw [hoffA, unflatten_readQuad_v14 ha halive]
    peel_gep 64 with r, f₁, s₁ as rField
    have fR : Fits s₁.mem rField 1024 := Fits.mono hrField (by simp)
    refine name_of ({ s₁ with mem := s₁.mem.splice rField (vecBV (readQuad ha).v14) })
      fun s₂ hs₂ => ?_
    peel_store (readQuad ha).v14, rField, fR, s₁ as s₂ := hs₂
    have f₂ : Fits s₂.mem r (3 * 8 * 64) := hs₂ ▸ fits_splice f₁

    -- `%4 … %6`: `v25`, stored 128 bytes into `r`
    peel_gep 128 with a, ha.1, s as aField25
    have hoffA25 : aField25.offsetInBits = a.offsetInBits + 1024 := by
      have hb := ha.2
      simp only [aField25, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
        h128] at hb ⊢
      omega
    have hE₂ : s₂.mem[aField25.id]? = some (.live ablk) := by
      rw [hs₂]
      exact (getElem?_splice_ne (m := s₁.mem) (p := rField) (x := vecBV (readQuad ha).v14)
        (q := aField25.id) hne).trans hE₁
    peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField25, hE₂, s₂
    rw [hoffA25, unflatten_readQuad_v25 ha halive]
    peel_gep 128 with r, f₂, s₂ as rField25
    have fR25 : Fits s₂.mem rField25 512 := Fits.mono hrField25 (by simp)
    peel_store (readQuad ha).v25, rField25, fR25, s₂

    simp_return
    rw [hs₂, hs₁]
    exact ⟨rfl, rfl, rfl⟩

end Firedancer.Avx512
