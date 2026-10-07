import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock7 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 261).take 4}

def productEnv7 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v219 : BitVec 128 := (x3.setWidth 128) * 17592186044415#128
  let v220 : BitVec 128 := (x4.setWidth 128) * 4503599627370495#128
  let v221 : BitVec 128 := v220 + v219
  E[%219 := .value v219][%220 := .value v220][%221 := .value v221]

def productWord7 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v219 : BitVec 128 := (x3.setWidth 128) * 17592186044415#128
  let v220 : BitVec 128 := (x4.setWidth 128) * 4503599627370495#128
  let v221 : BitVec 128 := v220 + v219
  v221

theorem product_chunk7 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p88 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p88 16)
    (hp : E.read (%88) = .value p88)
    (h194 : E.read (%194) = .value (x3.setWidth 128))
    (h204 : E.read (%204) = .value (x4.setWidth 128))
    (hk27 : E.read (%27) = .value 4503599627370495#128)
    (hk28 : E.read (%28) = .value 17592186044415#128)
    : productBlock7.runBodyFrom E 0 s =
      .value (productEnv7 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p88 (productWord7 x0 x1 x2 x3 x4)}) := by
  let v219 : BitVec 128 := (x3.setWidth 128) * 17592186044415#128
  obtain ⟨h219u, h219s, h219n⟩ := product_constant_flags x3 17592186044415#128 hx3 (by decide)
  let v220 : BitVec 128 := (x4.setWidth 128) * 4503599627370495#128
  obtain ⟨h220u, h220s, h220n⟩ := product_constant_flags x4 4503599627370495#128 hx4 (by decide)
  let v221 : BitVec 128 := v220 + v219
  have h221bound : (v220).toNat + (v219).toNat < 2 ^ 127 := by
    simp only [v219, v220, v221, h219n, h220n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h221u, h221s, h221n⟩ := product_add_flags (v220) (v219) h221bound
  dsimp only [v219, v220, v221] at h221u h221s h221n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock7.runBodyFrom E' 0 S =
        .value (productEnv7 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p88 (productWord7 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p88 128 := by rw [hS]; exact hr.fits
  step_pure [h194, h204, hk27, hk28, h219u, h219s]
  step_pure [h194, h204, hk27, hk28, h220u, h220s]
  step_pure [h194, h204, hk27, hk28, h221u, h221s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word7_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord7 x0 x1 x2 x3 x4).toNat = ((x4.toNat * 4503599627370495) + (x3.toNat * 17592186044415)) := by
  let v219 : BitVec 128 := (x3.setWidth 128) * 17592186044415#128
  obtain ⟨h219u, h219s, h219n⟩ := product_constant_flags x3 17592186044415#128 hx3 (by decide)
  let v220 : BitVec 128 := (x4.setWidth 128) * 4503599627370495#128
  obtain ⟨h220u, h220s, h220n⟩ := product_constant_flags x4 4503599627370495#128 hx4 (by decide)
  let v221 : BitVec 128 := v220 + v219
  have h221bound : (v220).toNat + (v219).toNat < 2 ^ 127 := by
    simp only [v219, v220, v221, h219n, h220n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h221u, h221s, h221n⟩ := product_add_flags (v220) (v219) h221bound
  dsimp only [v219, v220, v221] at h221u h221s h221n
  change v221.toNat = _
  norm_num [v219, v220, v221, h219n, h220n, h221n]

end Agave.Ed25519.ScalarReduce32.Execution
