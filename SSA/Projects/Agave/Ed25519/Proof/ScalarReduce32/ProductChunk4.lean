import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock4 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 236).take 11}

def productEnv4 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v197 : BitVec 128 := (x0.setWidth 128) * 17592186044415#128
  let v198 : BitVec 128 := (x1.setWidth 128) * 4503599627370495#128
  let v199 : BitVec 128 := v198 + v197
  let v200 : BitVec 128 := (x2.setWidth 128) * 4503599278581019#128
  let v201 : BitVec 128 := v199 + v200
  let v202 : BitVec 128 := (x3.setWidth 128) * 1049714374468698#128
  let v203 : BitVec 128 := v201 + v202
  let v204 : BitVec 128 := x4.setWidth 128
  let v205 : BitVec 128 := (v204) * 4302102966953709#128
  let v206 : BitVec 128 := v203 + v205
  E[%197 := .value v197][%198 := .value v198][%199 := .value v199][%200 := .value v200][%201 := .value v201][%202 := .value v202][%203 := .value v203][%204 := .value v204][%205 := .value v205][%206 := .value v206]

def productWord4 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v197 : BitVec 128 := (x0.setWidth 128) * 17592186044415#128
  let v198 : BitVec 128 := (x1.setWidth 128) * 4503599627370495#128
  let v199 : BitVec 128 := v198 + v197
  let v200 : BitVec 128 := (x2.setWidth 128) * 4503599278581019#128
  let v201 : BitVec 128 := v199 + v200
  let v202 : BitVec 128 := (x3.setWidth 128) * 1049714374468698#128
  let v203 : BitVec 128 := v201 + v202
  let v204 : BitVec 128 := x4.setWidth 128
  let v205 : BitVec 128 := (v204) * 4302102966953709#128
  let v206 : BitVec 128 := v203 + v205
  v206

theorem product_chunk4 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p85 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p85 16)
    (hp : E.read (%85) = .value p85)
    (h171 : E.read (%171) = .value (x4))
    (h177 : E.read (%177) = .value (x0.setWidth 128))
    (h180 : E.read (%180) = .value (x1.setWidth 128))
    (h186 : E.read (%186) = .value (x2.setWidth 128))
    (h194 : E.read (%194) = .value (x3.setWidth 128))
    (hk24 : E.read (%24) = .value 4302102966953709#128)
    (hk25 : E.read (%25) = .value 1049714374468698#128)
    (hk26 : E.read (%26) = .value 4503599278581019#128)
    (hk27 : E.read (%27) = .value 4503599627370495#128)
    (hk28 : E.read (%28) = .value 17592186044415#128)
    : productBlock4.runBodyFrom E 0 s =
      .value (productEnv4 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p85 (productWord4 x0 x1 x2 x3 x4)}) := by
  let v197 : BitVec 128 := (x0.setWidth 128) * 17592186044415#128
  obtain ⟨h197u, h197s, h197n⟩ := product_constant_flags x0 17592186044415#128 hx0 (by decide)
  let v198 : BitVec 128 := (x1.setWidth 128) * 4503599627370495#128
  obtain ⟨h198u, h198s, h198n⟩ := product_constant_flags x1 4503599627370495#128 hx1 (by decide)
  let v199 : BitVec 128 := v198 + v197
  have h199bound : (v198).toNat + (v197).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, h197n, h198n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h199u, h199s, h199n⟩ := product_add_flags (v198) (v197) h199bound
  dsimp only [v197, v198, v199] at h199u h199s h199n
  let v200 : BitVec 128 := (x2.setWidth 128) * 4503599278581019#128
  obtain ⟨h200u, h200s, h200n⟩ := product_constant_flags x2 4503599278581019#128 hx2 (by decide)
  let v201 : BitVec 128 := v199 + v200
  have h201bound : (v199).toNat + (v200).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, v200, v201, h197n, h198n, h199n, h200n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h201u, h201s, h201n⟩ := product_add_flags (v199) (v200) h201bound
  dsimp only [v197, v198, v199, v200, v201] at h201u h201s h201n
  let v202 : BitVec 128 := (x3.setWidth 128) * 1049714374468698#128
  obtain ⟨h202u, h202s, h202n⟩ := product_constant_flags x3 1049714374468698#128 hx3 (by decide)
  let v203 : BitVec 128 := v201 + v202
  have h203bound : (v201).toNat + (v202).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, v200, v201, v202, v203, h197n, h198n, h199n, h200n, h201n, h202n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h203u, h203s, h203n⟩ := product_add_flags (v201) (v202) h203bound
  dsimp only [v197, v198, v199, v200, v201, v202, v203] at h203u h203s h203n
  let v204 : BitVec 128 := x4.setWidth 128
  have h204nonneg := product_limb_nonneg x4 hx4
  let v205 : BitVec 128 := (v204) * 4302102966953709#128
  obtain ⟨h205u, h205s, h205n⟩ := product_constant_flags x4 4302102966953709#128 hx4 (by decide)
  let v206 : BitVec 128 := v203 + v205
  have h206bound : (v203).toNat + (v205).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, h197n, h198n, h199n, h200n, h201n, h202n, h203n, h205n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h206u, h206s, h206n⟩ := product_add_flags (v203) (v205) h206bound
  dsimp only [v197, v198, v199, v200, v201, v202, v203, v204, v205, v206] at h206u h206s h206n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock4.runBodyFrom E' 0 S =
        .value (productEnv4 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p85 (productWord4 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p85 128 := by rw [hS]; exact hr.fits
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h197u, h197s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h198u, h198s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h199u, h199s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h200u, h200s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h201u, h201s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h202u, h202s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h203u, h203s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h204nonneg]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h205u, h205s]
  step_pure [h171, h177, h180, h186, h194, hk24, hk25, hk26, hk27, hk28, h206u, h206s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word4_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord4 x0 x1 x2 x3 x4).toNat = (((((x1.toNat * 4503599627370495) + (x0.toNat * 17592186044415)) + (x2.toNat * 4503599278581019)) + (x3.toNat * 1049714374468698)) + (x4.toNat * 4302102966953709)) := by
  let v197 : BitVec 128 := (x0.setWidth 128) * 17592186044415#128
  obtain ⟨h197u, h197s, h197n⟩ := product_constant_flags x0 17592186044415#128 hx0 (by decide)
  let v198 : BitVec 128 := (x1.setWidth 128) * 4503599627370495#128
  obtain ⟨h198u, h198s, h198n⟩ := product_constant_flags x1 4503599627370495#128 hx1 (by decide)
  let v199 : BitVec 128 := v198 + v197
  have h199bound : (v198).toNat + (v197).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, h197n, h198n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h199u, h199s, h199n⟩ := product_add_flags (v198) (v197) h199bound
  dsimp only [v197, v198, v199] at h199u h199s h199n
  let v200 : BitVec 128 := (x2.setWidth 128) * 4503599278581019#128
  obtain ⟨h200u, h200s, h200n⟩ := product_constant_flags x2 4503599278581019#128 hx2 (by decide)
  let v201 : BitVec 128 := v199 + v200
  have h201bound : (v199).toNat + (v200).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, v200, v201, h197n, h198n, h199n, h200n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h201u, h201s, h201n⟩ := product_add_flags (v199) (v200) h201bound
  dsimp only [v197, v198, v199, v200, v201] at h201u h201s h201n
  let v202 : BitVec 128 := (x3.setWidth 128) * 1049714374468698#128
  obtain ⟨h202u, h202s, h202n⟩ := product_constant_flags x3 1049714374468698#128 hx3 (by decide)
  let v203 : BitVec 128 := v201 + v202
  have h203bound : (v201).toNat + (v202).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, v200, v201, v202, v203, h197n, h198n, h199n, h200n, h201n, h202n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h203u, h203s, h203n⟩ := product_add_flags (v201) (v202) h203bound
  dsimp only [v197, v198, v199, v200, v201, v202, v203] at h203u h203s h203n
  let v204 : BitVec 128 := x4.setWidth 128
  have h204nonneg := product_limb_nonneg x4 hx4
  let v205 : BitVec 128 := (v204) * 4302102966953709#128
  obtain ⟨h205u, h205s, h205n⟩ := product_constant_flags x4 4302102966953709#128 hx4 (by decide)
  let v206 : BitVec 128 := v203 + v205
  have h206bound : (v203).toNat + (v205).toNat < 2 ^ 127 := by
    simp only [v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, h197n, h198n, h199n, h200n, h201n, h202n, h203n, h205n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h206u, h206s, h206n⟩ := product_add_flags (v203) (v205) h206bound
  dsimp only [v197, v198, v199, v200, v201, v202, v203, v204, v205, v206] at h206u h206s h206n
  change v206.toNat = _
  norm_num [v197, v198, v199, v200, v201, v202, v203, v204, v205, v206, h197n, h198n, h199n, h200n, h201n, h202n, h203n, h205n, h206n]

end Agave.Ed25519.ScalarReduce32.Execution
