import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock2 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 220).take 7}

def productEnv2 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v183 : BitVec 128 := (x0.setWidth 128) * 4503599278581019#128
  let v184 : BitVec 128 := (x1.setWidth 128) * 1049714374468698#128
  let v185 : BitVec 128 := v184 + v183
  let v186 : BitVec 128 := x2.setWidth 128
  let v187 : BitVec 128 := (v186) * 4302102966953709#128
  let v188 : BitVec 128 := v185 + v187
  E[%183 := .value v183][%184 := .value v184][%185 := .value v185][%186 := .value v186][%187 := .value v187][%188 := .value v188]

def productWord2 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v183 : BitVec 128 := (x0.setWidth 128) * 4503599278581019#128
  let v184 : BitVec 128 := (x1.setWidth 128) * 1049714374468698#128
  let v185 : BitVec 128 := v184 + v183
  let v186 : BitVec 128 := x2.setWidth 128
  let v187 : BitVec 128 := (v186) * 4302102966953709#128
  let v188 : BitVec 128 := v185 + v187
  v188

theorem product_chunk2 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p83 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p83 16)
    (hp : E.read (%83) = .value p83)
    (h174 : E.read (%174) = .value (x2))
    (h177 : E.read (%177) = .value (x0.setWidth 128))
    (h180 : E.read (%180) = .value (x1.setWidth 128))
    (hk24 : E.read (%24) = .value 4302102966953709#128)
    (hk25 : E.read (%25) = .value 1049714374468698#128)
    (hk26 : E.read (%26) = .value 4503599278581019#128)
    : productBlock2.runBodyFrom E 0 s =
      .value (productEnv2 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p83 (productWord2 x0 x1 x2 x3 x4)}) := by
  let v183 : BitVec 128 := (x0.setWidth 128) * 4503599278581019#128
  obtain ⟨h183u, h183s, h183n⟩ := product_constant_flags x0 4503599278581019#128 hx0 (by decide)
  let v184 : BitVec 128 := (x1.setWidth 128) * 1049714374468698#128
  obtain ⟨h184u, h184s, h184n⟩ := product_constant_flags x1 1049714374468698#128 hx1 (by decide)
  let v185 : BitVec 128 := v184 + v183
  have h185bound : (v184).toNat + (v183).toNat < 2 ^ 127 := by
    simp only [v183, v184, v185, h183n, h184n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h185u, h185s, h185n⟩ := product_add_flags (v184) (v183) h185bound
  dsimp only [v183, v184, v185] at h185u h185s h185n
  let v186 : BitVec 128 := x2.setWidth 128
  have h186nonneg := product_limb_nonneg x2 hx2
  let v187 : BitVec 128 := (v186) * 4302102966953709#128
  obtain ⟨h187u, h187s, h187n⟩ := product_constant_flags x2 4302102966953709#128 hx2 (by decide)
  let v188 : BitVec 128 := v185 + v187
  have h188bound : (v185).toNat + (v187).toNat < 2 ^ 127 := by
    simp only [v183, v184, v185, v186, v187, v188, h183n, h184n, h185n, h187n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h188u, h188s, h188n⟩ := product_add_flags (v185) (v187) h188bound
  dsimp only [v183, v184, v185, v186, v187, v188] at h188u h188s h188n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock2.runBodyFrom E' 0 S =
        .value (productEnv2 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p83 (productWord2 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p83 128 := by rw [hS]; exact hr.fits
  step_pure [h174, h177, h180, hk24, hk25, hk26, h183u, h183s]
  step_pure [h174, h177, h180, hk24, hk25, hk26, h184u, h184s]
  step_pure [h174, h177, h180, hk24, hk25, hk26, h185u, h185s]
  step_pure [h174, h177, h180, hk24, hk25, hk26, h186nonneg]
  step_pure [h174, h177, h180, hk24, hk25, hk26, h187u, h187s]
  step_pure [h174, h177, h180, hk24, hk25, hk26, h188u, h188s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word2_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord2 x0 x1 x2 x3 x4).toNat = (((x1.toNat * 1049714374468698) + (x0.toNat * 4503599278581019)) + (x2.toNat * 4302102966953709)) := by
  let v183 : BitVec 128 := (x0.setWidth 128) * 4503599278581019#128
  obtain ⟨h183u, h183s, h183n⟩ := product_constant_flags x0 4503599278581019#128 hx0 (by decide)
  let v184 : BitVec 128 := (x1.setWidth 128) * 1049714374468698#128
  obtain ⟨h184u, h184s, h184n⟩ := product_constant_flags x1 1049714374468698#128 hx1 (by decide)
  let v185 : BitVec 128 := v184 + v183
  have h185bound : (v184).toNat + (v183).toNat < 2 ^ 127 := by
    simp only [v183, v184, v185, h183n, h184n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h185u, h185s, h185n⟩ := product_add_flags (v184) (v183) h185bound
  dsimp only [v183, v184, v185] at h185u h185s h185n
  let v186 : BitVec 128 := x2.setWidth 128
  have h186nonneg := product_limb_nonneg x2 hx2
  let v187 : BitVec 128 := (v186) * 4302102966953709#128
  obtain ⟨h187u, h187s, h187n⟩ := product_constant_flags x2 4302102966953709#128 hx2 (by decide)
  let v188 : BitVec 128 := v185 + v187
  have h188bound : (v185).toNat + (v187).toNat < 2 ^ 127 := by
    simp only [v183, v184, v185, v186, v187, v188, h183n, h184n, h185n, h187n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h188u, h188s, h188n⟩ := product_add_flags (v185) (v187) h188bound
  dsimp only [v183, v184, v185, v186, v187, v188] at h188u h188s h188n
  change v188.toNat = _
  norm_num [v183, v184, v185, v186, v187, v188, h183n, h184n, h185n, h187n, h188n]

end Agave.Ed25519.ScalarReduce32.Execution
