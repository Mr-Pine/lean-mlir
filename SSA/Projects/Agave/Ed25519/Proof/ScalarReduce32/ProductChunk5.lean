import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock5 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 247).take 8}

def productEnv5 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v207 : BitVec 128 := (x1.setWidth 128) * 17592186044415#128
  let v208 : BitVec 128 := (x2.setWidth 128) * 4503599627370495#128
  let v209 : BitVec 128 := v208 + v207
  let v210 : BitVec 128 := (x3.setWidth 128) * 4503599278581019#128
  let v211 : BitVec 128 := v209 + v210
  let v212 : BitVec 128 := (x4.setWidth 128) * 1049714374468698#128
  let v213 : BitVec 128 := v211 + v212
  E[%207 := .value v207][%208 := .value v208][%209 := .value v209][%210 := .value v210][%211 := .value v211][%212 := .value v212][%213 := .value v213]

def productWord5 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v207 : BitVec 128 := (x1.setWidth 128) * 17592186044415#128
  let v208 : BitVec 128 := (x2.setWidth 128) * 4503599627370495#128
  let v209 : BitVec 128 := v208 + v207
  let v210 : BitVec 128 := (x3.setWidth 128) * 4503599278581019#128
  let v211 : BitVec 128 := v209 + v210
  let v212 : BitVec 128 := (x4.setWidth 128) * 1049714374468698#128
  let v213 : BitVec 128 := v211 + v212
  v213

theorem product_chunk5 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p86 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p86 16)
    (hp : E.read (%86) = .value p86)
    (h180 : E.read (%180) = .value (x1.setWidth 128))
    (h186 : E.read (%186) = .value (x2.setWidth 128))
    (h194 : E.read (%194) = .value (x3.setWidth 128))
    (h204 : E.read (%204) = .value (x4.setWidth 128))
    (hk25 : E.read (%25) = .value 1049714374468698#128)
    (hk26 : E.read (%26) = .value 4503599278581019#128)
    (hk27 : E.read (%27) = .value 4503599627370495#128)
    (hk28 : E.read (%28) = .value 17592186044415#128)
    : productBlock5.runBodyFrom E 0 s =
      .value (productEnv5 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p86 (productWord5 x0 x1 x2 x3 x4)}) := by
  let v207 : BitVec 128 := (x1.setWidth 128) * 17592186044415#128
  obtain ⟨h207u, h207s, h207n⟩ := product_constant_flags x1 17592186044415#128 hx1 (by decide)
  let v208 : BitVec 128 := (x2.setWidth 128) * 4503599627370495#128
  obtain ⟨h208u, h208s, h208n⟩ := product_constant_flags x2 4503599627370495#128 hx2 (by decide)
  let v209 : BitVec 128 := v208 + v207
  have h209bound : (v208).toNat + (v207).toNat < 2 ^ 127 := by
    simp only [v207, v208, v209, h207n, h208n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h209u, h209s, h209n⟩ := product_add_flags (v208) (v207) h209bound
  dsimp only [v207, v208, v209] at h209u h209s h209n
  let v210 : BitVec 128 := (x3.setWidth 128) * 4503599278581019#128
  obtain ⟨h210u, h210s, h210n⟩ := product_constant_flags x3 4503599278581019#128 hx3 (by decide)
  let v211 : BitVec 128 := v209 + v210
  have h211bound : (v209).toNat + (v210).toNat < 2 ^ 127 := by
    simp only [v207, v208, v209, v210, v211, h207n, h208n, h209n, h210n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h211u, h211s, h211n⟩ := product_add_flags (v209) (v210) h211bound
  dsimp only [v207, v208, v209, v210, v211] at h211u h211s h211n
  let v212 : BitVec 128 := (x4.setWidth 128) * 1049714374468698#128
  obtain ⟨h212u, h212s, h212n⟩ := product_constant_flags x4 1049714374468698#128 hx4 (by decide)
  let v213 : BitVec 128 := v211 + v212
  have h213bound : (v211).toNat + (v212).toNat < 2 ^ 127 := by
    simp only [v207, v208, v209, v210, v211, v212, v213, h207n, h208n, h209n, h210n, h211n, h212n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h213u, h213s, h213n⟩ := product_add_flags (v211) (v212) h213bound
  dsimp only [v207, v208, v209, v210, v211, v212, v213] at h213u h213s h213n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock5.runBodyFrom E' 0 S =
        .value (productEnv5 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p86 (productWord5 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p86 128 := by rw [hS]; exact hr.fits
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h207u, h207s]
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h208u, h208s]
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h209u, h209s]
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h210u, h210s]
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h211u, h211s]
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h212u, h212s]
  step_pure [h180, h186, h194, h204, hk25, hk26, hk27, hk28, h213u, h213s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word5_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord5 x0 x1 x2 x3 x4).toNat = ((((x2.toNat * 4503599627370495) + (x1.toNat * 17592186044415)) + (x3.toNat * 4503599278581019)) + (x4.toNat * 1049714374468698)) := by
  let v207 : BitVec 128 := (x1.setWidth 128) * 17592186044415#128
  obtain ⟨h207u, h207s, h207n⟩ := product_constant_flags x1 17592186044415#128 hx1 (by decide)
  let v208 : BitVec 128 := (x2.setWidth 128) * 4503599627370495#128
  obtain ⟨h208u, h208s, h208n⟩ := product_constant_flags x2 4503599627370495#128 hx2 (by decide)
  let v209 : BitVec 128 := v208 + v207
  have h209bound : (v208).toNat + (v207).toNat < 2 ^ 127 := by
    simp only [v207, v208, v209, h207n, h208n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h209u, h209s, h209n⟩ := product_add_flags (v208) (v207) h209bound
  dsimp only [v207, v208, v209] at h209u h209s h209n
  let v210 : BitVec 128 := (x3.setWidth 128) * 4503599278581019#128
  obtain ⟨h210u, h210s, h210n⟩ := product_constant_flags x3 4503599278581019#128 hx3 (by decide)
  let v211 : BitVec 128 := v209 + v210
  have h211bound : (v209).toNat + (v210).toNat < 2 ^ 127 := by
    simp only [v207, v208, v209, v210, v211, h207n, h208n, h209n, h210n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h211u, h211s, h211n⟩ := product_add_flags (v209) (v210) h211bound
  dsimp only [v207, v208, v209, v210, v211] at h211u h211s h211n
  let v212 : BitVec 128 := (x4.setWidth 128) * 1049714374468698#128
  obtain ⟨h212u, h212s, h212n⟩ := product_constant_flags x4 1049714374468698#128 hx4 (by decide)
  let v213 : BitVec 128 := v211 + v212
  have h213bound : (v211).toNat + (v212).toNat < 2 ^ 127 := by
    simp only [v207, v208, v209, v210, v211, v212, v213, h207n, h208n, h209n, h210n, h211n, h212n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h213u, h213s, h213n⟩ := product_add_flags (v211) (v212) h213bound
  dsimp only [v207, v208, v209, v210, v211, v212, v213] at h213u h213s h213n
  change v213.toNat = _
  norm_num [v207, v208, v209, v210, v211, v212, v213, h207n, h208n, h209n, h210n, h211n, h212n, h213n]

end Agave.Ed25519.ScalarReduce32.Execution
