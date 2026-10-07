import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock3 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 227).take 9}

def productEnv3 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v189 : BitVec 128 := (x0.setWidth 128) * 4503599627370495#128
  let v190 : BitVec 128 := (x1.setWidth 128) * 4503599278581019#128
  let v191 : BitVec 128 := v190 + v189
  let v192 : BitVec 128 := (x2.setWidth 128) * 1049714374468698#128
  let v193 : BitVec 128 := v191 + v192
  let v194 : BitVec 128 := x3.setWidth 128
  let v195 : BitVec 128 := (v194) * 4302102966953709#128
  let v196 : BitVec 128 := v193 + v195
  E[%189 := .value v189][%190 := .value v190][%191 := .value v191][%192 := .value v192][%193 := .value v193][%194 := .value v194][%195 := .value v195][%196 := .value v196]

def productWord3 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v189 : BitVec 128 := (x0.setWidth 128) * 4503599627370495#128
  let v190 : BitVec 128 := (x1.setWidth 128) * 4503599278581019#128
  let v191 : BitVec 128 := v190 + v189
  let v192 : BitVec 128 := (x2.setWidth 128) * 1049714374468698#128
  let v193 : BitVec 128 := v191 + v192
  let v194 : BitVec 128 := x3.setWidth 128
  let v195 : BitVec 128 := (v194) * 4302102966953709#128
  let v196 : BitVec 128 := v193 + v195
  v196

theorem product_chunk3 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p84 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p84 16)
    (hp : E.read (%84) = .value p84)
    (h172 : E.read (%172) = .value (x3))
    (h177 : E.read (%177) = .value (x0.setWidth 128))
    (h180 : E.read (%180) = .value (x1.setWidth 128))
    (h186 : E.read (%186) = .value (x2.setWidth 128))
    (hk24 : E.read (%24) = .value 4302102966953709#128)
    (hk25 : E.read (%25) = .value 1049714374468698#128)
    (hk26 : E.read (%26) = .value 4503599278581019#128)
    (hk27 : E.read (%27) = .value 4503599627370495#128)
    : productBlock3.runBodyFrom E 0 s =
      .value (productEnv3 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p84 (productWord3 x0 x1 x2 x3 x4)}) := by
  let v189 : BitVec 128 := (x0.setWidth 128) * 4503599627370495#128
  obtain ⟨h189u, h189s, h189n⟩ := product_constant_flags x0 4503599627370495#128 hx0 (by decide)
  let v190 : BitVec 128 := (x1.setWidth 128) * 4503599278581019#128
  obtain ⟨h190u, h190s, h190n⟩ := product_constant_flags x1 4503599278581019#128 hx1 (by decide)
  let v191 : BitVec 128 := v190 + v189
  have h191bound : (v190).toNat + (v189).toNat < 2 ^ 127 := by
    simp only [v189, v190, v191, h189n, h190n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h191u, h191s, h191n⟩ := product_add_flags (v190) (v189) h191bound
  dsimp only [v189, v190, v191] at h191u h191s h191n
  let v192 : BitVec 128 := (x2.setWidth 128) * 1049714374468698#128
  obtain ⟨h192u, h192s, h192n⟩ := product_constant_flags x2 1049714374468698#128 hx2 (by decide)
  let v193 : BitVec 128 := v191 + v192
  have h193bound : (v191).toNat + (v192).toNat < 2 ^ 127 := by
    simp only [v189, v190, v191, v192, v193, h189n, h190n, h191n, h192n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h193u, h193s, h193n⟩ := product_add_flags (v191) (v192) h193bound
  dsimp only [v189, v190, v191, v192, v193] at h193u h193s h193n
  let v194 : BitVec 128 := x3.setWidth 128
  have h194nonneg := product_limb_nonneg x3 hx3
  let v195 : BitVec 128 := (v194) * 4302102966953709#128
  obtain ⟨h195u, h195s, h195n⟩ := product_constant_flags x3 4302102966953709#128 hx3 (by decide)
  let v196 : BitVec 128 := v193 + v195
  have h196bound : (v193).toNat + (v195).toNat < 2 ^ 127 := by
    simp only [v189, v190, v191, v192, v193, v194, v195, v196, h189n, h190n, h191n, h192n, h193n, h195n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h196u, h196s, h196n⟩ := product_add_flags (v193) (v195) h196bound
  dsimp only [v189, v190, v191, v192, v193, v194, v195, v196] at h196u h196s h196n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock3.runBodyFrom E' 0 S =
        .value (productEnv3 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p84 (productWord3 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p84 128 := by rw [hS]; exact hr.fits
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h189u, h189s]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h190u, h190s]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h191u, h191s]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h192u, h192s]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h193u, h193s]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h194nonneg]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h195u, h195s]
  step_pure [h172, h177, h180, h186, hk24, hk25, hk26, hk27, h196u, h196s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word3_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord3 x0 x1 x2 x3 x4).toNat = ((((x1.toNat * 4503599278581019) + (x0.toNat * 4503599627370495)) + (x2.toNat * 1049714374468698)) + (x3.toNat * 4302102966953709)) := by
  let v189 : BitVec 128 := (x0.setWidth 128) * 4503599627370495#128
  obtain ⟨h189u, h189s, h189n⟩ := product_constant_flags x0 4503599627370495#128 hx0 (by decide)
  let v190 : BitVec 128 := (x1.setWidth 128) * 4503599278581019#128
  obtain ⟨h190u, h190s, h190n⟩ := product_constant_flags x1 4503599278581019#128 hx1 (by decide)
  let v191 : BitVec 128 := v190 + v189
  have h191bound : (v190).toNat + (v189).toNat < 2 ^ 127 := by
    simp only [v189, v190, v191, h189n, h190n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h191u, h191s, h191n⟩ := product_add_flags (v190) (v189) h191bound
  dsimp only [v189, v190, v191] at h191u h191s h191n
  let v192 : BitVec 128 := (x2.setWidth 128) * 1049714374468698#128
  obtain ⟨h192u, h192s, h192n⟩ := product_constant_flags x2 1049714374468698#128 hx2 (by decide)
  let v193 : BitVec 128 := v191 + v192
  have h193bound : (v191).toNat + (v192).toNat < 2 ^ 127 := by
    simp only [v189, v190, v191, v192, v193, h189n, h190n, h191n, h192n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h193u, h193s, h193n⟩ := product_add_flags (v191) (v192) h193bound
  dsimp only [v189, v190, v191, v192, v193] at h193u h193s h193n
  let v194 : BitVec 128 := x3.setWidth 128
  have h194nonneg := product_limb_nonneg x3 hx3
  let v195 : BitVec 128 := (v194) * 4302102966953709#128
  obtain ⟨h195u, h195s, h195n⟩ := product_constant_flags x3 4302102966953709#128 hx3 (by decide)
  let v196 : BitVec 128 := v193 + v195
  have h196bound : (v193).toNat + (v195).toNat < 2 ^ 127 := by
    simp only [v189, v190, v191, v192, v193, v194, v195, v196, h189n, h190n, h191n, h192n, h193n, h195n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h196u, h196s, h196n⟩ := product_add_flags (v193) (v195) h196bound
  dsimp only [v189, v190, v191, v192, v193, v194, v195, v196] at h196u h196s h196n
  change v196.toNat = _
  norm_num [v189, v190, v191, v192, v193, v194, v195, v196, h189n, h190n, h191n, h192n, h193n, h195n, h196n]

end Agave.Ed25519.ScalarReduce32.Execution
