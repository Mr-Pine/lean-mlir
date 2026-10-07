import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock1 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 215).take 5}

def productEnv1 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v179 : BitVec 128 := (x0.setWidth 128) * 1049714374468698#128
  let v180 : BitVec 128 := x1.setWidth 128
  let v181 : BitVec 128 := (v180) * 4302102966953709#128
  let v182 : BitVec 128 := v181 + v179
  E[%179 := .value v179][%180 := .value v180][%181 := .value v181][%182 := .value v182]

def productWord1 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v179 : BitVec 128 := (x0.setWidth 128) * 1049714374468698#128
  let v180 : BitVec 128 := x1.setWidth 128
  let v181 : BitVec 128 := (v180) * 4302102966953709#128
  let v182 : BitVec 128 := v181 + v179
  v182

theorem product_chunk1 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p82 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p82 16)
    (hp : E.read (%82) = .value p82)
    (h175 : E.read (%175) = .value (x1))
    (h177 : E.read (%177) = .value (x0.setWidth 128))
    (hk24 : E.read (%24) = .value 4302102966953709#128)
    (hk25 : E.read (%25) = .value 1049714374468698#128)
    : productBlock1.runBodyFrom E 0 s =
      .value (productEnv1 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p82 (productWord1 x0 x1 x2 x3 x4)}) := by
  let v179 : BitVec 128 := (x0.setWidth 128) * 1049714374468698#128
  obtain ⟨h179u, h179s, h179n⟩ := product_constant_flags x0 1049714374468698#128 hx0 (by decide)
  let v180 : BitVec 128 := x1.setWidth 128
  have h180nonneg := product_limb_nonneg x1 hx1
  let v181 : BitVec 128 := (v180) * 4302102966953709#128
  obtain ⟨h181u, h181s, h181n⟩ := product_constant_flags x1 4302102966953709#128 hx1 (by decide)
  let v182 : BitVec 128 := v181 + v179
  have h182bound : (v181).toNat + (v179).toNat < 2 ^ 127 := by
    simp only [v179, v180, v181, v182, h179n, h181n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h182u, h182s, h182n⟩ := product_add_flags (v181) (v179) h182bound
  dsimp only [v179, v180, v181, v182] at h182u h182s h182n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock1.runBodyFrom E' 0 S =
        .value (productEnv1 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p82 (productWord1 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p82 128 := by rw [hS]; exact hr.fits
  step_pure [h175, h177, hk24, hk25, h179u, h179s]
  step_pure [h175, h177, hk24, hk25, h180nonneg]
  step_pure [h175, h177, hk24, hk25, h181u, h181s]
  step_pure [h175, h177, hk24, hk25, h182u, h182s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word1_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord1 x0 x1 x2 x3 x4).toNat = ((x1.toNat * 4302102966953709) + (x0.toNat * 1049714374468698)) := by
  let v179 : BitVec 128 := (x0.setWidth 128) * 1049714374468698#128
  obtain ⟨h179u, h179s, h179n⟩ := product_constant_flags x0 1049714374468698#128 hx0 (by decide)
  let v180 : BitVec 128 := x1.setWidth 128
  have h180nonneg := product_limb_nonneg x1 hx1
  let v181 : BitVec 128 := (v180) * 4302102966953709#128
  obtain ⟨h181u, h181s, h181n⟩ := product_constant_flags x1 4302102966953709#128 hx1 (by decide)
  let v182 : BitVec 128 := v181 + v179
  have h182bound : (v181).toNat + (v179).toNat < 2 ^ 127 := by
    simp only [v179, v180, v181, v182, h179n, h181n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h182u, h182s, h182n⟩ := product_add_flags (v181) (v179) h182bound
  dsimp only [v179, v180, v181, v182] at h182u h182s h182n
  change v182.toNat = _
  norm_num [v179, v180, v181, v182, h179n, h181n, h182n]

end Agave.Ed25519.ScalarReduce32.Execution
