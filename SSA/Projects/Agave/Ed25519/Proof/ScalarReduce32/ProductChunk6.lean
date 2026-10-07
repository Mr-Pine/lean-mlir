import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.ProductFlags
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def productBlock6 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 255).take 6}

def productEnv6 (E : Env program.Γ) (x0 x1 x2 x3 x4 : BitVec 64) : Env program.Γ :=
  let v214 : BitVec 128 := (x2.setWidth 128) * 17592186044415#128
  let v215 : BitVec 128 := (x3.setWidth 128) * 4503599627370495#128
  let v216 : BitVec 128 := v215 + v214
  let v217 : BitVec 128 := (x4.setWidth 128) * 4503599278581019#128
  let v218 : BitVec 128 := v216 + v217
  E[%214 := .value v214][%215 := .value v215][%216 := .value v216][%217 := .value v217][%218 := .value v218]

def productWord6 (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 128 :=
  let v214 : BitVec 128 := (x2.setWidth 128) * 17592186044415#128
  let v215 : BitVec 128 := (x3.setWidth 128) * 4503599627370495#128
  let v216 : BitVec 128 := v215 + v214
  let v217 : BitVec 128 := (x4.setWidth 128) * 4503599278581019#128
  let v218 : BitVec 128 := v216 + v217
  v218

theorem product_chunk6 (E : Env program.Γ) (s : GlobalState)
    (x0 x1 x2 x3 x4 : BitVec 64) (p87 : Pointer)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    (hr : SmallRange s.mem p87 16)
    (hp : E.read (%87) = .value p87)
    (h186 : E.read (%186) = .value (x2.setWidth 128))
    (h194 : E.read (%194) = .value (x3.setWidth 128))
    (h204 : E.read (%204) = .value (x4.setWidth 128))
    (hk26 : E.read (%26) = .value 4503599278581019#128)
    (hk27 : E.read (%27) = .value 4503599627370495#128)
    (hk28 : E.read (%28) = .value 17592186044415#128)
    : productBlock6.runBodyFrom E 0 s =
      .value (productEnv6 E x0 x1 x2 x3 x4,
        {s with mem := s.mem.storeAt p87 (productWord6 x0 x1 x2 x3 x4)}) := by
  let v214 : BitVec 128 := (x2.setWidth 128) * 17592186044415#128
  obtain ⟨h214u, h214s, h214n⟩ := product_constant_flags x2 17592186044415#128 hx2 (by decide)
  let v215 : BitVec 128 := (x3.setWidth 128) * 4503599627370495#128
  obtain ⟨h215u, h215s, h215n⟩ := product_constant_flags x3 4503599627370495#128 hx3 (by decide)
  let v216 : BitVec 128 := v215 + v214
  have h216bound : (v215).toNat + (v214).toNat < 2 ^ 127 := by
    simp only [v214, v215, v216, h214n, h215n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h216u, h216s, h216n⟩ := product_add_flags (v215) (v214) h216bound
  dsimp only [v214, v215, v216] at h216u h216s h216n
  let v217 : BitVec 128 := (x4.setWidth 128) * 4503599278581019#128
  obtain ⟨h217u, h217s, h217n⟩ := product_constant_flags x4 4503599278581019#128 hx4 (by decide)
  let v218 : BitVec 128 := v216 + v217
  have h218bound : (v216).toNat + (v217).toNat < 2 ^ 127 := by
    simp only [v214, v215, v216, v217, v218, h214n, h215n, h216n, h217n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h218u, h218s, h218n⟩ := product_add_flags (v216) (v217) h218bound
  dsimp only [v214, v215, v216, v217, v218] at h218u h218s h218n
  suffices ∀ (E' : Env program.Γ), E' = E → ∀ (S : GlobalState), S = s →
      productBlock6.runBodyFrom E' 0 S =
        .value (productEnv6 E x0 x1 x2 x3 x4,
          {s with mem := s.mem.storeAt p87 (productWord6 x0 x1 x2 x3 x4)}) by
    exact this E rfl s rfl
  intro E' hE S hS
  have hf : Fits S.mem p87 128 := by rw [hS]; exact hr.fits
  step_pure [h186, h194, h204, hk26, hk27, hk28, h214u, h214s]
  step_pure [h186, h194, h204, hk26, hk27, hk28, h215u, h215s]
  step_pure [h186, h194, h204, hk26, hk27, hk28, h216u, h216s]
  step_pure [h186, h194, h204, hk26, hk27, hk28, h217u, h217s]
  step_pure [h186, h194, h204, hk26, hk27, hk28, h218u, h218s]
  step_store [hp]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hS]
  subst_vars
  rfl

/-- Exact natural column value established alongside the emitted flags. -/
theorem product_word6_toNat (x0 x1 x2 x3 x4 : BitVec 64)
    (hx0 : x0.toNat < 2 ^ 52)
    (hx1 : x1.toNat < 2 ^ 52)
    (hx2 : x2.toNat < 2 ^ 52)
    (hx3 : x3.toNat < 2 ^ 52)
    (hx4 : x4.toNat < 2 ^ 52)
    : (productWord6 x0 x1 x2 x3 x4).toNat = (((x3.toNat * 4503599627370495) + (x2.toNat * 17592186044415)) + (x4.toNat * 4503599278581019)) := by
  let v214 : BitVec 128 := (x2.setWidth 128) * 17592186044415#128
  obtain ⟨h214u, h214s, h214n⟩ := product_constant_flags x2 17592186044415#128 hx2 (by decide)
  let v215 : BitVec 128 := (x3.setWidth 128) * 4503599627370495#128
  obtain ⟨h215u, h215s, h215n⟩ := product_constant_flags x3 4503599627370495#128 hx3 (by decide)
  let v216 : BitVec 128 := v215 + v214
  have h216bound : (v215).toNat + (v214).toNat < 2 ^ 127 := by
    simp only [v214, v215, v216, h214n, h215n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h216u, h216s, h216n⟩ := product_add_flags (v215) (v214) h216bound
  dsimp only [v214, v215, v216] at h216u h216s h216n
  let v217 : BitVec 128 := (x4.setWidth 128) * 4503599278581019#128
  obtain ⟨h217u, h217s, h217n⟩ := product_constant_flags x4 4503599278581019#128 hx4 (by decide)
  let v218 : BitVec 128 := v216 + v217
  have h218bound : (v216).toNat + (v217).toNat < 2 ^ 127 := by
    simp only [v214, v215, v216, v217, v218, h214n, h215n, h216n, h217n]
    norm_num at hx0 hx1 hx2 hx3 hx4 ⊢
    omega
  obtain ⟨h218u, h218s, h218n⟩ := product_add_flags (v216) (v217) h218bound
  dsimp only [v214, v215, v216, v217, v218] at h218u h218s h218n
  change v218.toNat = _
  norm_num [v214, v215, v216, v217, v218, h214n, h215n, h216n, h217n, h218n]

end Agave.Ed25519.ScalarReduce32.Execution
