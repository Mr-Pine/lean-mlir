import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock2 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 301).take 5}

def carryGapEnv2 (E : Env program.Γ) (d1 d2 : BitVec 64) (u196 u251 : BitVec 128) : Env program.Γ :=
  let v252 : BitVec 128 := (d1.setWidth 128) * 1367801#128
  let v253 : BitVec 128 := (d2.setWidth 128) * 3916664325105025#128
  let v254 : BitVec 128 := v252 + u196
  let v255 : BitVec 128 := v254 + v253
  let v256 : BitVec 128 := v255 + u251
  E[%252 := .value v252][%253 := .value v253][%254 := .value v254][%255 := .value v255][%256 := .value v256]

theorem carry_gap2 (E : Env program.Γ) (s : GlobalState) (d1 d2 : BitVec 64) (u196 u251 : BitVec 128)
    (hd236 : d1.toNat < 2 ^ 52)
    (h236 : E.read (%236) = .value (d1.setWidth 128))
    (hd248 : d2.toNat < 2 ^ 52)
    (h248 : E.read (%248) = .value (d2.setWidth 128))
    (hu196 : u196.toNat < 2 ^ 110)
    (h196 : E.read (%196) = .value u196)
    (hu251 : u251.toNat < 2 ^ 110)
    (h251 : E.read (%251) = .value u251)
    (hk32 : E.read (%32) = .value 3916664325105025#128)
    (hk33 : E.read (%33) = .value 1367801#128)
    : carryGapBlock2.runBodyFrom E 0 s = .value (carryGapEnv2 E d1 d2 u196 u251, s) := by
  let v252 : BitVec 128 := (d1.setWidth 128) * 1367801#128
  obtain ⟨h252u, h252s, h252n⟩ := product_constant_flags d1 1367801#128 hd236 (by decide)
  let v253 : BitVec 128 := (d2.setWidth 128) * 3916664325105025#128
  obtain ⟨h253u, h253s, h253n⟩ := product_constant_flags d2 3916664325105025#128 hd248 (by decide)
  let v254 : BitVec 128 := v252 + u196
  have h254bound : (v252).toNat + (u196).toNat < 2 ^ 120 := by
    simp only [v252, v253, v254, h252n, h253n]
    norm_num at hd236 hd248 hu196 hu251 ⊢
    omega
  obtain ⟨h254u, h254s, h254n⟩ := product_add_flags (v252) (u196)
    (h254bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v252, v253, v254] at h254u h254s h254n
  let v255 : BitVec 128 := v254 + v253
  have h255bound : (v254).toNat + (v253).toNat < 2 ^ 120 := by
    simp only [v252, v253, v254, v255, h252n, h253n, h254n]
    norm_num at hd236 hd248 hu196 hu251 ⊢
    omega
  obtain ⟨h255u, h255s, h255n⟩ := product_add_flags (v254) (v253)
    (h255bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v252, v253, v254, v255] at h255u h255s h255n
  let v256 : BitVec 128 := v255 + u251
  have h256bound : (v255).toNat + (u251).toNat < 2 ^ 120 := by
    simp only [v252, v253, v254, v255, v256, h252n, h253n, h254n, h255n]
    norm_num at hd236 hd248 hu196 hu251 ⊢
    omega
  obtain ⟨h256u, h256s, h256n⟩ := product_add_flags (v255) (u251)
    (h256bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v252, v253, v254, v255, v256] at h256u h256s h256n
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock2.runBodyFrom E' 0 s = .value (carryGapEnv2 E d1 d2 u196 u251, s) by
    exact this E rfl
  intro E' hE
  step_pure [h196, h236, h248, h251, hk32, hk33, h252u, h252s]
  step_pure [h196, h236, h248, h251, hk32, hk33, h253u, h253s]
  step_pure [h196, h236, h248, h251, hk32, hk33, h254u, h254s]
  step_pure [h196, h236, h248, h251, hk32, hk33, h255u, h255s]
  step_pure [h196, h236, h248, h251, hk32, hk33, h256u, h256s]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
