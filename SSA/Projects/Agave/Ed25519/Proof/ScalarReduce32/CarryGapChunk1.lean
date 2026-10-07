import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock1 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 289).take 5}

def carryGapEnv1 (E : Env program.Γ) (d0 d1 : BitVec 64) (u188 u239 : BitVec 128) : Env program.Γ :=
  let v240 : BitVec 128 := (d0.setWidth 128) * 1367801#128
  let v241 : BitVec 128 := (d1.setWidth 128) * 3916664325105025#128
  let v242 : BitVec 128 := u188 + v240
  let v243 : BitVec 128 := v242 + v241
  let v244 : BitVec 128 := v243 + u239
  E[%240 := .value v240][%241 := .value v241][%242 := .value v242][%243 := .value v243][%244 := .value v244]

theorem carry_gap1 (E : Env program.Γ) (s : GlobalState) (d0 d1 : BitVec 64) (u188 u239 : BitVec 128)
    (hd226 : d0.toNat < 2 ^ 52)
    (h226 : E.read (%226) = .value (d0.setWidth 128))
    (hd236 : d1.toNat < 2 ^ 52)
    (h236 : E.read (%236) = .value (d1.setWidth 128))
    (hu188 : u188.toNat < 2 ^ 110)
    (h188 : E.read (%188) = .value u188)
    (hu239 : u239.toNat < 2 ^ 110)
    (h239 : E.read (%239) = .value u239)
    (hk32 : E.read (%32) = .value 3916664325105025#128)
    (hk33 : E.read (%33) = .value 1367801#128)
    : carryGapBlock1.runBodyFrom E 0 s = .value (carryGapEnv1 E d0 d1 u188 u239, s) := by
  let v240 : BitVec 128 := (d0.setWidth 128) * 1367801#128
  obtain ⟨h240u, h240s, h240n⟩ := product_constant_flags d0 1367801#128 hd226 (by decide)
  let v241 : BitVec 128 := (d1.setWidth 128) * 3916664325105025#128
  obtain ⟨h241u, h241s, h241n⟩ := product_constant_flags d1 3916664325105025#128 hd236 (by decide)
  let v242 : BitVec 128 := u188 + v240
  have h242bound : (u188).toNat + (v240).toNat < 2 ^ 120 := by
    simp only [v240, v241, v242, h240n, h241n]
    norm_num at hd226 hd236 hu188 hu239 ⊢
    omega
  obtain ⟨h242u, h242s, h242n⟩ := product_add_flags (u188) (v240)
    (h242bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v240, v241, v242] at h242u h242s h242n
  let v243 : BitVec 128 := v242 + v241
  have h243bound : (v242).toNat + (v241).toNat < 2 ^ 120 := by
    simp only [v240, v241, v242, v243, h240n, h241n, h242n]
    norm_num at hd226 hd236 hu188 hu239 ⊢
    omega
  obtain ⟨h243u, h243s, h243n⟩ := product_add_flags (v242) (v241)
    (h243bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v240, v241, v242, v243] at h243u h243s h243n
  let v244 : BitVec 128 := v243 + u239
  have h244bound : (v243).toNat + (u239).toNat < 2 ^ 120 := by
    simp only [v240, v241, v242, v243, v244, h240n, h241n, h242n, h243n]
    norm_num at hd226 hd236 hu188 hu239 ⊢
    omega
  obtain ⟨h244u, h244s, h244n⟩ := product_add_flags (v243) (u239)
    (h244bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v240, v241, v242, v243, v244] at h244u h244s h244n
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock1.runBodyFrom E' 0 s = .value (carryGapEnv1 E d0 d1 u188 u239, s) by
    exact this E rfl
  intro E' hE
  step_pure [h188, h226, h236, h239, hk32, hk33, h240u, h240s]
  step_pure [h188, h226, h236, h239, hk32, hk33, h241u, h241s]
  step_pure [h188, h226, h236, h239, hk32, hk33, h242u, h242s]
  step_pure [h188, h226, h236, h239, hk32, hk33, h243u, h243s]
  step_pure [h188, h226, h236, h239, hk32, hk33, h244u, h244s]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
