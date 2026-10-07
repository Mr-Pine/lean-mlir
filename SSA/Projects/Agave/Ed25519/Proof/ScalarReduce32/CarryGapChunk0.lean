import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock0 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 279).take 3}

def carryGapEnv0 (E : Env program.Γ) (d0 : BitVec 64) (u182 u229 : BitVec 128) : Env program.Γ :=
  let v230 : BitVec 128 := (d0.setWidth 128) * 3916664325105025#128
  let v231 : BitVec 128 := v230 + u182
  let v232 : BitVec 128 := v231 + u229
  E[%230 := .value v230][%231 := .value v231][%232 := .value v232]

theorem carry_gap0 (E : Env program.Γ) (s : GlobalState) (d0 : BitVec 64) (u182 u229 : BitVec 128)
    (hd226 : d0.toNat < 2 ^ 52)
    (h226 : E.read (%226) = .value (d0.setWidth 128))
    (hu182 : u182.toNat < 2 ^ 110)
    (h182 : E.read (%182) = .value u182)
    (hu229 : u229.toNat < 2 ^ 110)
    (h229 : E.read (%229) = .value u229)
    (hk32 : E.read (%32) = .value 3916664325105025#128)
    : carryGapBlock0.runBodyFrom E 0 s = .value (carryGapEnv0 E d0 u182 u229, s) := by
  let v230 : BitVec 128 := (d0.setWidth 128) * 3916664325105025#128
  obtain ⟨h230u, h230s, h230n⟩ := product_constant_flags d0 3916664325105025#128 hd226 (by decide)
  let v231 : BitVec 128 := v230 + u182
  have h231bound : (v230).toNat + (u182).toNat < 2 ^ 120 := by
    simp only [v230, v231, h230n]
    norm_num at hd226 hu182 hu229 ⊢
    omega
  obtain ⟨h231u, h231s, h231n⟩ := product_add_flags (v230) (u182)
    (h231bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v230, v231] at h231u h231s h231n
  let v232 : BitVec 128 := v231 + u229
  have h232bound : (v231).toNat + (u229).toNat < 2 ^ 120 := by
    simp only [v230, v231, v232, h230n, h231n]
    norm_num at hd226 hu182 hu229 ⊢
    omega
  obtain ⟨h232u, h232s, h232n⟩ := product_add_flags (v231) (u229)
    (h232bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v230, v231, v232] at h232u h232s h232n
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock0.runBodyFrom E' 0 s = .value (carryGapEnv0 E d0 u182 u229, s) by
    exact this E rfl
  intro E' hE
  step_pure [h182, h226, h229, hk32, h230u, h230s]
  step_pure [h182, h226, h229, hk32, h231u, h231s]
  step_pure [h182, h226, h229, hk32, h232u, h232s]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
