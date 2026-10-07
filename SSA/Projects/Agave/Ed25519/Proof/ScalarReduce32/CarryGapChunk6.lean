import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock6 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 345).take 6}

def carryGapEnv6 (E : Env program.Γ) (d3 : BitVec 64) (u221 u295 : BitVec 128) : Env program.Γ :=
  let v296 : BitVec 128 := (d3.setWidth 128) <<< 44
  let v297 : BitVec 128 := v296 + u221
  let v298 : BitVec 128 := v297 + u295
  let v299 : BitVec 64 := (v298).setWidth 64
  let v300 : BitVec 64 := v299 &&& 4503599627370495#64
  let v301 : BitVec 128 := v298 >>> 52
  E[%296 := .value v296][%297 := .value v297][%298 := .value v298][%299 := .value v299][%300 := .value v300][%301 := .value v301]

theorem carry_gap6 (E : Env program.Γ) (s : GlobalState) (d3 : BitVec 64) (u221 u295 : BitVec 128)
    (hd260 : d3.toNat < 2 ^ 52)
    (h260 : E.read (%260) = .value (d3.setWidth 128))
    (hu221 : u221.toNat < 2 ^ 110)
    (h221 : E.read (%221) = .value u221)
    (hu295 : u295.toNat < 2 ^ 110)
    (h295 : E.read (%295) = .value u295)
    (hk23 : E.read (%23) = .value 4503599627370495#64)
    (hk31 : E.read (%31) = .value 52#128)
    (hk34 : E.read (%34) = .value 44#128)
    : carryGapBlock6.runBodyFrom E 0 s = .value (carryGapEnv6 E d3 u221 u295, s) := by
  let v296 : BitVec 128 := (d3.setWidth 128) <<< 44
  obtain ⟨h296u, h296s, h296n⟩ := carry_shift44_flags d3 hd260
  let v297 : BitVec 128 := v296 + u221
  have h297bound : (v296).toNat + (u221).toNat < 2 ^ 120 := by
    simp only [v296, v297, h296n]
    norm_num at hd260 hu221 hu295 ⊢
    omega
  obtain ⟨h297u, h297s, h297n⟩ := product_add_flags (v296) (u221)
    (h297bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v296, v297] at h297u h297s h297n
  let v298 : BitVec 128 := v297 + u295
  have h298bound : (v297).toNat + (u295).toNat < 2 ^ 120 := by
    simp only [v296, v297, v298, h296n, h297n]
    norm_num at hd260 hu221 hu295 ⊢
    omega
  obtain ⟨h298u, h298s, h298n⟩ := product_add_flags (v297) (u295)
    (h298bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v296, v297, v298] at h298u h298s h298n
  let v299 : BitVec 64 := (v298).setWidth 64
  let v300 : BitVec 64 := v299 &&& 4503599627370495#64
  let v301 : BitVec 128 := v298 >>> 52
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock6.runBodyFrom E' 0 s = .value (carryGapEnv6 E d3 u221 u295, s) by
    exact this E rfl
  intro E' hE
  step_pure [h221, h260, h295, hk23, hk31, hk34, h296u, h296s]
  step_pure [h221, h260, h295, hk23, hk31, hk34, h297u, h297s]
  step_pure [h221, h260, h295, hk23, hk31, hk34, h298u, h298s]
  step_pure [h221, h260, h295, hk23, hk31, hk34]
  step_pure [h221, h260, h295, hk23, hk31, hk34]
  step_pure [h221, h260, h295, hk23, hk31, hk34]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
