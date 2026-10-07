import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock4 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 327).take 10}

def carryGapEnv4 (E : Env program.Γ) (d1 d3 d4 : BitVec 64) (u213 u277 : BitVec 128) : Env program.Γ :=
  let v278 : BitVec 128 := (d1.setWidth 128) <<< 44
  let v279 : BitVec 128 := (d3.setWidth 128) * 1367801#128
  let v280 : BitVec 128 := (d4.setWidth 128) * 3916664325105025#128
  let v281 : BitVec 128 := u213 + v278
  let v282 : BitVec 128 := v281 + v279
  let v283 : BitVec 128 := v282 + v280
  let v284 : BitVec 128 := v283 + u277
  let v285 : BitVec 64 := (v284).setWidth 64
  let v286 : BitVec 64 := v285 &&& 4503599627370495#64
  let v287 : BitVec 128 := v284 >>> 52
  E[%278 := .value v278][%279 := .value v279][%280 := .value v280][%281 := .value v281][%282 := .value v282][%283 := .value v283][%284 := .value v284][%285 := .value v285][%286 := .value v286][%287 := .value v287]

theorem carry_gap4 (E : Env program.Γ) (s : GlobalState) (d1 d3 d4 : BitVec 64) (u213 u277 : BitVec 128)
    (hd236 : d1.toNat < 2 ^ 52)
    (h236 : E.read (%236) = .value (d1.setWidth 128))
    (hd260 : d3.toNat < 2 ^ 52)
    (h260 : E.read (%260) = .value (d3.setWidth 128))
    (hd274 : d4.toNat < 2 ^ 52)
    (h274 : E.read (%274) = .value (d4.setWidth 128))
    (hu213 : u213.toNat < 2 ^ 110)
    (h213 : E.read (%213) = .value u213)
    (hu277 : u277.toNat < 2 ^ 110)
    (h277 : E.read (%277) = .value u277)
    (hk23 : E.read (%23) = .value 4503599627370495#64)
    (hk31 : E.read (%31) = .value 52#128)
    (hk32 : E.read (%32) = .value 3916664325105025#128)
    (hk33 : E.read (%33) = .value 1367801#128)
    (hk34 : E.read (%34) = .value 44#128)
    : carryGapBlock4.runBodyFrom E 0 s = .value (carryGapEnv4 E d1 d3 d4 u213 u277, s) := by
  let v278 : BitVec 128 := (d1.setWidth 128) <<< 44
  obtain ⟨h278u, h278s, h278n⟩ := carry_shift44_flags d1 hd236
  let v279 : BitVec 128 := (d3.setWidth 128) * 1367801#128
  obtain ⟨h279u, h279s, h279n⟩ := product_constant_flags d3 1367801#128 hd260 (by decide)
  let v280 : BitVec 128 := (d4.setWidth 128) * 3916664325105025#128
  obtain ⟨h280u, h280s, h280n⟩ := product_constant_flags d4 3916664325105025#128 hd274 (by decide)
  let v281 : BitVec 128 := u213 + v278
  have h281bound : (u213).toNat + (v278).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, h278n, h279n, h280n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h281u, h281s, h281n⟩ := product_add_flags (u213) (v278)
    (h281bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281] at h281u h281s h281n
  let v282 : BitVec 128 := v281 + v279
  have h282bound : (v281).toNat + (v279).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, v282, h278n, h279n, h280n, h281n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h282u, h282s, h282n⟩ := product_add_flags (v281) (v279)
    (h282bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281, v282] at h282u h282s h282n
  let v283 : BitVec 128 := v282 + v280
  have h283bound : (v282).toNat + (v280).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, v282, v283, h278n, h279n, h280n, h281n, h282n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h283u, h283s, h283n⟩ := product_add_flags (v282) (v280)
    (h283bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281, v282, v283] at h283u h283s h283n
  let v284 : BitVec 128 := v283 + u277
  have h284bound : (v283).toNat + (u277).toNat < 2 ^ 120 := by
    simp only [v278, v279, v280, v281, v282, v283, v284, h278n, h279n, h280n, h281n, h282n, h283n]
    norm_num at hd236 hd260 hd274 hu213 hu277 ⊢
    omega
  obtain ⟨h284u, h284s, h284n⟩ := product_add_flags (v283) (u277)
    (h284bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v278, v279, v280, v281, v282, v283, v284] at h284u h284s h284n
  let v285 : BitVec 64 := (v284).setWidth 64
  let v286 : BitVec 64 := v285 &&& 4503599627370495#64
  let v287 : BitVec 128 := v284 >>> 52
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock4.runBodyFrom E' 0 s = .value (carryGapEnv4 E d1 d3 d4 u213 u277, s) by
    exact this E rfl
  intro E' hE
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h278u, h278s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h279u, h279s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h280u, h280s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h281u, h281s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h282u, h282s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h283u, h283s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34, h284u, h284s]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34]
  step_pure [h213, h236, h260, h274, h277, hk23, hk31, hk32, hk33, hk34]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
