import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock3 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 313).take 7}

def carryGapEnv3 (E : Env program.Γ) (d0 d2 d3 : BitVec 64) (u206 u263 : BitVec 128) : Env program.Γ :=
  let v264 : BitVec 128 := (d0.setWidth 128) <<< 44
  let v265 : BitVec 128 := (d2.setWidth 128) * 1367801#128
  let v266 : BitVec 128 := (d3.setWidth 128) * 3916664325105025#128
  let v267 : BitVec 128 := u206 + v264
  let v268 : BitVec 128 := v267 + v265
  let v269 : BitVec 128 := v268 + v266
  let v270 : BitVec 128 := v269 + u263
  E[%264 := .value v264][%265 := .value v265][%266 := .value v266][%267 := .value v267][%268 := .value v268][%269 := .value v269][%270 := .value v270]

theorem carry_gap3 (E : Env program.Γ) (s : GlobalState) (d0 d2 d3 : BitVec 64) (u206 u263 : BitVec 128)
    (hd226 : d0.toNat < 2 ^ 52)
    (h226 : E.read (%226) = .value (d0.setWidth 128))
    (hd248 : d2.toNat < 2 ^ 52)
    (h248 : E.read (%248) = .value (d2.setWidth 128))
    (hd260 : d3.toNat < 2 ^ 52)
    (h260 : E.read (%260) = .value (d3.setWidth 128))
    (hu206 : u206.toNat < 2 ^ 110)
    (h206 : E.read (%206) = .value u206)
    (hu263 : u263.toNat < 2 ^ 110)
    (h263 : E.read (%263) = .value u263)
    (hk32 : E.read (%32) = .value 3916664325105025#128)
    (hk33 : E.read (%33) = .value 1367801#128)
    (hk34 : E.read (%34) = .value 44#128)
    : carryGapBlock3.runBodyFrom E 0 s = .value (carryGapEnv3 E d0 d2 d3 u206 u263, s) := by
  let v264 : BitVec 128 := (d0.setWidth 128) <<< 44
  obtain ⟨h264u, h264s, h264n⟩ := carry_shift44_flags d0 hd226
  let v265 : BitVec 128 := (d2.setWidth 128) * 1367801#128
  obtain ⟨h265u, h265s, h265n⟩ := product_constant_flags d2 1367801#128 hd248 (by decide)
  let v266 : BitVec 128 := (d3.setWidth 128) * 3916664325105025#128
  obtain ⟨h266u, h266s, h266n⟩ := product_constant_flags d3 3916664325105025#128 hd260 (by decide)
  let v267 : BitVec 128 := u206 + v264
  have h267bound : (u206).toNat + (v264).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, h264n, h265n, h266n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h267u, h267s, h267n⟩ := product_add_flags (u206) (v264)
    (h267bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267] at h267u h267s h267n
  let v268 : BitVec 128 := v267 + v265
  have h268bound : (v267).toNat + (v265).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, v268, h264n, h265n, h266n, h267n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h268u, h268s, h268n⟩ := product_add_flags (v267) (v265)
    (h268bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267, v268] at h268u h268s h268n
  let v269 : BitVec 128 := v268 + v266
  have h269bound : (v268).toNat + (v266).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, v268, v269, h264n, h265n, h266n, h267n, h268n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h269u, h269s, h269n⟩ := product_add_flags (v268) (v266)
    (h269bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267, v268, v269] at h269u h269s h269n
  let v270 : BitVec 128 := v269 + u263
  have h270bound : (v269).toNat + (u263).toNat < 2 ^ 120 := by
    simp only [v264, v265, v266, v267, v268, v269, v270, h264n, h265n, h266n, h267n, h268n, h269n]
    norm_num at hd226 hd248 hd260 hu206 hu263 ⊢
    omega
  obtain ⟨h270u, h270s, h270n⟩ := product_add_flags (v269) (u263)
    (h270bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v264, v265, v266, v267, v268, v269, v270] at h270u h270s h270n
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock3.runBodyFrom E' 0 s = .value (carryGapEnv3 E d0 d2 d3 u206 u263, s) by
    exact this E rfl
  intro E' hE
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h264u, h264s]
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h265u, h265s]
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h266u, h266s]
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h267u, h267s]
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h268u, h268s]
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h269u, h269s]
  step_pure [h206, h226, h248, h260, h263, hk32, hk33, hk34, h270u, h270s]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
