import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock5 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 337).take 8}

def carryGapEnv5 (E : Env program.Γ) (d2 d4 : BitVec 64) (u218 u287 : BitVec 128) : Env program.Γ :=
  let v288 : BitVec 128 := (d2.setWidth 128) <<< 44
  let v289 : BitVec 128 := (d4.setWidth 128) * 1367801#128
  let v290 : BitVec 128 := v288 + u218
  let v291 : BitVec 128 := v290 + v289
  let v292 : BitVec 128 := v291 + u287
  let v293 : BitVec 64 := (v292).setWidth 64
  let v294 : BitVec 64 := v293 &&& 4503599627370495#64
  let v295 : BitVec 128 := v292 >>> 52
  E[%288 := .value v288][%289 := .value v289][%290 := .value v290][%291 := .value v291][%292 := .value v292][%293 := .value v293][%294 := .value v294][%295 := .value v295]

theorem carry_gap5 (E : Env program.Γ) (s : GlobalState) (d2 d4 : BitVec 64) (u218 u287 : BitVec 128)
    (hd248 : d2.toNat < 2 ^ 52)
    (h248 : E.read (%248) = .value (d2.setWidth 128))
    (hd274 : d4.toNat < 2 ^ 52)
    (h274 : E.read (%274) = .value (d4.setWidth 128))
    (hu218 : u218.toNat < 2 ^ 110)
    (h218 : E.read (%218) = .value u218)
    (hu287 : u287.toNat < 2 ^ 110)
    (h287 : E.read (%287) = .value u287)
    (hk23 : E.read (%23) = .value 4503599627370495#64)
    (hk31 : E.read (%31) = .value 52#128)
    (hk33 : E.read (%33) = .value 1367801#128)
    (hk34 : E.read (%34) = .value 44#128)
    : carryGapBlock5.runBodyFrom E 0 s = .value (carryGapEnv5 E d2 d4 u218 u287, s) := by
  let v288 : BitVec 128 := (d2.setWidth 128) <<< 44
  obtain ⟨h288u, h288s, h288n⟩ := carry_shift44_flags d2 hd248
  let v289 : BitVec 128 := (d4.setWidth 128) * 1367801#128
  obtain ⟨h289u, h289s, h289n⟩ := product_constant_flags d4 1367801#128 hd274 (by decide)
  let v290 : BitVec 128 := v288 + u218
  have h290bound : (v288).toNat + (u218).toNat < 2 ^ 120 := by
    simp only [v288, v289, v290, h288n, h289n]
    norm_num at hd248 hd274 hu218 hu287 ⊢
    omega
  obtain ⟨h290u, h290s, h290n⟩ := product_add_flags (v288) (u218)
    (h290bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v288, v289, v290] at h290u h290s h290n
  let v291 : BitVec 128 := v290 + v289
  have h291bound : (v290).toNat + (v289).toNat < 2 ^ 120 := by
    simp only [v288, v289, v290, v291, h288n, h289n, h290n]
    norm_num at hd248 hd274 hu218 hu287 ⊢
    omega
  obtain ⟨h291u, h291s, h291n⟩ := product_add_flags (v290) (v289)
    (h291bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v288, v289, v290, v291] at h291u h291s h291n
  let v292 : BitVec 128 := v291 + u287
  have h292bound : (v291).toNat + (u287).toNat < 2 ^ 120 := by
    simp only [v288, v289, v290, v291, v292, h288n, h289n, h290n, h291n]
    norm_num at hd248 hd274 hu218 hu287 ⊢
    omega
  obtain ⟨h292u, h292s, h292n⟩ := product_add_flags (v291) (u287)
    (h292bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v288, v289, v290, v291, v292] at h292u h292s h292n
  let v293 : BitVec 64 := (v292).setWidth 64
  let v294 : BitVec 64 := v293 &&& 4503599627370495#64
  let v295 : BitVec 128 := v292 >>> 52
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock5.runBodyFrom E' 0 s = .value (carryGapEnv5 E d2 d4 u218 u287, s) by
    exact this E rfl
  intro E' hE
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34, h288u, h288s]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34, h289u, h289s]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34, h290u, h290s]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34, h291u, h291s]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34, h292u, h292s]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34]
  step_pure [h218, h248, h274, h287, hk23, hk31, hk33, hk34]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
