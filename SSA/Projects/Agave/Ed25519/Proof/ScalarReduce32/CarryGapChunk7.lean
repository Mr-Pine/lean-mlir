import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapFlags

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def carryGapBlock7 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 351).take 7}

def carryGapEnv7 (E : Env program.Γ) (d4 : BitVec 64) (u222 u301 : BitVec 128) : Env program.Γ :=
  let v302 : BitVec 128 := (d4.setWidth 128) <<< 44
  let v303 : BitVec 128 := v302 + u222
  let v304 : BitVec 128 := v303 + u301
  let v305 : BitVec 64 := (v304).setWidth 64
  let v306 : BitVec 64 := v305 &&& 4503599627370495#64
  let v307 : BitVec 128 := v304 >>> 52
  let v308 : BitVec 64 := (v307).setWidth 64
  E[%302 := .value v302][%303 := .value v303][%304 := .value v304][%305 := .value v305][%306 := .value v306][%307 := .value v307][%308 := .value v308]

theorem carry_gap7 (E : Env program.Γ) (s : GlobalState) (d4 : BitVec 64) (u222 u301 : BitVec 128)
    (hd274 : d4.toNat < 2 ^ 52)
    (h274 : E.read (%274) = .value (d4.setWidth 128))
    (hu222 : u222.toNat < 2 ^ 110)
    (h222 : E.read (%222) = .value u222)
    (hu301 : u301.toNat < 2 ^ 110)
    (h301 : E.read (%301) = .value u301)
    (hk23 : E.read (%23) = .value 4503599627370495#64)
    (hk31 : E.read (%31) = .value 52#128)
    (hk34 : E.read (%34) = .value 44#128)
    : carryGapBlock7.runBodyFrom E 0 s = .value (carryGapEnv7 E d4 u222 u301, s) := by
  let v302 : BitVec 128 := (d4.setWidth 128) <<< 44
  obtain ⟨h302u, h302s, h302n⟩ := carry_shift44_flags d4 hd274
  let v303 : BitVec 128 := v302 + u222
  have h303bound : (v302).toNat + (u222).toNat < 2 ^ 120 := by
    simp only [v302, v303, h302n]
    norm_num at hd274 hu222 hu301 ⊢
    omega
  obtain ⟨h303u, h303s, h303n⟩ := product_add_flags (v302) (u222)
    (h303bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v302, v303] at h303u h303s h303n
  let v304 : BitVec 128 := v303 + u301
  have h304bound : (v303).toNat + (u301).toNat < 2 ^ 120 := by
    simp only [v302, v303, v304, h302n, h303n]
    norm_num at hd274 hu222 hu301 ⊢
    omega
  obtain ⟨h304u, h304s, h304n⟩ := product_add_flags (v303) (u301)
    (h304bound.trans (by decide : 2 ^ 120 < 2 ^ 127))
  dsimp only [v302, v303, v304] at h304u h304s h304n
  let v305 : BitVec 64 := (v304).setWidth 64
  let v306 : BitVec 64 := v305 &&& 4503599627370495#64
  let v307 : BitVec 128 := v304 >>> 52
  let v308 : BitVec 64 := (v307).setWidth 64
  have h308bound : (v307).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have h := h304bound
    rw [h304n]
    norm_num at h ⊢
    omega
  obtain ⟨h308u, h308s⟩ := carry_trunc64_flags (v307) h308bound
  dsimp only [v302, v303, v304, v305, v306, v307, v308] at h308u h308s
  suffices ∀ (E' : Env program.Γ), E' = E →
      carryGapBlock7.runBodyFrom E' 0 s = .value (carryGapEnv7 E d4 u222 u301, s) by
    exact this E rfl
  intro E' hE
  step_pure [h222, h274, h301, hk23, hk31, hk34, h302u, h302s]
  step_pure [h222, h274, h301, hk23, hk31, hk34, h303u, h303s]
  step_pure [h222, h274, h301, hk23, hk31, hk34, h304u, h304s]
  step_pure [h222, h274, h301, hk23, hk31, hk34]
  step_pure [h222, h274, h301, hk23, hk31, hk34]
  step_pure [h222, h274, h301, hk23, hk31, hk34]
  step_pure [h222, h274, h301, hk23, hk31, hk34, h308u, h308s]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  rw [hE]
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
