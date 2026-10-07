import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def unpackBlock1 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 128).take 18}

def unpackEnv1 (E : Env program.Γ) (a : Pointer) (s : GlobalState) : Env program.Γ :=
  let v117 : Pointer := a.add 8#64
  let v118 : BitVec 32 := s.mem.readAt (a.add 8#64) 32
  let v119 : BitVec 64 := v118.setWidth 64
  let v120 : Pointer := a.add 12#64
  let v121 : BitVec 8 := s.mem.readAt (a.add 12#64) 8
  let v122 : BitVec 64 := v121.setWidth 64
  let v123 : BitVec 64 := v122 <<< 32
  let v124 : BitVec 64 := v123 ||| v119
  let v125 : Pointer := a.add 13#64
  let v126 : BitVec 8 := s.mem.readAt (a.add 13#64) 8
  let v127 : BitVec 64 := v126.setWidth 64
  let v128 : BitVec 64 := v127 <<< 40
  let v129 : Pointer := a.add 14#64
  let v130 : BitVec 16 := s.mem.readAt (a.add 14#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : BitVec 64 := v131 <<< 48
  let v133 : BitVec 64 := v132 ||| v128
  let v134 : BitVec 64 := v133 ||| v124
  E[%117 := .value v117][%118 := .value v118][%119 := .value v119][%120 := .value v120][%121 := .value v121][%122 := .value v122][%123 := .value v123][%124 := .value v124][%125 := .value v125][%126 := .value v126][%127 := .value v127][%128 := .value v128][%129 := .value v129][%130 := .value v130][%131 := .value v131][%132 := .value v132][%133 := .value v133][%134 := .value v134]

theorem unpack_chunk1 (E : Env program.Γ) (a : Pointer) (s : GlobalState)
    (ha : SmallRange s.mem a 32)
    (harg : E.read (%arg1) = .value a)
    (hk2 : E.read (%2) = .value 32#64)
    (hk4 : E.read (%4) = .value 40#64)
    (hk6 : E.read (%6) = .value 48#64)
    (hk9 : E.read (%9) = .value 8#64)
    (hk10 : E.read (%10) = .value 12#64)
    (hk11 : E.read (%11) = .value 13#64)
    (hk12 : E.read (%12) = .value 14#64)
    : unpackBlock1.runBodyFrom E 0 s = .value (unpackEnv1 E a s, s) := by
  let v117 : Pointer := a.add 8#64
  let v118 : BitVec 32 := s.mem.readAt (a.add 8#64) 32
  let v119 : BitVec 64 := v118.setWidth 64
  let v120 : Pointer := a.add 12#64
  let v121 : BitVec 8 := s.mem.readAt (a.add 12#64) 8
  let v122 : BitVec 64 := v121.setWidth 64
  let v123 : BitVec 64 := v122 <<< 32
  let v124 : BitVec 64 := v123 ||| v119
  let v125 : Pointer := a.add 13#64
  let v126 : BitVec 8 := s.mem.readAt (a.add 13#64) 8
  let v127 : BitVec 64 := v126.setWidth 64
  let v128 : BitVec 64 := v127 <<< 40
  let v129 : Pointer := a.add 14#64
  let v130 : BitVec 16 := s.mem.readAt (a.add 14#64) 16
  let v131 : BitVec 64 := v130.setWidth 64
  let v132 : BitVec 64 := v131 <<< 48
  let v133 : BitVec 64 := v132 ||| v128
  let v134 : BitVec 64 := v133 ||| v124
  have h123u : (v122 <<< 32) >>> 32 = v122 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 32 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v121.isLt
      omega
    · decide
  have h123s : (v122 <<< 32).sshiftRight 32 = v122 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 32 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v121.isLt
      omega
    · decide
  have h124d : v123 &&& v119 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v123, v122, v119,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h128u : (v127 <<< 40) >>> 40 = v127 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 40 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v126.isLt
      omega
    · decide
  have h128s : (v127 <<< 40).sshiftRight 40 = v127 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 40 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v126.isLt
      omega
    · decide
  have h132u : (v131 <<< 48) >>> 48 = v131 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 48 (2 ^ 16 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 16 ≤ 64)]
      have h := v130.isLt
      omega
    · decide
  have h133d : v132 &&& v128 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v132, v131, v128, v127,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h134d : v133 &&& v124 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v133, v132, v131, v128, v127, v124, v123, v122, v119,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  dsimp only [v117, v118, v119, v120, v121, v122, v123, v124, v125, v126, v127, v128, v129, v130, v131, v132, v133, v134] at h123u h123s h124d h128u h128s h132u h133d h134d
  suffices ∀ (E' : Env program.Γ), E' = E →
      unpackBlock1.runBodyFrom E' 0 s = .value (unpackEnv1 E a s, s) by
    exact this E rfl
  intro E' hE
  have hEargs : E'.args = E.args := by rw [hE]
  change E.args 1 = .value a at harg
  have hf118 := ha.fits_add (k := 8) (count := 4) (by decide)
  have hf121 := ha.fits_add (k := 12) (count := 1) (by decide)
  have hf126 := ha.fits_add (k := 13) (count := 1) (by decide)
  have hf130 := ha.fits_add (k := 14) (count := 2) (by decide)
  have hgep := ha.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  have hgep := ha.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12, h123u, h123s]
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12, h124d]
  have hgep := ha.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12, h128u, h128s]
  have hgep := ha.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12]
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12, h132u]
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12, h133d]
  step_pure [harg, hk2, hk4, hk6, hk9, hk10, hk11, hk12, h134d]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
