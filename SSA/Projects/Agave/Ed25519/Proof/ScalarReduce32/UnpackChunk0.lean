import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def unpackBlock0 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 106).take 22}

def unpackEnv0 (E : Env program.Γ) (a : Pointer) (s : GlobalState) : Env program.Γ :=
  let v95 : BitVec 32 := s.mem.readAt a 32
  let v96 : BitVec 64 := v95.setWidth 64
  let v97 : Pointer := a.add 4#64
  let v98 : BitVec 8 := s.mem.readAt (a.add 4#64) 8
  let v99 : BitVec 64 := v98.setWidth 64
  let v100 : BitVec 64 := v99 <<< 32
  let v101 : BitVec 64 := v100 ||| v96
  let v102 : Pointer := a.add 5#64
  let v103 : BitVec 8 := s.mem.readAt (a.add 5#64) 8
  let v104 : BitVec 64 := v103.setWidth 64
  let v105 : BitVec 64 := v104 <<< 40
  let v106 : BitVec 64 := v101 ||| v105
  let v107 : Pointer := a.add 6#64
  let v108 : BitVec 8 := s.mem.readAt (a.add 6#64) 8
  let v109 : BitVec 64 := v108.setWidth 64
  let v110 : BitVec 64 := v109 <<< 48
  let v111 : BitVec 64 := v106 ||| v110
  let v112 : Pointer := a.add 7#64
  let v113 : BitVec 8 := s.mem.readAt (a.add 7#64) 8
  let v114 : BitVec 64 := v113.setWidth 64
  let v115 : BitVec 64 := v114 <<< 56
  let v116 : BitVec 64 := v115 ||| v111
  E[%95 := .value v95][%96 := .value v96][%97 := .value v97][%98 := .value v98][%99 := .value v99][%100 := .value v100][%101 := .value v101][%102 := .value v102][%103 := .value v103][%104 := .value v104][%105 := .value v105][%106 := .value v106][%107 := .value v107][%108 := .value v108][%109 := .value v109][%110 := .value v110][%111 := .value v111][%112 := .value v112][%113 := .value v113][%114 := .value v114][%115 := .value v115][%116 := .value v116]

theorem unpack_chunk0 (E : Env program.Γ) (a : Pointer) (s : GlobalState)
    (ha : SmallRange s.mem a 32)
    (harg : E.read (%arg1) = .value a)
    (hk1 : E.read (%1) = .value 4#64)
    (hk2 : E.read (%2) = .value 32#64)
    (hk3 : E.read (%3) = .value 5#64)
    (hk4 : E.read (%4) = .value 40#64)
    (hk5 : E.read (%5) = .value 6#64)
    (hk6 : E.read (%6) = .value 48#64)
    (hk7 : E.read (%7) = .value 7#64)
    (hk8 : E.read (%8) = .value 56#64)
    : unpackBlock0.runBodyFrom E 0 s = .value (unpackEnv0 E a s, s) := by
  let v95 : BitVec 32 := s.mem.readAt a 32
  let v96 : BitVec 64 := v95.setWidth 64
  let v97 : Pointer := a.add 4#64
  let v98 : BitVec 8 := s.mem.readAt (a.add 4#64) 8
  let v99 : BitVec 64 := v98.setWidth 64
  let v100 : BitVec 64 := v99 <<< 32
  let v101 : BitVec 64 := v100 ||| v96
  let v102 : Pointer := a.add 5#64
  let v103 : BitVec 8 := s.mem.readAt (a.add 5#64) 8
  let v104 : BitVec 64 := v103.setWidth 64
  let v105 : BitVec 64 := v104 <<< 40
  let v106 : BitVec 64 := v101 ||| v105
  let v107 : Pointer := a.add 6#64
  let v108 : BitVec 8 := s.mem.readAt (a.add 6#64) 8
  let v109 : BitVec 64 := v108.setWidth 64
  let v110 : BitVec 64 := v109 <<< 48
  let v111 : BitVec 64 := v106 ||| v110
  let v112 : Pointer := a.add 7#64
  let v113 : BitVec 8 := s.mem.readAt (a.add 7#64) 8
  let v114 : BitVec 64 := v113.setWidth 64
  let v115 : BitVec 64 := v114 <<< 56
  let v116 : BitVec 64 := v115 ||| v111
  have h100u : (v99 <<< 32) >>> 32 = v99 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 32 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v98.isLt
      omega
    · decide
  have h100s : (v99 <<< 32).sshiftRight 32 = v99 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 32 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v98.isLt
      omega
    · decide
  have h101d : v100 &&& v96 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v100, v99, v96,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h105u : (v104 <<< 40) >>> 40 = v104 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 40 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v103.isLt
      omega
    · decide
  have h105s : (v104 <<< 40).sshiftRight 40 = v104 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 40 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v103.isLt
      omega
    · decide
  have h106d : v101 &&& v105 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v101, v100, v99, v96, v105, v104,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h110u : (v109 <<< 48) >>> 48 = v109 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 48 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v108.isLt
      omega
    · decide
  have h110s : (v109 <<< 48).sshiftRight 48 = v109 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 48 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v108.isLt
      omega
    · decide
  have h111d : v106 &&& v110 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v106, v101, v100, v99, v96, v105, v104, v110, v109,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h115u : (v114 <<< 56) >>> 56 = v114 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 56 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v113.isLt
      omega
    · decide
  have h116d : v115 &&& v111 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v115, v114, v111, v106, v101, v100, v99, v96, v105, v104, v110, v109,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  dsimp only [v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116] at h100u h100s h101d h105u h105s h106d h110u h110s h111d h115u h116d
  suffices ∀ (E' : Env program.Γ), E' = E →
      unpackBlock0.runBodyFrom E' 0 s = .value (unpackEnv0 E a s, s) by
    exact this E rfl
  intro E' hE
  have hEargs : E'.args = E.args := by rw [hE]
  change E.args 1 = .value a at harg
  have hf95 := ha.fits_add (k := 0) (count := 4) (by decide)
  simp only [Pointer.add_zero] at hf95
  have hf98 := ha.fits_add (k := 4) (count := 1) (by decide)
  have hf103 := ha.fits_add (k := 5) (count := 1) (by decide)
  have hf108 := ha.fits_add (k := 6) (count := 1) (by decide)
  have hf113 := ha.fits_add (k := 7) (count := 1) (by decide)
  step_load [harg] inline
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  have hgep := ha.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h100u, h100s]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h101d]
  have hgep := ha.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h105u, h105s]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h106d]
  have hgep := ha.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h110u, h110s]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h111d]
  have hgep := ha.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h115u]
  step_pure [harg, hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, h116d]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
