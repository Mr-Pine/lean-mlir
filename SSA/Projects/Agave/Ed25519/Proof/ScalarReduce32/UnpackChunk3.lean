import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def unpackBlock3 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 166).take 18}

def unpackEnv3 (E : Env program.Γ) (a : Pointer) (s : GlobalState) : Env program.Γ :=
  let v153 : Pointer := a.add 24#64
  let v154 : BitVec 8 := s.mem.readAt (a.add 24#64) 8
  let v155 : BitVec 64 := v154.setWidth 64
  let v156 : Pointer := a.add 25#64
  let v157 : BitVec 8 := s.mem.readAt (a.add 25#64) 8
  let v158 : BitVec 64 := v157.setWidth 64
  let v159 : BitVec 64 := v158 <<< 8
  let v160 : BitVec 64 := v159 ||| v155
  let v161 : Pointer := a.add 26#64
  let v162 : BitVec 32 := s.mem.readAt (a.add 26#64) 32
  let v163 : BitVec 64 := v162.setWidth 64
  let v164 : BitVec 64 := v163 <<< 16
  let v165 : Pointer := a.add 30#64
  let v166 : BitVec 16 := s.mem.readAt (a.add 30#64) 16
  let v167 : BitVec 64 := v166.setWidth 64
  let v168 : BitVec 64 := v167 <<< 48
  let v169 : BitVec 64 := v168 ||| v164
  let v170 : BitVec 64 := v169 ||| v160
  E[%153 := .value v153][%154 := .value v154][%155 := .value v155][%156 := .value v156][%157 := .value v157][%158 := .value v158][%159 := .value v159][%160 := .value v160][%161 := .value v161][%162 := .value v162][%163 := .value v163][%164 := .value v164][%165 := .value v165][%166 := .value v166][%167 := .value v167][%168 := .value v168][%169 := .value v169][%170 := .value v170]

theorem unpack_chunk3 (E : Env program.Γ) (a : Pointer) (s : GlobalState)
    (ha : SmallRange s.mem a 32)
    (harg : E.read (%arg1) = .value a)
    (hk6 : E.read (%6) = .value 48#64)
    (hk9 : E.read (%9) = .value 8#64)
    (hk13 : E.read (%13) = .value 16#64)
    (hk16 : E.read (%16) = .value 24#64)
    (hk18 : E.read (%18) = .value 25#64)
    (hk19 : E.read (%19) = .value 26#64)
    (hk20 : E.read (%20) = .value 30#64)
    : unpackBlock3.runBodyFrom E 0 s = .value (unpackEnv3 E a s, s) := by
  let v153 : Pointer := a.add 24#64
  let v154 : BitVec 8 := s.mem.readAt (a.add 24#64) 8
  let v155 : BitVec 64 := v154.setWidth 64
  let v156 : Pointer := a.add 25#64
  let v157 : BitVec 8 := s.mem.readAt (a.add 25#64) 8
  let v158 : BitVec 64 := v157.setWidth 64
  let v159 : BitVec 64 := v158 <<< 8
  let v160 : BitVec 64 := v159 ||| v155
  let v161 : Pointer := a.add 26#64
  let v162 : BitVec 32 := s.mem.readAt (a.add 26#64) 32
  let v163 : BitVec 64 := v162.setWidth 64
  let v164 : BitVec 64 := v163 <<< 16
  let v165 : Pointer := a.add 30#64
  let v166 : BitVec 16 := s.mem.readAt (a.add 30#64) 16
  let v167 : BitVec 64 := v166.setWidth 64
  let v168 : BitVec 64 := v167 <<< 48
  let v169 : BitVec 64 := v168 ||| v164
  let v170 : BitVec 64 := v169 ||| v160
  have h159u : (v158 <<< 8) >>> 8 = v158 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 8 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v157.isLt
      omega
    · decide
  have h159s : (v158 <<< 8).sshiftRight 8 = v158 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 8 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v157.isLt
      omega
    · decide
  have h160d : v159 &&& v155 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v159, v158, v155,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h164u : (v163 <<< 16) >>> 16 = v163 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 16 (2 ^ 32 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
      have h := v162.isLt
      omega
    · decide
  have h164s : (v163 <<< 16).sshiftRight 16 = v163 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 16 (2 ^ 32 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
      have h := v162.isLt
      omega
    · decide
  have h168u : (v167 <<< 48) >>> 48 = v167 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 48 (2 ^ 16 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 16 ≤ 64)]
      have h := v166.isLt
      omega
    · decide
  have h169d : v168 &&& v164 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v168, v167, v164, v163,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h170d : v169 &&& v160 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v169, v168, v167, v164, v163, v160, v159, v158, v155,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  dsimp only [v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170] at h159u h159s h160d h164u h164s h168u h169d h170d
  suffices ∀ (E' : Env program.Γ), E' = E →
      unpackBlock3.runBodyFrom E' 0 s = .value (unpackEnv3 E a s, s) by
    exact this E rfl
  intro E' hE
  have hEargs : E'.args = E.args := by rw [hE]
  change E.args 1 = .value a at harg
  have hf154 := ha.fits_add (k := 24) (count := 1) (by decide)
  have hf157 := ha.fits_add (k := 25) (count := 1) (by decide)
  have hf162 := ha.fits_add (k := 26) (count := 4) (by decide)
  have hf166 := ha.fits_add (k := 30) (count := 2) (by decide)
  have hgep := ha.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  have hgep := ha.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20, h159u, h159s]
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20, h160d]
  have hgep := ha.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20, h164u, h164s]
  have hgep := ha.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20]
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20, h168u]
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20, h169d]
  step_pure [harg, hk6, hk9, hk13, hk16, hk18, hk19, hk20, h170d]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
