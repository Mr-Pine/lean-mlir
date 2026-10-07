import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def unpackBlock2 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 147).take 18}

def unpackEnv2 (E : Env program.Γ) (a : Pointer) (s : GlobalState) : Env program.Γ :=
  let v135 : Pointer := a.add 16#64
  let v136 : BitVec 16 := s.mem.readAt (a.add 16#64) 16
  let v137 : BitVec 64 := v136.setWidth 64
  let v138 : Pointer := a.add 18#64
  let v139 : BitVec 8 := s.mem.readAt (a.add 18#64) 8
  let v140 : BitVec 64 := v139.setWidth 64
  let v141 : BitVec 64 := v140 <<< 16
  let v142 : BitVec 64 := v141 ||| v137
  let v143 : Pointer := a.add 19#64
  let v144 : BitVec 8 := s.mem.readAt (a.add 19#64) 8
  let v145 : BitVec 64 := v144.setWidth 64
  let v146 : BitVec 64 := v145 <<< 24
  let v147 : BitVec 64 := v142 ||| v146
  let v148 : Pointer := a.add 20#64
  let v149 : BitVec 32 := s.mem.readAt (a.add 20#64) 32
  let v150 : BitVec 64 := v149.setWidth 64
  let v151 : BitVec 64 := v150 <<< 32
  let v152 : BitVec 64 := v151 ||| v147
  E[%135 := .value v135][%136 := .value v136][%137 := .value v137][%138 := .value v138][%139 := .value v139][%140 := .value v140][%141 := .value v141][%142 := .value v142][%143 := .value v143][%144 := .value v144][%145 := .value v145][%146 := .value v146][%147 := .value v147][%148 := .value v148][%149 := .value v149][%150 := .value v150][%151 := .value v151][%152 := .value v152]

theorem unpack_chunk2 (E : Env program.Γ) (a : Pointer) (s : GlobalState)
    (ha : SmallRange s.mem a 32)
    (harg : E.read (%arg1) = .value a)
    (hk2 : E.read (%2) = .value 32#64)
    (hk13 : E.read (%13) = .value 16#64)
    (hk14 : E.read (%14) = .value 18#64)
    (hk15 : E.read (%15) = .value 19#64)
    (hk16 : E.read (%16) = .value 24#64)
    (hk17 : E.read (%17) = .value 20#64)
    : unpackBlock2.runBodyFrom E 0 s = .value (unpackEnv2 E a s, s) := by
  let v135 : Pointer := a.add 16#64
  let v136 : BitVec 16 := s.mem.readAt (a.add 16#64) 16
  let v137 : BitVec 64 := v136.setWidth 64
  let v138 : Pointer := a.add 18#64
  let v139 : BitVec 8 := s.mem.readAt (a.add 18#64) 8
  let v140 : BitVec 64 := v139.setWidth 64
  let v141 : BitVec 64 := v140 <<< 16
  let v142 : BitVec 64 := v141 ||| v137
  let v143 : Pointer := a.add 19#64
  let v144 : BitVec 8 := s.mem.readAt (a.add 19#64) 8
  let v145 : BitVec 64 := v144.setWidth 64
  let v146 : BitVec 64 := v145 <<< 24
  let v147 : BitVec 64 := v142 ||| v146
  let v148 : Pointer := a.add 20#64
  let v149 : BitVec 32 := s.mem.readAt (a.add 20#64) 32
  let v150 : BitVec 64 := v149.setWidth 64
  let v151 : BitVec 64 := v150 <<< 32
  let v152 : BitVec 64 := v151 ||| v147
  have h141u : (v140 <<< 16) >>> 16 = v140 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 16 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v139.isLt
      omega
    · decide
  have h141s : (v140 <<< 16).sshiftRight 16 = v140 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 16 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v139.isLt
      omega
    · decide
  have h142d : v141 &&& v137 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v141, v140, v137,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h146u : (v145 <<< 24) >>> 24 = v145 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 24 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v144.isLt
      omega
    · decide
  have h146s : (v145 <<< 24).sshiftRight 24 = v145 := by
    apply Agave.Ed25519.Encoding.RIR.shift_signed_safe _ 24 (2 ^ 8 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      have h := v144.isLt
      omega
    · decide
  have h147d : v142 &&& v146 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v142, v141, v140, v137, v146, v145,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h151u : (v150 <<< 32) >>> 32 = v150 := by
    apply Agave.Ed25519.Encoding.RIR.shift_unsigned_safe _ 32 (2 ^ 32 - 1)
    · rw [BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
      have h := v149.isLt
      omega
    · decide
  have h152d : v151 &&& v147 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [v151, v150, v147, v142, v141, v140, v137, v146, v145,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  dsimp only [v135, v136, v137, v138, v139, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152] at h141u h141s h142d h146u h146s h147d h151u h152d
  suffices ∀ (E' : Env program.Γ), E' = E →
      unpackBlock2.runBodyFrom E' 0 s = .value (unpackEnv2 E a s, s) by
    exact this E rfl
  intro E' hE
  have hEargs : E'.args = E.args := by rw [hE]
  change E.args 1 = .value a at harg
  have hf136 := ha.fits_add (k := 16) (count := 2) (by decide)
  have hf139 := ha.fits_add (k := 18) (count := 1) (by decide)
  have hf144 := ha.fits_add (k := 19) (count := 1) (by decide)
  have hf149 := ha.fits_add (k := 20) (count := 4) (by decide)
  have hgep := ha.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk13, hk14, hk15, hk16, hk17]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17]
  have hgep := ha.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk13, hk14, hk15, hk16, hk17]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17]
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17, h141u, h141s]
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17, h142d]
  have hgep := ha.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk13, hk14, hk15, hk16, hk17]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17]
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17, h146u, h146s]
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17, h147d]
  have hgep := ha.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, harg, hk2, hk13, hk14, hk15, hk16, hk17]
  clear hgep
  step_load [harg] inline
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17]
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17, h151u]
  step_pure [harg, hk2, hk13, hk14, hk15, hk16, hk17, h152d]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
