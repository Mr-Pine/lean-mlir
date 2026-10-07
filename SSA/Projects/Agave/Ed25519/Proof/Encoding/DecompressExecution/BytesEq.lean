import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

namespace Agave.Ed25519.Encoding.Decompress.Execution.BytesEq
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

@[mlir_mem, mlir_transport]
theorem wf_blackBox_return {s : GlobalState} (h : s.WF) :
    ({ s with alloc := (s.alloca 1).alloc } : GlobalState).WF := by
  exact h.add_blocks (k := 1)

/-- One byte comparison, zero-extended exactly as in the imported body. -/
def equalByte (a b : BitVec 8) : BitVec 8 := (BitVec.ofBool (a == b)).setWidth 8

/-- The 32 unrolled byte comparisons in their emitted order. -/
def comparison (s : GlobalState) (a b : Pointer) : BitVec 8 :=
  equalByte (s.mem.readAt (a.add 31#64) 8) (s.mem.readAt (b.add 31#64) 8) &&& (equalByte (s.mem.readAt (a.add 30#64) 8) (s.mem.readAt (b.add 30#64) 8) &&& (equalByte (s.mem.readAt (a.add 29#64) 8) (s.mem.readAt (b.add 29#64) 8) &&& (equalByte (s.mem.readAt (a.add 28#64) 8) (s.mem.readAt (b.add 28#64) 8) &&& (equalByte (s.mem.readAt (a.add 27#64) 8) (s.mem.readAt (b.add 27#64) 8) &&& (equalByte (s.mem.readAt (a.add 26#64) 8) (s.mem.readAt (b.add 26#64) 8) &&& (equalByte (s.mem.readAt (a.add 25#64) 8) (s.mem.readAt (b.add 25#64) 8) &&& (equalByte (s.mem.readAt (a.add 24#64) 8) (s.mem.readAt (b.add 24#64) 8) &&& (equalByte (s.mem.readAt (a.add 23#64) 8) (s.mem.readAt (b.add 23#64) 8) &&& (equalByte (s.mem.readAt (a.add 22#64) 8) (s.mem.readAt (b.add 22#64) 8) &&& (equalByte (s.mem.readAt (a.add 21#64) 8) (s.mem.readAt (b.add 21#64) 8) &&& (equalByte (s.mem.readAt (a.add 20#64) 8) (s.mem.readAt (b.add 20#64) 8) &&& (equalByte (s.mem.readAt (a.add 19#64) 8) (s.mem.readAt (b.add 19#64) 8) &&& (equalByte (s.mem.readAt (a.add 18#64) 8) (s.mem.readAt (b.add 18#64) 8) &&& (equalByte (s.mem.readAt (a.add 17#64) 8) (s.mem.readAt (b.add 17#64) 8) &&& (equalByte (s.mem.readAt (a.add 16#64) 8) (s.mem.readAt (b.add 16#64) 8) &&& (equalByte (s.mem.readAt (a.add 15#64) 8) (s.mem.readAt (b.add 15#64) 8) &&& (equalByte (s.mem.readAt (a.add 14#64) 8) (s.mem.readAt (b.add 14#64) 8) &&& (equalByte (s.mem.readAt (a.add 13#64) 8) (s.mem.readAt (b.add 13#64) 8) &&& (equalByte (s.mem.readAt (a.add 12#64) 8) (s.mem.readAt (b.add 12#64) 8) &&& (equalByte (s.mem.readAt (a.add 11#64) 8) (s.mem.readAt (b.add 11#64) 8) &&& (equalByte (s.mem.readAt (a.add 10#64) 8) (s.mem.readAt (b.add 10#64) 8) &&& (equalByte (s.mem.readAt (a.add 9#64) 8) (s.mem.readAt (b.add 9#64) 8) &&& (equalByte (s.mem.readAt (a.add 8#64) 8) (s.mem.readAt (b.add 8#64) 8) &&& (equalByte (s.mem.readAt (a.add 7#64) 8) (s.mem.readAt (b.add 7#64) 8) &&& (equalByte (s.mem.readAt (a.add 6#64) 8) (s.mem.readAt (b.add 6#64) 8) &&& (equalByte (s.mem.readAt (a.add 5#64) 8) (s.mem.readAt (b.add 5#64) 8) &&& (equalByte (s.mem.readAt (a.add 4#64) 8) (s.mem.readAt (b.add 4#64) 8) &&& (equalByte (s.mem.readAt (a.add 3#64) 8) (s.mem.readAt (b.add 3#64) 8) &&& (equalByte (s.mem.readAt (a.add 2#64) 8) (s.mem.readAt (b.add 2#64) 8) &&& (equalByte (s.mem.readAt (a.add 1#64) 8) (s.mem.readAt (b.add 1#64) 8) &&& (equalByte (s.mem.readAt (a.add 0#64) 8) (s.mem.readAt (b.add 0#64) 8) &&& (1#8))))))))))))))))))))))))))))))))

theorem boolByte_and (a b : Bool) :
    (BitVec.ofBool a).setWidth 8 &&& (BitVec.ofBool b).setWidth 8 =
      (BitVec.ofBool (a && b)).setWidth 8 := by cases a <;> cases b <;> rfl

theorem boolByte_and_one (a : Bool) :
    (BitVec.ofBool a).setWidth 8 &&& 1#8 = (BitVec.ofBool a).setWidth 8 := by
  cases a <;> rfl

theorem boolByte_eq_one (a : Bool) :
    (BitVec.ofBool a).setWidth 8 = 1 ↔ a = true := by cases a <;> decide

set_option maxHeartbeats 2000000 in
/-- Every loaded byte is equal precisely when the result is one. -/
theorem comparison_eq_one_iff (s : GlobalState) (a b : Pointer) :
    comparison s a b = 1 ↔ ∀ i : Fin 32,
      s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8 =
        s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 := by
  simp only [comparison, equalByte, boolByte_and_one, boolByte_and, boolByte_eq_one,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    rcases h with ⟨h31, h30, h29, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h14
    · exact h15
    · exact h16
    · exact h17
    · exact h18
    · exact h19
    · exact h20
    · exact h21
    · exact h22
    · exact h23
    · exact h24
    · exact h25
    · exact h26
    · exact h27
    · exact h28
    · exact h29
    · exact h30
    · exact h31
  · intro h
    exact ⟨h 31, h 30, h 29, h 28, h 27, h 26, h 25, h 24, h 23, h 22, h 21, h 20, h 19, h 18, h 17, h 16, h 15, h 14, h 13, h 12, h 11, h 10, h 9, h 8, h 7, h 6, h 5, h 4, h 3, h 2, h 1, h 0⟩

theorem boolByte_normalized (p : Bool) :
    (BitVec.ofBool p).setWidth 8 = 0 ∨ (BitVec.ofBool p).setWidth 8 = 1 := by
  cases p <;> decide

/-- The helper always returns a normalized subtle Choice byte. -/
theorem comparison_normalized (s : GlobalState) (a b : Pointer) :
    comparison s a b = 0 ∨ comparison s a b = 1 := by
  simp only [comparison, equalByte, boolByte_and_one, boolByte_and]
  exact boolByte_normalized _

theorem read_byte (s : GlobalState) (p : Pointer) (h : SmallRange s.mem p 32)
    (i : Fin 32) :
    s.mem.readAt (p.add (BitVec.ofNat 64 i.val)) 8 =
      (s.mem.readAt p 256).extractLsb' (i.val * 8) 8 := by
  have hi : i.val < 18446744073709551616 := by omega
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] using
    (MemoryState.readAt_add_of_readAt (w := 8) h.fits (h.no_wrap (k := i.val) (by omega))
      (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; omega) rfl)

theorem read_eq_iff_bytes (s : GlobalState) (a b : Pointer)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32) :
    s.mem.readAt a 256 = s.mem.readAt b 256 ↔ ∀ i : Fin 32,
      s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8 =
        s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 := by
  constructor
  · intro h i
    rw [read_byte s a ha i, read_byte s b hb i, h]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hbyte := h ⟨k / 8, by omega⟩
    rw [read_byte s a ha, read_byte s b hb] at hbyte
    have hbit := congrArg (fun x : BitVec 8 => x.getLsbD (k % 8)) hbyte
    have hmod : k % 8 < 8 := Nat.mod_lt _ (by decide)
    have hindex : k / 8 * 8 + k % 8 = k := by omega
    simpa [BitVec.getLsbD_extractLsb', hmod, hindex] using hbit

/-- Exact comparison result including rejection of any unequal byte strings. -/
theorem comparison_exact (s : GlobalState) (a b : Pointer)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32) :
    comparison s a b = if s.mem.readAt a 256 = s.mem.readAt b 256 then 1 else 0 := by
  have hone := (comparison_eq_one_iff s a b).trans (read_eq_iff_bytes s a b ha hb).symm
  split_ifs with h
  · exact hone.mpr h
  · rcases comparison_normalized s a b with hz | ho
    · exact hz
    · exact False.elim (h (hone.mp ho))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Exact execution of all 32 comparisons and 33 concrete black_box calls. -/
theorem program_call (a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32) :
    (program bytesEqPrimitives).call (program.args (.value a) (.value b)) s =
      .value (.cons (.value (comparison s a b)) .nil,
        { s with alloc := ⟨s.alloc.nextFreeBlock + 33⟩ }) := by
  have ha0 := ha.fits_add (k := 0) (count := 1) (by decide)
  have ha1 := ha.fits_add (k := 1) (count := 1) (by decide)
  have ha2 := ha.fits_add (k := 2) (count := 1) (by decide)
  have ha3 := ha.fits_add (k := 3) (count := 1) (by decide)
  have ha4 := ha.fits_add (k := 4) (count := 1) (by decide)
  have ha5 := ha.fits_add (k := 5) (count := 1) (by decide)
  have ha6 := ha.fits_add (k := 6) (count := 1) (by decide)
  have ha7 := ha.fits_add (k := 7) (count := 1) (by decide)
  have ha8 := ha.fits_add (k := 8) (count := 1) (by decide)
  have ha9 := ha.fits_add (k := 9) (count := 1) (by decide)
  have ha10 := ha.fits_add (k := 10) (count := 1) (by decide)
  have ha11 := ha.fits_add (k := 11) (count := 1) (by decide)
  have ha12 := ha.fits_add (k := 12) (count := 1) (by decide)
  have ha13 := ha.fits_add (k := 13) (count := 1) (by decide)
  have ha14 := ha.fits_add (k := 14) (count := 1) (by decide)
  have ha15 := ha.fits_add (k := 15) (count := 1) (by decide)
  have ha16 := ha.fits_add (k := 16) (count := 1) (by decide)
  have ha17 := ha.fits_add (k := 17) (count := 1) (by decide)
  have ha18 := ha.fits_add (k := 18) (count := 1) (by decide)
  have ha19 := ha.fits_add (k := 19) (count := 1) (by decide)
  have ha20 := ha.fits_add (k := 20) (count := 1) (by decide)
  have ha21 := ha.fits_add (k := 21) (count := 1) (by decide)
  have ha22 := ha.fits_add (k := 22) (count := 1) (by decide)
  have ha23 := ha.fits_add (k := 23) (count := 1) (by decide)
  have ha24 := ha.fits_add (k := 24) (count := 1) (by decide)
  have ha25 := ha.fits_add (k := 25) (count := 1) (by decide)
  have ha26 := ha.fits_add (k := 26) (count := 1) (by decide)
  have ha27 := ha.fits_add (k := 27) (count := 1) (by decide)
  have ha28 := ha.fits_add (k := 28) (count := 1) (by decide)
  have ha29 := ha.fits_add (k := 29) (count := 1) (by decide)
  have ha30 := ha.fits_add (k := 30) (count := 1) (by decide)
  have ha31 := ha.fits_add (k := 31) (count := 1) (by decide)
  have hb0 := hb.fits_add (k := 0) (count := 1) (by decide)
  have hb1 := hb.fits_add (k := 1) (count := 1) (by decide)
  have hb2 := hb.fits_add (k := 2) (count := 1) (by decide)
  have hb3 := hb.fits_add (k := 3) (count := 1) (by decide)
  have hb4 := hb.fits_add (k := 4) (count := 1) (by decide)
  have hb5 := hb.fits_add (k := 5) (count := 1) (by decide)
  have hb6 := hb.fits_add (k := 6) (count := 1) (by decide)
  have hb7 := hb.fits_add (k := 7) (count := 1) (by decide)
  have hb8 := hb.fits_add (k := 8) (count := 1) (by decide)
  have hb9 := hb.fits_add (k := 9) (count := 1) (by decide)
  have hb10 := hb.fits_add (k := 10) (count := 1) (by decide)
  have hb11 := hb.fits_add (k := 11) (count := 1) (by decide)
  have hb12 := hb.fits_add (k := 12) (count := 1) (by decide)
  have hb13 := hb.fits_add (k := 13) (count := 1) (by decide)
  have hb14 := hb.fits_add (k := 14) (count := 1) (by decide)
  have hb15 := hb.fits_add (k := 15) (count := 1) (by decide)
  have hb16 := hb.fits_add (k := 16) (count := 1) (by decide)
  have hb17 := hb.fits_add (k := 17) (count := 1) (by decide)
  have hb18 := hb.fits_add (k := 18) (count := 1) (by decide)
  have hb19 := hb.fits_add (k := 19) (count := 1) (by decide)
  have hb20 := hb.fits_add (k := 20) (count := 1) (by decide)
  have hb21 := hb.fits_add (k := 21) (count := 1) (by decide)
  have hb22 := hb.fits_add (k := 22) (count := 1) (by decide)
  have hb23 := hb.fits_add (k := 23) (count := 1) (by decide)
  have hb24 := hb.fits_add (k := 24) (count := 1) (by decide)
  have hb25 := hb.fits_add (k := 25) (count := 1) (by decide)
  have hb26 := hb.fits_add (k := 26) (count := 1) (by decide)
  have hb27 := hb.fits_add (k := 27) (count := 1) (by decide)
  have hb28 := hb.fits_add (k := 28) (count := 1) (by decide)
  have hb29 := hb.fits_add (k := 29) (count := 1) (by decide)
  have hb30 := hb.fits_add (k := 30) (count := 1) (by decide)
  have hb31 := hb.fits_add (k := 31) (count := 1) (by decide)
  simp only [Pointer.add_zero] at ha0 hb0
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_pure
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 1) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 2) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 3) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 4) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 5) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 6) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 7) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 8) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 9) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 10) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 11) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 12) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 13) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 14) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 15) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 17) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 18) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 19) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 20) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 21) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 22) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 23) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 25) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 26) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 27) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 28) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 29) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 30) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  have hgep := ha.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  have hgep := hb.gep (k := 31) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  try simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset]
  clear hgep
  step_load inline
  step_load inline
  step_pure
  step_pure
  step_call using BlackBox.program_call
  step_pure
  step_call using BlackBox.program_call
  finish_block
  rw [hS]
  erase_frame
  subst_vars
  simp [comparison, equalByte, GlobalState.alloca, Pointer.add, Nat.add_assoc]

/-- Complete helper refinement: normal return, exact equality decision, unchanged
memory, and exactly 33 reclaimed stack allocations. -/
theorem program_exact (a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (ha : SmallRange s.mem a 32) (hb : SmallRange s.mem b 32) :
    (program bytesEqPrimitives).call (program.args (.value a) (.value b)) s =
      .value (.cons (.value (if s.mem.readAt a 256 = s.mem.readAt b 256 then 1 else 0)) .nil,
        { s with alloc := ⟨s.alloc.nextFreeBlock + 33⟩ }) := by
  rw [program_call a b s hwf ha hb, comparison_exact s a b ha hb]

end Agave.Ed25519.Encoding.Decompress.Execution.BytesEq
