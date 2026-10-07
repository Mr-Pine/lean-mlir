import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignCompose

/-! Exact word meaning of the emitted conditional-negation stores. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

def selectedWords (byte : BitVec 8) (x : Words) : Words := ![
  signChoose byte (x 0) (negativeZero x),
  signChoose byte (x 1) (negativeOne x),
  signChoose byte (x 2) (negativeTwo x),
  signChoose byte (x 3) (negativeThree x),
  signChoose byte (x 4) (negativeFour x)]

theorem selectedWords_eq (byte : BitVec 8) (x : Words) :
    selectedWords byte x = signedWords byte[7] x := by
  funext i
  fin_cases i <;> simp only [selectedWords,signedWords,selectWord,
    negativeZero,negativeOne,negativeTwo,negativeThree,negativeFour,negativeBias,negativeLow,
    emittedNegativeWords,signChoose,signMask,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val,BitVec.add_comm]
  all_goals rfl

theorem signedState_eq (s : GlobalState) (r : Pointer) (byte : BitVec 8) :
    signedState s r byte =
      {s with mem := storeVectorLimbs s.mem r (signedWords byte[7] (readLimbs s r))} := by
  rw [← selectedWords_eq]
  simp only [signedState,signLastState,signLowState,signFirstState,storeVectorLimbs,
    pack_pair,selectedWords,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]

theorem signed_readback (s : GlobalState) (r : Pointer) (byte : BitVec 8)
    (hr : SmallRange s.mem r 40) :
    readLimbs (signedState s r byte) r = signedWords byte[7] (readLimbs s r) := by
  rw [signedState_eq]
  exact storeVectorLimbs_readLimbs s r _ hr

theorem signed_read320 (s : GlobalState) (r : Pointer) (byte : BitVec 8)
    (hr : SmallRange s.mem r 40) :
    (signedState s r byte).mem.readAt r 320 =
      fieldPayload (signedWords byte[7] (readLimbs s r)) := by
  rw [signedState_eq]
  exact storeVectorLimbs_read320 s.mem r _ hr

theorem signed_live (s : GlobalState) (r q : Pointer) (byte : BitVec 8)
    (h : SmallRange s.mem q n) : SmallRange (signedState s r byte).mem q n :=
  ((h.storeAt _ _).storeAt _ _).storeAt _ _

theorem signed_read_ne (s : GlobalState) (r q : Pointer) (byte : BitVec 8)
    (bits : Nat) (hd : r.id ≠ q.id) :
    (signedState s r byte).mem.readAt q bits = s.mem.readAt q bits := by
  rw [signedState_eq]
  change (storeVectorLimbs s.mem r _).readAt q bits = _
  unfold storeVectorLimbs
  rw [MemoryState.readAt_storeAt_disjoint
    (p := r.add 24#64) (q := q) (w := bits) (Or.inl hd)]
  rw [MemoryState.readAt_storeAt_disjoint (p := r) (q := q) (w := bits) (Or.inl hd)]
  exact MemoryState.readAt_storeAt_disjoint
    (p := r.add 8#64) (q := q) (m := s.mem) (w := bits) (Or.inl hd) _

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
