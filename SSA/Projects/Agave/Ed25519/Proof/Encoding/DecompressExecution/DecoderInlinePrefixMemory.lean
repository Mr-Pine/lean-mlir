import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixCompose

/-! Caller observations and exact numerator readback of the executed prefix. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

theorem erase_get (m : MemoryState) (id : BlockId) (n : Nat) (h : id.id < n) :
    (m.eraseFrom n)[id]? = m[id]? := by
  simp [MemoryState.eraseFrom, MemoryState.getElem?_eq, Std.ExtHashMap.getElem?_filter', h]
  cases m.mem[id]? <;> rfl

theorem private_get (h : PrivateFrame before after) (id : BlockId)
    (hi : id.id < before.alloc.nextFreeBlock) : after.mem[id]? = before.mem[id]? := by
  have hm := congrArg (fun m : MemoryState => m[id]?) h.memory
  rwa [erase_get _ _ _ hi] at hm

theorem private_read (h : PrivateFrame before after) (q : Pointer) (bits : Nat)
    (hi : q.id.id < before.alloc.nextFreeBlock) :
    after.mem.readAt q bits = before.mem.readAt q bits := by
  simp only [MemoryState.readAt, private_get h q.id hi]

theorem private_live (h : PrivateFrame before after) (hwf : before.WF)
    (hp : SmallRange before.mem q n) : SmallRange after.mem q n := by
  have hi := hwf.lt hp.fits.mem
  rcases hp with ⟨b, hb, hs, hz⟩
  exact ⟨b, (private_get h q.id hi).trans hb, hs, hz⟩

theorem private_ready (h : PrivateFrame before after) (hwf : before.WF)
    (ready : Ready dg sg before) : Ready dg sg after := by
  constructor
  · exact ⟨private_live h hwf ready.curveD.1,
      (private_read h dg.address0 320 (hwf.lt ready.curveD.1.fits.mem)).trans ready.curveD.2⟩
  · exact ⟨private_live h hwf ready.sqrtM1.1,
      (private_read h sg.address0 320 (hwf.lt ready.sqrtM1.1.fits.mem)).trans ready.sqrtM1.2⟩

theorem carry_state_eq (s : GlobalState) (r : Pointer) (x : Words) :
    carryResultState (carryOneState s r x) r x =
      {s with mem := storeVectorLimbs s.mem r (numeratorMachine x)} := by
  simp only [carryResultState, carryOneState, storeVectorLimbs, pack_pair,
    carryOne, carryTwo, carryThree, carryFour, carryZero, numeratorMachine, SerialPoint.weakWord]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.head_cons, BitVec.add_comm]
  rfl

theorem numerator_readback (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    readLimbs (numeratorState s input) (slot3 s) = (numeratorWord bytes).limbs := by
  unfold numeratorState
  rw [carry_state_eq, storeVectorLimbs_readLimbs _ _ _
    (square_live s input _ _ (slot3_live s hwf)), square_readback s input bytes hwf hin,
    numeratorMachine_eq]
  rfl

theorem carry_result_read_ne (s : GlobalState) (r a : Pointer) (x : Words)
    (hd : r.id ≠ a.id) :
    readLimbs (carryResultState (carryOneState s r x) r x) a = readLimbs s a := by
  rw [carry_state_eq]
  funext i
  let q := a.add (BitVec.ofNat 64 (8 * i.val))
  change (storeVectorLimbs s.mem r (numeratorMachine x)).readAt q 64 = s.mem.readAt q 64
  unfold storeVectorLimbs
  rw [MemoryState.readAt_storeAt_disjoint
    (p := r.add 24#64) (q := q) (w := 64) (Or.inl hd)]
  rw [MemoryState.readAt_storeAt_disjoint (p := r) (q := q) (w := 64) (Or.inl hd)]
  exact MemoryState.readAt_storeAt_disjoint
    (p := r.add 8#64) (q := q) (m := s.mem) (w := 64) (Or.inl hd) _

theorem numerator_square_readback (s : GlobalState) (input : Pointer) (bytes : BitVec 256)
    (hwf : s.WF) (hin : Verifier.Execution.Dalek.ReadBytes s input 32 bytes) :
    readLimbs (numeratorState s input) (slot4 s) = ((parsedWord bytes).square 1).limbs := by
  unfold numeratorState
  rw [carry_result_read_ne]
  · exact square_readback s input bytes hwf hin
  · intro h
    have := congrArg BlockId.id h
    simp only [slot3_id, slot4_id] at this
    omega

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
