import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixDenominator
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.ReadyValues

/-! Composition of the decoder's checked bounded instruction slices. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul SerialPoint
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open SmallOrder.Execution (PrivateFrame)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

theorem segment_append (f : Func) (block : Fin f.n) (first n m : Nat)
    (E : Env f.Γ) :
    Cutpoint.segment f block first (n + m) E = (do
      let F ← Cutpoint.segment f block first n E
      Cutpoint.segment f block (first + n) m F) := by
  unfold Cutpoint.segment
  rw [List.take_add, List.foldlM_append]
  simp only [List.drop_drop]

theorem carry_read_ne (s : GlobalState) (r a : Pointer) (x : Words)
    (hd : r.id ≠ a.id) : readLimbs (carryOneState s r x) a = readLimbs s a := by
  funext i
  exact MemoryState.readAt_storeAt_disjoint
    (p := r.add 8#64) (q := a.add (BitVec.ofNat 64 (8 * i.val)))
    (m := s.mem) (v := 128) (w := 64) (Or.inl hd) _

theorem numerator_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r a : Pointer) (hr : SmallRange s.mem r 40)
    (ha : SmallRange s.mem a 40) (hd : r.id ≠ a.id)
    (he : NumeratorRegisters E r a) :
    Cutpoint.segment (program p g) 0 74 31 E s =
      .value (carryEndEnv E r a (readLimbs s a),
        carryResultState (carryOneState s r (readLimbs s a)) r (readLimbs s a)) := by
  let x := readLimbs s a
  let t := carryOneState s r x
  have hrt : SmallRange t.mem r 40 := hr.storeAt _ _
  have hat : SmallRange t.mem a 40 := ha.storeAt _ _
  have hxt : readLimbs t a = x := carry_read_ne s r a x hd
  rw [show 31 = 14 + 17 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, numerator_segment_A p g E s r a hr ha he,
    PoisonOr.value_bind]
  rw [show 17 = 2 + 15 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, carry_one_segment p g E s r a (readLimbs s a) hr he,
    PoisonOr.value_bind]
  rw [show 15 = 2 + 13 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, carry_load_segment p g E (carryOneState s r (readLimbs s a)) r a (readLimbs s a) hrt hat hxt he,
    PoisonOr.value_bind]
  rw [show 13 = 3 + 10 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, carry_bias_segment p g E (carryOneState s r (readLimbs s a)) r a (readLimbs s a) he,
    PoisonOr.value_bind]
  rw [show 10 = 2 + 8 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, carry_prep_segment p g E (carryOneState s r (readLimbs s a)) r a (readLimbs s a) he,
    PoisonOr.value_bind]
  rw [show 8 = 2 + 6 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, carry_shuffle_segment p g E (carryOneState s r (readLimbs s a)) r a (readLimbs s a) he,
    PoisonOr.value_bind]
  rw [show 6 = 2 + 4 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, carry_end_segment p g E (carryOneState s r (readLimbs s a)) r a (readLimbs s a) he,
    PoisonOr.value_bind]
  exact carry_store_segment p g E (carryOneState s r (readLimbs s a)) r a (readLimbs s a) hrt he

def numeratorState (s : GlobalState) (input : Pointer) : GlobalState :=
  let x := readLimbs (squareState s input) (slot4 s)
  carryResultState (carryOneState (squareState s input) (slot3 s) x) (slot3 s) x

noncomputable def afterNumeratorEnv (g : Globals) (s : GlobalState)
    (out input : Pointer) : Env program.Γ :=
  carryEndEnv (parseEnv g s out input) (slot3 s) (slot4 s)
    (readLimbs (squareState s input) (slot4 s))

theorem square_live (s : GlobalState) (input q : Pointer) (n : Nat)
    (h : SmallRange (allocated s).mem q n) : SmallRange (squareState s input).mem q n :=
  smallRange_storeLimbs (parse_live s input q n h) _ _

theorem numerator_live (s : GlobalState) (input q : Pointer) (n : Nat)
    (h : SmallRange (allocated s).mem q n) : SmallRange (numeratorState s input).mem q n :=
  (((square_live s input q n h).storeAt _ _).storeAt _ _).storeAt _ _

theorem numerator_frame (s : GlobalState) (input : Pointer) (hwf : s.WF) :
    PrivateFrame s (numeratorState s input) := by
  exact (((square_frame s input hwf).storeAt _ _
    (by simp only [Pointer.add, slot3_id]; omega)).storeAt _ _
    (by simp only [slot3_id]; omega)).storeAt _ _
    (by simp only [Pointer.add, slot3_id]; omega)

theorem through_numerator_segment (g : Globals) (sg : SqrtRatio.Globals)
    (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hin : SmallRange s.mem input 32) :
    Cutpoint.segment (program (decodePrimitives sg) g) 0 0 105 (initialEnv out input) s =
      .value (afterNumeratorEnv g s out input, numeratorState s input) := by
  rw [show 105 = 74 + 31 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, first_square_segment g sg s out input hwf hin,
    PoisonOr.value_bind]
  exact numerator_segment (decodePrimitives sg) g (parseEnv g s out input)
    (squareState s input) (slot3 s) (slot4 s)
    (square_live s input _ _ (slot3_live s hwf))
    (square_live s input _ _ (slot4_live s hwf))
    (by intro h; have := congrArg BlockId.id h; simp only [slot3_id, slot4_id] at this; omega)
    (numerator_registers g s out input)

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
