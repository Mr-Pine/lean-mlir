import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixSignStores

/-! Complete emitted conditional-negation network (bb1:9--46). -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
open LeanMLIR.RIR SerialFieldMul
open SerialPoint.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000

def signedState (s : GlobalState) (r : Pointer) (byte : BitVec 8) : GlobalState :=
  signLastState (signLowState (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r)) r byte (readLimbs s r)

theorem sign_network_segment (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r : Pointer) (byte : BitVec 8) (hr : SmallRange s.mem r 40)
    (he : SignRegisters E r byte) :
    Cutpoint.segment (program p g) 1 9 38 E s =
      .value (signAllSelectedEnv E r byte (readLimbs s r), signedState s r byte) := by
  have hr1 : SmallRange (signFirstState s r byte (readLimbs s r)).mem r 40 := hr.storeAt _ _
  have hr2 : SmallRange (signLowState (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r)).mem r 40 := hr1.storeAt _ _
  have hx3 : (signFirstState s r byte (readLimbs s r)).mem.readAt (r.add 24#64) 64 = (readLimbs s r) 3 :=
    (sign_first_high_read s r byte (readLimbs s r) hr 24 (by decide)).trans rfl
  have hx4 : (signFirstState s r byte (readLimbs s r)).mem.readAt (r.add 32#64) 64 = (readLimbs s r) 4 :=
    (sign_first_high_read s r byte (readLimbs s r) hr 32 (by decide)).trans rfl
  rw [show 38 = 7 + 31 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_load_segment p g E s r byte hr he,PoisonOr.value_bind]
  rw [show 31 = 3 + 28 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_bias_segment p g E s r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 28 = 3 + 25 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_mask_segment p g E s r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 25 = 1 + 24 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_carry_segment p g E s r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 24 = 3 + 21 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_broadcast_segment p g E s r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 21 = 2 + 19 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_selected_segment p g E s r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 19 = 1 + 18 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_first_store_segment p g E s r byte (readLimbs s r) hr,PoisonOr.value_bind]
  rw [show 18 = 1 + 17 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_high_load_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) hr1 hx3 hx4,PoisonOr.value_bind]
  rw [show 17 = 3 + 14 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_highbias_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 14 = 2 + 12 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_highprep_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 12 = 2 + 10 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_highshuffle_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 10 = 1 + 9 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_lowfold_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 9 = 1 + 8 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_highcarry_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 8 = 3 + 5 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_lowselected_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  rw [show 5 = 1 + 4 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_low_store_segment p g E (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r) hr1 he,PoisonOr.value_bind]
  rw [show 4 = 3 + 1 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,sign_allselected_segment p g E (signLowState (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r)) r byte (readLimbs s r) he,PoisonOr.value_bind]
  exact sign_last_store_segment p g E (signLowState (signFirstState s r byte (readLimbs s r)) r byte (readLimbs s r)) r byte (readLimbs s r) hr2

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.InlinePrefix
