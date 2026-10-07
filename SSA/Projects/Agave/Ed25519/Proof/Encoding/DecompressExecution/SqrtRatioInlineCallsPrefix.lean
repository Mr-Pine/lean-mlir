import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsChecked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInlineCallsFrame

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
open Pow22501 (TightWords)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def state117 (s : GlobalState) (u v : Pointer) : GlobalState :=
  callsState s (callWords (readLimbs s u) (readLimbs s v))
    (callExtra (readLimbs s u) (readLimbs s v)) 13

/-- The actual entry and all field calls reach the first inlined serializer.
Only live caller inputs and ordinary memory well-formedness are premises. -/
theorem prefix117 (g : Globals) (E : Env program.Γ) (s : GlobalState) (u v : Pointer)
    (hwf : s.WF) (hu : SmallRange s.mem u 40) (hv : SmallRange s.mem v 40)
    (heu : E.read (%arg1) = .value u) (hev : E.read (%arg2) = .value v) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 0 117 E s =
      .value ((entryResult g E s).1,state117 s u v) := by
  rw [show 117 = 86 + 31 from rfl,segment_append]
  simp only [EffectM.bind_eq,entry_segment,PoisonOr.value_bind]
  rw [entry_state]
  apply arithmetic_calls_segment g s u v (entryResult g E s).1
    (callsState s (callWords (readLimbs s u) (readLimbs s v))
      (callExtra (readLimbs s u) (readLimbs s v)))
  · exact entry_slot g E s
  · change (entryResult g E s).1.args 1 = .value u
    rw [entry_args]
    exact heu
  · change (entryResult g E s).1.args 2 = .value v
    rw [entry_args]
    exact hev
  · exact entry_first_count g E s
  · rfl
  · rfl
  · exact checked_arithmetic_calls s u v hwf hu hv

/-- Arithmetic meaning of the candidate and its checked square at pc117. -/
theorem state117_words (s : GlobalState) (u v : Pointer) (a b : TightWords)
    (hwf : s.WF) (hu : readLimbs s u = a.limbs) (hv : readLimbs s v = b.limbs) :
    readLimbs (state117 s u v) (slot s 17) = (wordCandidate a b).limbs ∧
    readLimbs (state117 s u v) (slot s 13) = (wordCheck a b).limbs := by
  have hc := callsState_words_written s (callWords (readLimbs s u) (readLimbs s v))
    (callExtra (readLimbs s u) (readLimbs s v)) hwf (i := 10) (n := 13) (by decide) (by decide)
  have hd := callsState_words_written s (callWords (readLimbs s u) (readLimbs s v))
    (callExtra (readLimbs s u) (readLimbs s v)) hwf (i := 12) (n := 13) (by decide) (by decide)
  constructor
  · exact hc.trans (by rw [hu,hv,callWords_candidate])
  · exact hd.trans (by rw [hu,hv,callWords_check])

theorem state117_wf (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    (state117 s u v).WF := callsState_wf s _ _ hwf 13

theorem state117_ready (dg : Decode.Globals) (g : Globals) (s : GlobalState)
    (u v : Pointer) (hwf : s.WF) (h : Ready dg g s) : Ready dg g (state117 s u v) :=
  callsState_ready dg g s _ _ hwf h 13

theorem state117_private (s : GlobalState) (u v : Pointer) (hwf : s.WF) :
    (state117 s u v).mem.eraseFrom s.alloc.nextFreeBlock = s.mem ∧
    (state117 s u v).alloc.nextFreeBlock = s.alloc.nextFreeBlock + 42 := by
  refine ⟨callsState_private s _ _ hwf 13, ?_⟩
  simpa only [state117,callsState_counter,ite_true,show 6 < 13 from by decide,Nat.add_assoc]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline
