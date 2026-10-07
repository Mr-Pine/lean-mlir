import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline956Segments
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline956Semantic
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixOperations

/-! The exact final sqrt-ratio inline tail. The only incoming facts concern
registers, live memory and the two candidate limb arrays at pc956. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
open LeanMLIR.RIR SerialFieldMul SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open Decode.InlinePrefix (vector_two carry_operation carry_vector_operation fold_operation)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem segment_append (f : Func) (block : Fin f.n) (first n m : Nat)
    (E : Env f.Γ) :
    Cutpoint.segment f block first (n + m) E = (do
      let F ← Cutpoint.segment f block first n E
      Cutpoint.segment f block (first + n) m F) := by
  unfold Cutpoint.segment
  rw [List.take_add, List.foldlM_append]
  simp only [List.drop_drop]

theorem pack_pair (a b : BitVec 64) : BitVec.packLanes #v[a, b] = b ++ a := by
  change (0#0 ++ b) ++ a = b ++ a
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

def storeRoot (m : MemoryState) (r : Pointer) (a : Words) : MemoryState :=
  ((m.storeAt r (a 0)).storeAt (r.add 8#64) (a 2 ++ a 1)).storeAt
    (r.add 24#64) (a 4 ++ a 3)

def tailState (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words) : GlobalState :=
  {alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
   mem := storeRoot s.mem r (rootWords r t b x y)}

theorem inline72 (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40)
    (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 956 72 E s =
      .value (env1028 E r t b x y, s) := by
  rw [show 72 = 1 + 71 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment956 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 71 = 1 + 70 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment957 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 70 = 4 + 66 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment958 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 66 = 4 + 62 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment962 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 62 = 4 + 58 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment966 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 58 = 4 + 54 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment970 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 54 = 4 + 50 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment974 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 50 = 4 + 46 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment978 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 46 = 1 + 45 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment982 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 45 = 1 + 44 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment983 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 44 = 1 + 43 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment984 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 43 = 1 + 42 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment985 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 42 = 4 + 38 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment986 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 38 = 1 + 37 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment990 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 37 = 1 + 36 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment991 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 36 = 3 + 33 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment992 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 33 = 4 + 29 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment995 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 29 = 4 + 25 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment999 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 25 = 1 + 24 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1003 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 24 = 1 + 23 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1004 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 23 = 1 + 22 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1005 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 22 = 1 + 21 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1006 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 21 = 4 + 17 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1007 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 17 = 1 + 16 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1011 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 16 = 1 + 15 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1012 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 15 = 1 + 14 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1013 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 14 = 1 + 13 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1014 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 13 = 1 + 12 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1015 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 12 = 1 + 11 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1016 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 11 = 1 + 10 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1017 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 10 = 1 + 9 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1018 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 9 = 1 + 8 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1019 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 8 = 1 + 7 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1020 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 7 = 1 + 6 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1021 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 6 = 1 + 5 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1022 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 5 = 1 + 4 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1023 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 4 = 1 + 3 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1024 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  rw [show 3 = 1 + 2 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1025 g E s r t b x y he hwf hr ht hx hy, PoisonOr.value_bind]
  exact segment1026 g E s r t b x y he hwf hr ht hx hy

theorem final18 (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hr : SmallRange s.mem r 40) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1029 18
      (env1029 E r t b x y) s =
      .value (env1047 E r t b x y, {s with mem := storeRoot s.mem r (rootWords r t b x y)}) := by
  rw [show 18 = 1 + 17 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1029 g E (s) r t b x y he, PoisonOr.value_bind]
  rw [show 17 = 1 + 16 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1030 g E (s) r t b x y he, PoisonOr.value_bind]
  rw [show 16 = 1 + 15 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1031 g E (s) r t b x y he, PoisonOr.value_bind]
  rw [show 15 = 1 + 14 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1032 g E (s) r t b x y he, PoisonOr.value_bind]
  rw [show 14 = 1 + 13 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1033 g E (s) r t b x y he, PoisonOr.value_bind]
  rw [show 13 = 3 + 10 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1034 g E (s) r t b x y he, PoisonOr.value_bind]
  rw [show 10 = 1 + 9 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1037 g E (s) r t b x y he (hr), PoisonOr.value_bind]
  rw [show 9 = 4 + 5 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1038 g E ({s with mem := (s).mem.storeAt (r) (v814 r t b x y)}) r t b x y he, PoisonOr.value_bind]
  rw [show 5 = 1 + 4 from rfl, segment_append]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1042 g E ({s with mem := (s).mem.storeAt (r) (v814 r t b x y)}) r t b x y he ((hr).storeAt _ _), PoisonOr.value_bind]
  simp only [Nat.reduceAdd, EffectM.bind_eq, segment1043 g E ({{s with mem := (s).mem.storeAt (r) (v814 r t b x y)} with mem := ({s with mem := (s).mem.storeAt (r) (v814 r t b x y)}).mem.storeAt ((v736 r t b x y)) (BitVec.packLanes (v818 r t b x y))}) r t b x y he (((hr).storeAt _ _).storeAt _ _), PoisonOr.value_bind]
  simp [storeRoot,rootWords,pack_pair,v736,v738,
    v818,v821,GlobalState.alloca_alloc]

/-- All 91 original instructions, including the actual imported black_box call. -/
theorem tail91 (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40)
    (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 956 91 E s =
      .value (env1047 E r t b x y, tailState s r t b x y) := by
  rw [show 91 = 72 + 19 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,inline72 g E s r t b x y he hwf hr ht hx hy,
    PoisonOr.value_bind]
  rw [show 19 = 1 + 18 from rfl, segment_append]
  simp only [Nat.reduceAdd,EffectM.bind_eq,segment1028 g E s r t b x y he hwf,
    PoisonOr.value_bind]
  exact final18 g E {s with alloc := (s.alloca 1).alloc} r t b x y he hr

/-- Compact cutpoint interface to the existing exact output suffix. -/
theorem cutpoint (g : Globals) (E : Env program.Γ) (s : GlobalState)
    (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40)
    (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.resume (program sqrtRatioPrimitives g) 0 956 E s =
      Cutpoint.resume (program sqrtRatioPrimitives g) 0 1047
        (env1047 E r t b x y) (tailState s r t b x y) :=
  Cutpoint.after_segment _ _ 956 91 _ _ _ _ (tail91 g E s r t b x y he hwf hr ht hx hy)

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
