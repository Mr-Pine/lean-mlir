import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioExecutionComposition
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.PointOutput

/-! Exact composition of the original decoder entry and success prefixes with
its checked decision, output stores, and public call-frame erase. The remaining
prefix computations are explicit source segments, including their poison cases.
The readiness premises contain registers and memory facts, not execution claims. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

noncomputable def outerEntryPrefix (p : Primitives) (g : Globals)
    (E : ⟪program.Γ⟫) : EffectM ⟪program.Γ⟫ :=
  Cutpoint.segment (program p g) 0 0 137 E

noncomputable def outerSuccessPrefix (p : Primitives) (g : Globals)
    (E : ⟪program.Γ⟫) : EffectM ⟪program.Γ⟫ :=
  Cutpoint.segment (program p g) 1 0 50 E

structure OuterSuccessData where
  point : Pointer
  y : Pointer

structure OuterSuccessReady (E : ⟪program.Γ⟫) (s : GlobalState)
    (out : Pointer) (d : OuterSuccessData) : Prop where
  outputRegister : E.read (%arg0) = .value out
  pointRegister : E.read (%36) = .value d.point
  yRegister : E.read (%38) = .value d.y
  fortyRegister : E.read (%19) = .value 40#64
  eightyRegister : E.read (%27) = .value 80#64
  eightyEightRegister : E.read (%28) = .value 88#64
  oneRegister : E.read (%6) = .value 1#64
  zeroRegister : E.read (%20) = .value 0#8
  thirtyTwoRegister : E.read (%10) = .value 32#64
  eightRegister : E.read (%8) = .value 8#64
  oneSixtyRegister : E.read (%29) = .value 160#64
  pointLive : SmallRange s.mem d.point 160
  yLive : SmallRange s.mem d.y 40
  outputLive : SmallRange s.mem out 168
  yDisjoint : (Range.of (d.point.add 40#64) 320).Disjoint (Range.of d.y 320)
  outputDisjoint : (Range.of (out.add 8#64) 1280).Disjoint (Range.of d.point 1280)

structure OuterDecisionReady (E : ⟪program.Γ⟫) (s : GlobalState)
    (out : Pointer) (flag : BitVec 8) : Prop where
  outputRegister : E.read (%arg0) = .value out
  flagRegister : E.read (%93) = .value flag
  zeroRegister : E.read (%20) = .value 0#8
  tagRegister : E.read (%14) = .value 0#64
  outputLive : SmallRange s.mem out 168

def outerSuccessState (s : GlobalState) (out : Pointer) (d : OuterSuccessData) : GlobalState :=
  successState (finishPointState s d.point d.y) out
    (finishPointBits (s.mem.readAt d.point 1280) (s.mem.readAt d.y 320))

def outerSuccessEnv (E : ⟪program.Γ⟫) (flag : BitVec 8) : ⟪program.Γ⟫ :=
  E[%96 := .value (BitVec.ofBool (flag == 0#8))]

noncomputable def outerSuccessResult (p : Primitives) (g : Globals) (out : Pointer)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData) (E : ⟪program.Γ⟫)
    (s : GlobalState) : PoisonOr (Vals [] × GlobalState) :=
  outerSuccessPrefix p g E s >>= fun (E', t) =>
    .value (.nil, outerSuccessState t out (data E' t))

theorem outerSuccess_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out : Pointer)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData)
    (hready : ∀ E' t, outerSuccessPrefix p g E s = .value (E', t) →
      OuterSuccessReady E' t out (data E' t)) :
    (program p g).runFrom E 1 s = outerSuccessResult p g out data E s := by
  rw [← Cutpoint.zero]
  rw [OuterComposition.resume_segment (program p g) 1 0 50 E]
  simp only [EffectM.bind_eq, Nat.zero_add]
  change (outerSuccessPrefix p g E s >>= _) = _
  unfold outerSuccessResult
  cases hp : outerSuccessPrefix p g E s with
  | poison => rfl
  | value value =>
    rcases value with ⟨E', t⟩
    simp only [LeanMLIR.RIR.PoisonOr.value_bind]
    have hr := hready E' t hp
    exact finishPoint_run p g E' t out (data E' t).point (data E' t).y
      hr.outputRegister hr.pointRegister hr.yRegister hr.fortyRegister
      hr.eightyRegister hr.eightyEightRegister hr.oneRegister hr.zeroRegister
      hr.thirtyTwoRegister hr.eightRegister hr.oneSixtyRegister hr.pointLive
      hr.yLive hr.outputLive hr.yDisjoint hr.outputDisjoint

noncomputable def outerDecisionResult (p : Primitives) (g : Globals) (out : Pointer)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData) (E : ⟪program.Γ⟫)
    (s : GlobalState) (flag : BitVec 8) : PoisonOr (Vals [] × GlobalState) :=
  if flag = 0#8 then .value (.nil, rejectionState s out)
  else outerSuccessResult p g out data (outerSuccessEnv E flag) s

theorem outerDecision_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out : Pointer) (flag : BitVec 8)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData)
    (hdecision : OuterDecisionReady E s out flag)
    (hready : flag ≠ 0#8 → ∀ E' t,
      outerSuccessPrefix p g (outerSuccessEnv E flag) s = .value (E', t) →
      OuterSuccessReady E' t out (data E' t)) :
    resume p g 0 137 E s = outerDecisionResult p g out data E s flag := by
  by_cases hflag : flag = 0#8
  · subst flag
    unfold outerDecisionResult
    rw [ite_eq_left rfl]
    exact rejection_run p g E s out hdecision.outputRegister hdecision.flagRegister
      hdecision.zeroRegister hdecision.tagRegister hdecision.outputLive
  · rw [decide_path p g E s flag hdecision.flagRegister hdecision.zeroRegister
      hdecision.tagRegister, ite_eq_right hflag]
    unfold outerDecisionResult
    rw [ite_eq_right hflag]
    exact outerSuccess_run p g (outerSuccessEnv E flag) s out data (hready hflag)

noncomputable def outerResult (p : Primitives) (g : Globals) (out : Pointer)
    (flags : ⟪program.Γ⟫ → GlobalState → BitVec 8)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData) (E : ⟪program.Γ⟫)
    (s : GlobalState) : PoisonOr (Vals [] × GlobalState) :=
  outerEntryPrefix p g E s >>= fun (E', t) =>
    outerDecisionResult p g out data E' t (flags E' t)

theorem outer_run (p : Primitives) (g : Globals) (E : ⟪program.Γ⟫)
    (s : GlobalState) (out : Pointer)
    (flags : ⟪program.Γ⟫ → GlobalState → BitVec 8)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData)
    (hdecision : ∀ E' t, outerEntryPrefix p g E s = .value (E', t) →
      OuterDecisionReady E' t out (flags E' t))
    (hready : ∀ E' t, outerEntryPrefix p g E s = .value (E', t) →
      flags E' t ≠ 0#8 → ∀ E'' u,
        outerSuccessPrefix p g (outerSuccessEnv E' (flags E' t)) t = .value (E'', u) →
        OuterSuccessReady E'' u out (data E'' u)) :
    (program p g).runFrom E 0 s = outerResult p g out flags data E s := by
  rw [← Cutpoint.zero]
  rw [OuterComposition.resume_segment (program p g) 0 0 137 E]
  simp only [EffectM.bind_eq, Nat.zero_add]
  change (outerEntryPrefix p g E s >>= _) = _
  unfold outerResult
  cases hp : outerEntryPrefix p g E s with
  | poison => rfl
  | value value =>
    rcases value with ⟨E', t⟩
    simp only [LeanMLIR.RIR.PoisonOr.value_bind]
    exact outerDecision_run p g E' t out (flags E' t) data
      (hdecision E' t hp) (hready E' t hp)

/-- The public decoder call, including both return branches and erasure of all
allocations in the decoder's call frame. -/
theorem outer_call (p : Primitives) (g : Globals) (out input : Pointer)
    (s : GlobalState)
    (flags : ⟪program.Γ⟫ → GlobalState → BitVec 8)
    (data : ⟪program.Γ⟫ → GlobalState → OuterSuccessData)
    (hdecision : ∀ E' t,
      outerEntryPrefix p g (Env.init (program.args (.value out) (.value input)).get) s =
        .value (E', t) → OuterDecisionReady E' t out (flags E' t))
    (hready : ∀ E' t,
      outerEntryPrefix p g (Env.init (program.args (.value out) (.value input)).get) s =
        .value (E', t) → flags E' t ≠ 0#8 → ∀ E'' u,
        outerSuccessPrefix p g (outerSuccessEnv E' (flags E' t)) t = .value (E'', u) →
        OuterSuccessReady E'' u out (data E'' u)) :
    (program p g).call (program.args (.value out) (.value input)) s =
      (outerResult p g out flags data
        (Env.init (program.args (.value out) (.value input)).get) s >>= fun result =>
          .value (result.1, {result.2 with mem := result.2.mem.eraseFrom s.alloc.nextFreeBlock})) := by
  have hr := outer_run p g
    (Env.init (program.args (.value out) (.value input)).get) s out flags data hdecision hready
  rw [Func.call_eq_run_bind, Func.run_runFrom_eq]
  change ((program p g).runFrom
    (Env.init (program.args (.value out) (.value input)).get) 0 s >>= _) = _
  rw [hr]

end Agave.Ed25519.Encoding.Decompress.Execution.Decode
