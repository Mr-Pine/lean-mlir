import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioExecutionPow
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtOutput

/-! Exact finite-source composition, with no assumed prefix execution. The
prefix remains an explicit computation over the original instructions. This
module proves its connection to the checked output suffix and actual call
frame; it does not identify the computed root with the field specification. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

namespace OuterComposition

/-- Expose a finite source segment without assuming its result or termination. -/
theorem resume_segment (f : Func) (block : Fin f.n) (first count : Nat)
    (E : ⟪f.Γ⟫) :
    Cutpoint.resume f block first E = (do
      let E' ← Cutpoint.segment f block first count E
      Cutpoint.resume f block (first + count) E') := by
  have hb : (f.blocks block).runBodyFrom E first = (do
      let E' ← Cutpoint.segment f block first count E
      (f.blocks block).runBodyFrom E' (first + count)) := by
    unfold BasicBlock.runBodyFrom Cutpoint.segment
    conv =>
      lhs
      rw [← List.take_append_drop count ((f.blocks block).body.drop first)]
    rw [List.foldlM_append, List.drop_drop]
  funext s
  simp only [Cutpoint.resume, hb, EffectM.bind_eq, bind_assoc]

/-- Sequential original-source slices, ending before the separately proved suffix. -/
def pieces (f : Func) (block : Fin f.n) : Nat → List Nat → ⟪f.Γ⟫ → EffectM ⟪f.Γ⟫
  | _, [], E => pure E
  | first, count :: rest, E => do
      let E' ← Cutpoint.segment f block first count E
      pieces f block (first + count) rest E'

theorem resume_pieces (f : Func) (block : Fin f.n) (first : Nat)
    (counts : List Nat) (E : ⟪f.Γ⟫) :
    Cutpoint.resume f block first E = (do
      let E' ← pieces f block first counts E
      Cutpoint.resume f block (first + counts.sum) E') := by
  induction counts generalizing first E with
  | nil => simp only [pieces, List.sum_nil, Nat.add_zero, pure_bind]
  | cons count rest ih =>
    rw [resume_segment f block first count E]
    simp only [pieces, List.sum_cons, bind_assoc]
    congr 1
    funext E'
    simpa only [Nat.add_assoc] using ih (first + count) E'

end OuterComposition

namespace SqrtRatio
open Reduce64.Execution (SmallRange)

/-- Each singleton is an original external-call instruction. The intervening
counts are the original inline regions, in source order. The last output call
at1048 is already discharged by `output_run`. -/
def executionPieceLengths : List Nat :=
  [86, 1, 0, 1, 3, 1, 0, 1, 2, 1, 2, 1, 1, 1, 4, 1, 0, 1, 2, 1,
   5, 1, 0, 1, 189, 1, 0, 1, 261, 1, 6, 1, 370, 1, 5, 1, 1, 1, 72, 1, 18]

theorem executionPieceLengths_sum : executionPieceLengths.sum = 1047 := by decide

noncomputable def executionPrefix (g : Globals) (E : ⟪program.Γ⟫) : EffectM ⟪program.Γ⟫ :=
  OuterComposition.pieces (program sqrtRatioPrimitives g) 0 0 executionPieceLengths E

structure ExecutionOutputData where
  root : Pointer
  first : BitVec 8
  second : BitVec 8

/-- Concrete suffix readiness: register values, live ranges, noalias and WF.
No field equality or execution equation is a field. -/
structure ExecutionOutputReady (E : ⟪program.Γ⟫) (s : GlobalState)
    (out : Pointer) (d : ExecutionOutputData) : Prop where
  wf : s.WF
  outputLive : SmallRange s.mem out 48
  rootLive : SmallRange s.mem d.root 40
  disjoint : (Range.of out 384).Disjoint (Range.of d.root 320)
  outputRegister : E.read (%arg0) = .value out
  rootRegister : E.read (%79) = .value d.root
  firstRegister : E.read (%430) = .value d.first
  secondRegister : E.read (%236) = .value d.second
  eightRegister : E.read (%3) = .value 8#64
  fortyRegister : E.read (%1) = .value 40#64

theorem executionPrefix_resume (g : Globals) (E : ⟪program.Γ⟫) :
    (program sqrtRatioPrimitives g).runFrom E 0 = (do
      let E' ← executionPrefix g E
      Cutpoint.resume (program sqrtRatioPrimitives g) 0 1047 E') := by
  funext s
  rw [← Cutpoint.zero]
  exact congrFun (by simpa only [executionPrefix, executionPieceLengths_sum, Nat.zero_add] using
    OuterComposition.resume_pieces (program sqrtRatioPrimitives g) 0 0 executionPieceLengths E) s

/-- Exact run observation, including poison from the finite prefix. Readiness
is required only for states actually produced by that prefix. -/
theorem execution_run (g : Globals) (E : ⟪program.Γ⟫) (s : GlobalState)
    (out : Pointer) (data : ⟪program.Γ⟫ → GlobalState → ExecutionOutputData)
    (hready : ∀ E' t, executionPrefix g E s = .value (E', t) →
      ExecutionOutputReady E' t out (data E' t)) :
    (program sqrtRatioPrimitives g).runFrom E 0 s =
      (executionPrefix g E s >>= fun (E', t) =>
        .value (.nil, outputState t out ((data E' t).first ||| (data E' t).second)
          (t.mem.readAt (data E' t).root 320))) := by
  rw [executionPrefix_resume]
  simp only [EffectM.bind_eq]
  cases hp : executionPrefix g E s with
  | poison => simp only [LeanMLIR.RIR.PoisonOr.poison_bind]
  | value value =>
    rcases value with ⟨E', t⟩
    simp only [LeanMLIR.RIR.PoisonOr.value_bind]
    have hr := hready E' t hp
    exact output_run g E' t out (data E' t).root (data E' t).first
      (data E' t).second hr.wf hr.outputLive hr.rootLive hr.disjoint
      hr.outputRegister hr.rootRegister hr.firstRegister hr.secondRegister
      hr.eightRegister hr.fortyRegister

/-- The actual outer frame erase is retained after the checked sqrt output stores. -/
theorem execution_call (g : Globals) (out u v : Pointer) (s : GlobalState)
    (data : ⟪program.Γ⟫ → GlobalState → ExecutionOutputData)
    (hready : ∀ E' t,
      executionPrefix g (Env.init (program.args (.value out) (.value u) (.value v)).get) s =
          .value (E', t) → ExecutionOutputReady E' t out (data E' t)) :
    (program sqrtRatioPrimitives g).call
        (program.args (.value out) (.value u) (.value v)) s =
      (executionPrefix g (Env.init (program.args (.value out) (.value u) (.value v)).get) s >>=
        fun (E', t) =>
          let result := outputState t out ((data E' t).first ||| (data E' t).second)
            (t.mem.readAt (data E' t).root 320)
          .value (.nil, {result with mem := result.mem.eraseFrom s.alloc.nextFreeBlock})) := by
  have hr := execution_run g
    (Env.init (program.args (.value out) (.value u) (.value v)).get) s out data hready
  rw [Func.call_eq_run_bind, Func.run_runFrom_eq]
  change ((program sqrtRatioPrimitives g).runFrom
    (Env.init (program.args (.value out) (.value u) (.value v)).get) 0 s >>= fun p =>
      .value (p.1, {p.2 with mem := p.2.mem.eraseFrom s.alloc.nextFreeBlock})) = _
  rw [hr]
  simp only [bind_assoc, LeanMLIR.RIR.PoisonOr.value_bind]

end SqrtRatio
end Agave.Ed25519.Encoding.Decompress.Execution
