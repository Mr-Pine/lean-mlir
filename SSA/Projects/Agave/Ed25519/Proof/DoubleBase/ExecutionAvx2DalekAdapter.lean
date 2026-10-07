import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapterOutput
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Correctness
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.PointRepresentation

/-! The AVX2-to-Dalek adapter preserves concrete execution, exact output bytes,
all caller-visible memory, and the tight group representative. Its remaining
execution premises are the constructor and five individual arithmetic blocks. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F Represents)
open Reduce64.Execution (SmallRange)
open Conformance.BackendExecution (Invocation readPoint)
open Verifier Verifier.Execution
set_option maxRecDepth 10000

/-- The extra memory fact is maintained at each arithmetic block boundary;
register-only control blocks preserve it without an execution premise. -/
def DalekContext (i : Conformance.BackendExecution.Invocation) (initial : GlobalState) : LocalContext := fun E s =>
  BackendReady i.output (avx2StackPtr initial 27) (stackSetupSlots initial)
    (readPoint initial i.pointA) E s ∧ CallerFrame initial s i.output

theorem dalekContext_stable (i : Conformance.BackendExecution.Invocation) (s : GlobalState) :
    ContextStable (DalekContext i s) := by
  intro E E' state hf h
  exact ⟨backendReady_stable E E' state hf h.1, h.2⟩

/-- The real prefix's retained observations establish the chosen loop
invariant. This predicate contains no backend or loop execution assertion. -/
def PrefixContext (g : Avx2CFG.Globals) (i : Conformance.BackendExecution.Invocation)
    (s : GlobalState) (ctx : LocalContext) : Prop :=
  ∀ ES st,
    RegisterFrame 268 421 (entryLoopEnv (Env.init i.args.get) g s) ES →
    TableFrame (prefixState s (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256))
      st (avx2StackPtr s 27) →
    (∀ k : Fin 8,
      Avx2PointAdd.pointReduced (packedPoint st.mem
        ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))) ∧
      Avx2PointAdd.pointValue (packedPoint st.mem
        ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))) =
        avx2Cache (Tables.avx2Width5 (readPoint s i.pointA) k)) →
    ctx (tableSetupResult ES (stackSetupSlots s) (avx2StackPtr s 27)
      (scalarStartIndex (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256))) st

theorem prefix_dalekContext (g : Avx2CFG.Globals)
    (i : Conformance.BackendExecution.Invocation) (s : GlobalState) (hinput : Input i s) :
    PrefixContext g i s (DalekContext i s) := by
  intro ES st hf ht hv
  exact ⟨prefix_backendReady g i s hinput ES st hf ht hv,
    prefix_callerFrame s _ _ hinput.wellFormed ht⟩

set_option maxHeartbeats 1000000 in
/-- Actual entry, constructor, descending ladder and return, with both the
frame and a valid machine representation retained through function return. -/
theorem backend_validPoint_of_local_blocks
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals) (htable : TableContract p.call0)
    (i : Conformance.BackendExecution.Invocation) (s : GlobalState) (hinput : Input i s)
    (ctx : LocalContext) (hstable : ContextStable ctx)
    (hcontext : ∀ E st, ctx E st → DalekContext i s E st)
    (hc : ArithmeticBlocks p g ctx
      (s.mem.readAt i.scalarA 256).toNat (s.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr s 29) (avx2StackPtr s 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint s i.pointA))))
    (hinitial : PrefixContext g i s ctx)
    (V : GroupPoint) (hA : Represents (readPoint s i.pointA) V)
    (ha : (s.mem.readAt i.scalarA 256).toNat < 2^255)
    (hb : (s.mem.readAt i.scalarB 256).toNat < 2^255) :
    ∃ (P : ValidPoint) (after : GlobalState),
      (avx2Kernel p g).call i.args s = .value (.nil, after) ∧
      Dalek.OutputFrame s after i.output 160 ∧
      P.curve = (s.mem.readAt i.scalarA 256).toNat • V +
        (s.mem.readAt i.scalarB 256).toNat • Tables.baseGroup ∧
      Dalek.ReadBytes after i.output 160 P.bytes := by
  let a := s.mem.readAt i.scalarA 256
  let b := s.mem.readAt i.scalarB 256
  let E : ⟪avx2Kernel.Γ⟫ := Env.init i.args.get
  obtain ⟨ES, st, hprefix, hframe, htableFrame, hvalues⟩ := prefix_to_ladder_run p g htable
    E s i.scalarA i.scalarB i.pointA a b hinput.wellFormed hinput.scalarA hinput.scalarB
    hinput.pointA hinput.pointLimbs rfl rfl
    (by simp [E, Env.init, Conformance.BackendExecution.Invocation.args])
    (by simp [E, Env.init, Conformance.BackendExecution.Invocation.args])
    (by simp [E, Env.init, Conformance.BackendExecution.Invocation.args])
  let EL := tableSetupResult ES (stackSetupSlots s) (avx2StackPtr s 27) (scalarStartIndex a b)
  have hcontrolES : ControlReady ES (avx2StackPtr s 29) (avx2StackPtr s 28) := by
    refine ⟨(hframe.read (%1) (by decide)).trans ?_,
      (hframe.read (%4) (by decide)).trans ?_,
      (hframe.read (%10) (by decide)).trans ?_,
      (hframe.read (%19) (by decide)).trans ?_,
      (hframe.read (%117) (by decide)).trans ?_,
      (hframe.read (%222) (by decide)).trans ?_,
      (hframe.read (%266) (by decide)).trans ?_,
      (hframe.read (%265) (by decide)).trans ?_⟩
    all_goals simp [entryLoopEnv, avx2EntryEnv, mlir_env]
  have hcontrol : ControlReady EL (avx2StackPtr s 29) (avx2StackPtr s 28) := by
    rcases hcontrolES with ⟨h1, h4, h10, h19, h117, h222, h266, h265⟩
    constructor <;> simp [EL, tableSetupResult, tableSetupInput, mlir_env,
      h1, h4, h10, h19, h117, h222, h266, h265]
  have hdigits : DigitMemory st (avx2StackPtr s 29) (avx2StackPtr s 28) a.toNat b.toNat :=
    (prefixState_digits s a b hinput.wellFormed).of_tableFrame htableFrame
      (avx2Stack_separate s 29 27 (by decide)) (avx2Stack_separate s 28 27 (by decide))
  have hready : LadderReady ctx a.toNat b.toNat (avx2StackPtr s 29) (avx2StackPtr s 28)
      EL st (scalarStartIndex a b) :=
    ⟨hcontrol, by simp [EL, tableSetupResult, mlir_env], hdigits,
      hinitial ES st hframe htableFrame hvalues⟩
  obtain ⟨EF, sf, hrun, hr, hp⟩ := ladder_run hc hstable
    (scalarStartIndex a b).val (scalarStartIndex a b).isLt EL st identityPoint hready
    (tableSetupResult_point ES _ _ _)
  have hmath : Represents
      (run (avx2Step (finiteTable (Tables.avx2DoubleBaseTable (readPoint s i.pointA))))
        (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) (scalarStartIndex a b).val identityPoint)
      (a.toNat • V + b.toNat • Tables.baseGroup) := by
    change Represents (avx2Math a.toNat (readPoint s i.pointA) b.toNat) _
    simpa only [natCast_zsmul] using avx2Math_represents_direct hA a.toNat b.toNat ha hb
  have hfinalContext := hcontext EF sf hr.localContext
  obtain ⟨P, final, hreturn, hframe, hcurve, hbytes⟩ := unpack_run_validPoint p g EF sf
    i.output _ _ hfinalContext.1.wellFormed hfinalContext.1.outputRegisters
      hfinalContext.1.output hp hmath
  have hfull : (avx2Kernel p g).run i.args s = .value (.nil, final) := by
    rw [Func.run_runFrom_eq]
    exact hprefix.trans (hrun.trans hreturn)
  have hcaller : i.output.id.id < s.alloc.nextFreeBlock :=
    hinput.wellFormed.lt hinput.output.fits.mem
  refine ⟨P, {final with mem := final.mem.eraseFrom s.alloc.nextFreeBlock},
    Func.call_of_run hfull,
    (hfinalContext.2.thenOutput hframe).erase hinput.wellFormed, hcurve,
    smallRange_eraseFrom hbytes.1 hcaller, ?_⟩
  exact (readAt_eraseFrom final.mem i.output 1280 hcaller).trans hbytes.2


/-- Actual entry, constructor, descending ladder and return, with both the
frame and a valid machine representation retained through function return. -/
theorem backend_validPoint_of_framed_blocks
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals) (htable : TableContract p.call0)
    (i : Conformance.BackendExecution.Invocation) (s : GlobalState) (hinput : Input i s)
    (hc : ArithmeticBlocks p g (DalekContext i s)
      (s.mem.readAt i.scalarA 256).toNat (s.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr s 29) (avx2StackPtr s 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint s i.pointA))))
    (V : GroupPoint) (hA : Represents (readPoint s i.pointA) V)
    (ha : (s.mem.readAt i.scalarA 256).toNat < 2^255)
    (hb : (s.mem.readAt i.scalarB 256).toNat < 2^255) :
    ∃ (P : ValidPoint) (after : GlobalState),
      (avx2Kernel p g).call i.args s = .value (.nil, after) ∧
      Dalek.OutputFrame s after i.output 160 ∧
      P.curve = (s.mem.readAt i.scalarA 256).toNat • V +
        (s.mem.readAt i.scalarB 256).toNat • Tables.baseGroup ∧
      Dalek.ReadBytes after i.output 160 P.bytes :=
  backend_validPoint_of_local_blocks p g htable i s hinput
    (DalekContext i s) (dalekContext_stable i s) (fun _ _ h => h) hc
    (prefix_dalekContext g i s hinput) V hA ha hb

end Agave.Ed25519.DoubleBase.ExecutionAvx2
