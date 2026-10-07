import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.RIR.Run.Tactic.Trace

/-! Exact initialization stores of the pinned scalar C body. The context buffer
and magic field are outside the write set. SmallRange accounts for every
emitted inbounds GEP; this theorem does not rely on a SHA oracle. -/

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Init
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def memory (m : MemoryState) (p : Pointer) : MemoryState :=
  let m := m.storeAt (p.add 128#64) (7640891576956012808#64)
  let m := m.storeAt (p.add 136#64) (13503953896175478587#64)
  let m := m.storeAt (p.add 144#64) (4354685564936845355#64)
  let m := m.storeAt (p.add 152#64) (11912009170470909681#64)
  let m := m.storeAt (p.add 160#64) (5840696475078001361#64)
  let m := m.storeAt (p.add 168#64) (11170449401992604703#64)
  let m := m.storeAt (p.add 176#64) (2270897969802886507#64)
  let m := m.storeAt (p.add 184#64) (6620516959819538809#64)
  m.storeAt (p.add 200#64) (0#192)

def registers (E : Env program.Γ) (p : Pointer) : Env program.Γ :=
  E[%0 := .value (128 : BitVec 64),
    %1 := .value (7640891576956012808 : BitVec 64),
    %2 := .value (136 : BitVec 64),
    %3 := .value (-4942790177534073029 : BitVec 64),
    %4 := .value (144 : BitVec 64),
    %5 := .value (4354685564936845355 : BitVec 64),
    %6 := .value (152 : BitVec 64),
    %7 := .value (-6534734903238641935 : BitVec 64),
    %8 := .value (160 : BitVec 64),
    %9 := .value (5840696475078001361 : BitVec 64),
    %10 := .value (168 : BitVec 64),
    %11 := .value (-7276294671716946913 : BitVec 64),
    %12 := .value (176 : BitVec 64),
    %13 := .value (2270897969802886507 : BitVec 64),
    %14 := .value (184 : BitVec 64),
    %15 := .value (6620516959819538809 : BitVec 64),
    %16 := .value (200 : BitVec 64),
    %17 := .value (0 : BitVec 8),
    %18 := .value (24 : BitVec 64),
    %19 := .value (p.add 128#64),
    %20 := .value (p.add 136#64),
    %21 := .value (p.add 144#64),
    %22 := .value (p.add 152#64),
    %23 := .value (p.add 160#64),
    %24 := .value (p.add 168#64),
    %25 := .value (p.add 176#64),
    %26 := .value (p.add 184#64),
    %27 := .value (p.add 200#64)]

theorem body (E : Env program.Γ) (s : GlobalState) (p : Pointer)
    (hp : E.read (%arg0) = .value p) (hr : SmallRange s.mem p 224) :
    List.foldlM Instr.run E program.entry.body s =
      .value (registers E p, {s with mem := memory s.mem p}) := by
  have hp' : E.args 0 = .value p := hp
  have hr0 := hr
  have hg0 := hr0.gep (k := 128) (by decide)
  have hf0 := hr0.fits_add (k := 128) (count := 8) (by decide)
  have hr1 := hr0.storeAt (p.add 128#64) (7640891576956012808#64)
  have hg1 := hr1.gep (k := 136) (by decide)
  have hf1 := hr1.fits_add (k := 136) (count := 8) (by decide)
  have hr2 := hr1.storeAt (p.add 136#64) (13503953896175478587#64)
  have hg2 := hr2.gep (k := 144) (by decide)
  have hf2 := hr2.fits_add (k := 144) (count := 8) (by decide)
  have hr3 := hr2.storeAt (p.add 144#64) (4354685564936845355#64)
  have hg3 := hr3.gep (k := 152) (by decide)
  have hf3 := hr3.fits_add (k := 152) (count := 8) (by decide)
  have hr4 := hr3.storeAt (p.add 152#64) (11912009170470909681#64)
  have hg4 := hr4.gep (k := 160) (by decide)
  have hf4 := hr4.fits_add (k := 160) (count := 8) (by decide)
  have hr5 := hr4.storeAt (p.add 160#64) (5840696475078001361#64)
  have hg5 := hr5.gep (k := 168) (by decide)
  have hf5 := hr5.fits_add (k := 168) (count := 8) (by decide)
  have hr6 := hr5.storeAt (p.add 168#64) (11170449401992604703#64)
  have hg6 := hr6.gep (k := 176) (by decide)
  have hf6 := hr6.fits_add (k := 176) (count := 8) (by decide)
  have hr7 := hr6.storeAt (p.add 176#64) (2270897969802886507#64)
  have hg7 := hr7.gep (k := 184) (by decide)
  have hf7 := hr7.fits_add (k := 184) (count := 8) (by decide)
  have hr8 := hr7.storeAt (p.add 184#64) (6620516959819538809#64)
  have hg8 := hr8.gep (k := 200) (by decide)
  have hf8 := hr8.fits_add (k := 200) (count := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8
  have hz : (0#8).replicate 24 = 0#192 := by decide
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    registers, memory, hp', EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
    Operation.GepSignedRange, Operation.store, Operation.memset,
    mlir_env, mlir_effect, throwUBIf, hz, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8]

theorem run (s : GlobalState) (p : Pointer) (hr : SmallRange s.mem p 224) :
    program.run (program.args (.value p)) s =
      .value (.cons (.value p) .nil, {s with mem := memory s.mem p}) := by
  let E := Env.init (program.args (.value p)).get
  have hb := body E s p (by rfl) hr
  have hblock : program.entry.run program.blockParams E s =
      .value ((registers E p, .inl (.cons (.value p) .nil)),
        {s with mem := memory s.mem p}) := by
    unfold BasicBlock.run
    simp only [EffectM.bind_eq, hb, LeanMLIR.RIR.PoisonOr.value_bind]
    rfl
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  change (do
    let ((E', res), s') ← program.entry.run program.blockParams E s
    Func.continue («func» := program) E' res s') = _
  rw [hblock]
  rfl

/-- The concrete updates preserve allocator well-formedness. -/
theorem memory_wf (s : GlobalState) (p : Pointer) (hwf : s.WF) :
    ({s with mem := memory s.mem p} : GlobalState).WF := by
  simpa only [memory, GlobalState.WF_storeAt] using hwf

/-- Full call including frame cleanup: init allocates no private blocks. -/
theorem call (s : GlobalState) (p : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem p 224) :
    program.call (program.args (.value p)) s =
      .value (.cons (.value p) .nil, {s with mem := memory s.mem p}) := by
  have hc := Func.call_of_run (run s p hr)
  have he := GlobalState.eraseFrom_self (memory_wf s p hwf)
  simpa only [he] using hc

/-- Every allocation other than the context is exactly unchanged. -/
theorem memory_other_block (m : MemoryState) (p : Pointer) (id : BlockId)
    (hne : id ≠ p.id) : (memory m p)[id]? = m[id]? := by
  have hn (k : BitVec 64) : (⟨id, 0⟩ : Pointer).id ≠ (p.add k).id := hne
  simp only [memory, MemoryState.getElem?_storeAt_ne (hn _)]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Init
