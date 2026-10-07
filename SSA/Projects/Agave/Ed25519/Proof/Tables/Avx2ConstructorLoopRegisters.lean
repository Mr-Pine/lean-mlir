import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorEntryFrames
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheCombined
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddState
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoopTail

/-! Stable register readiness and the exact entry and backedge jumps of the
unchanged AVX2 table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters
open LeanMLIR.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2FieldMul.Execution (Blocks)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

structure Constants (E : ⟪kernel.Γ⟫) : Prop where
  cache : CacheCombined.Constants E
  double : Double.Constants E
  add : Add.Constants E
  zero21 : E.read (%21) = .value 0#64
  one22 : E.read (%22) = .value 1#64
  c195 : E.read (%195) = .value 160#64
  c196 : E.read (%196) = .value 192#64
  c197 : E.read (%197) = .value 224#64
  c198 : E.read (%198) = .value 256#64
  c199 : E.read (%199) = .value 288#64
  seven350 : E.read (%350) = .value 7#64
  bytes351 : E.read (%351) = .value 1280#64

theorem constants_ready (E : ⟪kernel.Γ⟫) : Constants (Avx2Constructor.Constants.result E) := by
  refine ⟨CacheCombined.constants_ready E, Double.constants_ready E, ?_,
    Avx2Constructor.Constants.read_21 E, Avx2Constructor.Constants.read_22 E,
    Avx2Constructor.Constants.read_195 E, Avx2Constructor.Constants.read_196 E,
    Avx2Constructor.Constants.read_197 E, Avx2Constructor.Constants.read_198 E,
    Avx2Constructor.Constants.read_199 E, Avx2Constructor.Constants.read_350 E,
    Avx2Constructor.Constants.read_351 E⟩
  exact ⟨Avx2Constructor.Constants.read_31 E, Avx2Constructor.Constants.read_52 E,
    Avx2Constructor.Constants.read_70 E, Avx2Constructor.Constants.read_332 E,
    Avx2Constructor.Constants.read_349 E⟩

theorem Constants.frame {E F : ⟪kernel.Γ⟫} (h : Constants E)
    (hf : RegisterFrame 352 kernel.Γ.n E F) : Constants F := by
  refine ⟨h.cache.frame hf, ?_, ?_,
    (hf.read (%21) (by decide)).trans h.zero21,
    (hf.read (%22) (by decide)).trans h.one22,
    (hf.read (%195) (by decide)).trans h.c195,
    (hf.read (%196) (by decide)).trans h.c196,
    (hf.read (%197) (by decide)).trans h.c197,
    (hf.read (%198) (by decide)).trans h.c198,
    (hf.read (%199) (by decide)).trans h.c199,
    (hf.read (%350) (by decide)).trans h.seven350,
    (hf.read (%351) (by decide)).trans h.bytes351⟩
  · exact ⟨(hf.read (%4) (by decide)).trans h.double.c32,
      (hf.read (%8) (by decide)).trans h.double.c64,
      (hf.read (%12) (by decide)).trans h.double.c96,
      (hf.read (%16) (by decide)).trans h.double.c128,
      (hf.read (%31) (by decide)).trans h.double.poison,
      (hf.read (%230) (by decide)).trans h.double.one,
      (hf.read (%247) (by decide)).trans h.double.«prefix»,
      (hf.read (%264) (by decide)).trans h.double.difference,
      (hf.read (%281) (by decide)).trans h.double.lazy0,
      (hf.read (%298) (by decide)).trans h.double.lazyN,
      (hf.read (%315) (by decide)).trans h.double.sum⟩
  · exact ⟨(hf.read (%31) (by decide)).trans h.add.poison,
      (hf.read (%52) (by decide)).trans h.add.prepare0,
      (hf.read (%70) (by decide)).trans h.add.prepareN,
      (hf.read (%332) (by decide)).trans h.add.difference0,
      (hf.read (%349) (by decide)).trans h.add.differenceN⟩

structure BaseReady (slots : State.Slots) (table : Pointer) (E : ⟪kernel.Γ⟫) : Prop where
  constants : Constants E
  initial : Double.InitialPointers E slots
  tableRead : E.read (%360) = .value table

structure Ready (slots : State.Slots) (table : Pointer) (E : ⟪kernel.Γ⟫) : Prop
    extends BaseReady slots table E where
  setup : Double.SetupPointers E slots

theorem BaseReady.preserve {E F : ⟪kernel.Γ⟫} (h : BaseReady slots table E)
    (hf : RegisterFrame 361 kernel.Γ.n E F) : BaseReady slots table F := by
  refine ⟨h.constants.frame (hf.weaken (by decide) (by rfl)), ?_,
    (hf.read (%360) (by decide)).trans h.tableRead⟩
  exact ⟨(hf.read (%352) (by decide)).trans h.initial.r352,
    (hf.read (%353) (by decide)).trans h.initial.r353,
    (hf.read (%354) (by decide)).trans h.initial.r354,
    (hf.read (%355) (by decide)).trans h.initial.r355,
    (hf.read (%356) (by decide)).trans h.initial.r356,
    (hf.read (%357) (by decide)).trans h.initial.r357,
    (hf.read (%358) (by decide)).trans h.initial.r358,
    (hf.read (%359) (by decide)).trans h.initial.r359⟩

theorem Ready.preserve {E F : ⟪kernel.Γ⟫} (h : Ready slots table E)
    (hf : RegisterFrame 803 kernel.Γ.n E F) : Ready slots table F := by
  refine ⟨h.toBaseReady.preserve (hf.weaken (by decide) (by rfl)), ?_⟩
  exact ⟨(hf.read (%787) (by decide)).trans h.setup.r787,
    (hf.read (%788) (by decide)).trans h.setup.r788,
    (hf.read (%789) (by decide)).trans h.setup.r789,
    (hf.read (%790) (by decide)).trans h.setup.r790,
    (hf.read (%791) (by decide)).trans h.setup.r791,
    (hf.read (%792) (by decide)).trans h.setup.r792,
    (hf.read (%793) (by decide)).trans h.setup.r793,
    (hf.read (%794) (by decide)).trans h.setup.r794,
    (hf.read (%795) (by decide)).trans h.setup.r795,
    (hf.read (%796) (by decide)).trans h.setup.r796,
    (hf.read (%797) (by decide)).trans h.setup.r797,
    (hf.read (%798) (by decide)).trans h.setup.r798,
    (hf.read (%799) (by decide)).trans h.setup.r799,
    (hf.read (%800) (by decide)).trans h.setup.r800,
    (hf.read (%801) (by decide)).trans h.setup.r801,
    (hf.read (%802) (by decide)).trans h.setup.r802⟩

theorem entry_ready (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer) :
    BaseReady (State.slots s) (Stack.pointer s 8) (Entry.result E s a) :=
  ⟨(constants_ready E).frame ((EntryFrames.result_frame E s a).weaken (by rfl) (by decide)),
    EntryFrames.initial_pointers E s a, EntryFrames.table_read E s a⟩

theorem double_ready {E : ⟪kernel.Γ⟫} (h : BaseReady slots table E)
    (P : Avx2PointAdd.Point) : Ready slots table (Double.resultEnv E slots P) :=
  ⟨h.preserve ((Double.resultEnv_frame E slots P).weaken (by decide) (by rfl)),
    Double.resultEnv_pointers E slots P⟩

theorem Ready.add_input {E : ⟪kernel.Γ⟫} (h : Ready slots table E) (i : Fin 7)
    (hc : E.read (%803) = .value (BitVec.ofNat 64 i.val)) :
    Add.Input E (AddState.q slots) (slots 7) table (AddState.index i) := by
  exact ⟨h.constants.add, h.constants.one22, h.initial.r359, h.constants.c195,
    h.initial.r352, h.initial.r353, h.initial.r354, h.initial.r355, h.initial.r358,
    h.tableRead,
    h.setup.r787, h.setup.r788, h.setup.r789, h.setup.r790,
    h.setup.r791, h.setup.r792, h.setup.r793, h.setup.r794,
    h.setup.r795, h.setup.r796, h.setup.r797, h.setup.r798,
    h.setup.r799, h.setup.r800, h.setup.r801, h.setup.r802, hc⟩

def entryPhi (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ := E[%803 := .value 0#64]

theorem entryPhi_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 803 kernel.Γ.n E (entryPhi E) :=
  (RegisterFrame.refl 803 kernel.Γ.n E).write (%803) (.value 0#64) (by decide)

theorem entryPhi_cursor (E : ⟪kernel.Γ⟫) :
    (entryPhi E).read (%803) = .value 0#64 := by simp [entryPhi, mlir_env]

theorem entryPhi_ready {E : ⟪kernel.Γ⟫} (h : Ready slots table E) :
    Ready slots table (entryPhi E) := h.preserve (entryPhi_frame E)

theorem entry_exit (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (h : Ready slots table E) :
    (kernel.bb0 p).exit.run kernel.blockParams E s = .value ((entryPhi E, .inr 2), s) := by
  simp [kernel.bb0, Exit.run, Jump.run, kernel.blockParams, entryPhi,
    mlir_env, h.constants.zero21, EffectM.pure_eq]
  rfl

theorem Ready.tail_input {E : ⟪kernel.Γ⟫} (h : Ready slots table E)
    (i : Fin 7) {v : Blocks}
    (h804 : E.read (%804) = .value (BitVec.ofNat 64 (i.val + 1)))
    (h805 : E.read (%805) = .value (table.add (BitVec.ofNat 64 (160 * i.val))))
    (hv : ∀ k, CacheNegation.successorOutputReads E k = Ty.wrap (t := .vec 8 32) (v k)) :
    LoopTail.input E (table.add (BitVec.ofNat 64 (160 * i.val))) v i = E := by
  have h0 : E.read (%1021) = Ty.wrap (v 0) := hv 0
  have h1 : E.read (%1022) = Ty.wrap (v 1) := hv 1
  have h2 : E.read (%1023) = Ty.wrap (v 2) := hv 2
  have h3 : E.read (%1024) = Ty.wrap (v 3) := hv 3
  have h4 : E.read (%1025) = Ty.wrap (v 4) := hv 4
  unfold LoopTail.input
  rw [Env.write_of_read E (%195) h.constants.c195,
    Env.write_of_read E (%196) h.constants.c196,
    Env.write_of_read E (%197) h.constants.c197,
    Env.write_of_read E (%198) h.constants.c198,
    Env.write_of_read E (%199) h.constants.c199,
    Env.write_of_read E (%350) h.constants.seven350,
    Env.write_of_read E (%804) h804, Env.write_of_read E (%805) h805,
    Env.write_of_read E (%1021) h0, Env.write_of_read E (%1022) h1,
    Env.write_of_read E (%1023) h2, Env.write_of_read E (%1024) h3,
    Env.write_of_read E (%1025) h4]

theorem tailResult_frame (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks) (i : Fin 7)
    (hinput : LoopTail.input E r v i = E) :
    RegisterFrame 1026 kernel.Γ.n E (LoopTail.result E r v i) := by
  unfold LoopTail.result
  rw [hinput]
  iterate 6 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

def tailPhi (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  if i.val = 6 then LoopTail.result E r v i
  else (LoopTail.result E r v i)[%803 := .value (BitVec.ofNat 64 (i.val + 1))]

theorem tailPhi_frame (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks) (i : Fin 7)
    (hinput : LoopTail.input E r v i = E) :
    RegisterFrame 803 kernel.Γ.n E (tailPhi E r v i) := by
  have hf : RegisterFrame 803 kernel.Γ.n E (LoopTail.result E r v i) :=
    (tailResult_frame E r v i hinput).weaken (by decide) (by rfl)
  unfold tailPhi
  split
  · exact hf
  · exact hf.write (%803) (.value (BitVec.ofNat 64 (i.val + 1))) (by decide)

theorem tailPhi_cursor (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks) (i : Fin 7)
    (hi : i.val < 6) :
    (tailPhi E r v i).read (%803) = .value (BitVec.ofNat 64 (i.val + 1)) := by
  have hn : i.val ≠ 6 := by omega
  simp [tailPhi, hn, mlir_env]

theorem tailPhi_ready {E : ⟪kernel.Γ⟫} (h : Ready slots table E)
    (r : Pointer) (v : Blocks) (i : Fin 7) (hinput : LoopTail.input E r v i = E) :
    Ready slots table (tailPhi E r v i) := h.preserve (tailPhi_frame E r v i hinput)

theorem tail_exit (p : Primitives) (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks)
    (i : Fin 7) (s : GlobalState) :
    (kernel.bb2 p).exit.run kernel.blockParams (LoopTail.result E r v i) s =
      .value ((tailPhi E r v i, .inr (if i.val = 6 then 1 else 2)), s) :=
  LoopTail.exit p E r v i s

theorem Ready.returnInput {E : ⟪kernel.Γ⟫} (h : Ready slots table E) :
    ConstructorMemory.avx2ReturnInput E table = E := by
  unfold ConstructorMemory.avx2ReturnInput
  rw [Env.write_of_read E (%351) h.constants.bytes351,
    Env.write_of_read E (%360) h.tableRead]

end Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.constants_ready,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.Constants.frame,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.BaseReady.preserve,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.Ready.preserve,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.entry_ready,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.double_ready,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.Ready.add_input,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.entryPhi_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.entryPhi_cursor,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.entryPhi_ready,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.entry_exit,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.Ready.tail_input,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.tailResult_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.tailPhi_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.tailPhi_cursor,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.tailPhi_ready,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.tail_exit,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopRegisters.Ready.returnInput] do
    let axioms ← collectAxioms endpoint
    for axiomName in axioms do
      unless axiomName ∈ [`propext, `Classical.choice, `Quot.sound] do
        throwError "nonstandard axiom {axiomName} in {endpoint}"
    logInfo m!"standard-three audit passed: {endpoint}"
