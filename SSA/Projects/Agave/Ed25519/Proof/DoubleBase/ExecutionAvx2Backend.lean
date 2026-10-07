import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Prefix
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Ladder
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2UnpackReadback

/-! Source-only composition of the AVX2 prelude and descending ladder.
The outstanding premises concern individual arithmetic blocks and their
register/memory invariants. No premise asserts a complete backend refinement.
This module also makes the caller-frame erasure at `Func.call` explicit. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
open NAF.Memory (Buffer)
open Reduce64.Execution (SmallRange)
open Conformance.BackendExecution (Invocation readPoint PointReadable RefinesAt)
open Avx2PointAdd.Phases (packPoint)
set_option maxRecDepth 10000

variable {p : Avx2CFG.Primitives}

/-- Live-in constants of the already proved final block, before its point
registers are supplied by `PointAt .afterB`. -/
def OutputReady (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) : Prop :=
  E ⊨ [%arg0 := .value r, %3 := .value 32#64, %5 := .value 6#64,
    %10 := .value 1#64, %13 := .value 5#64, %20 := .value 64#64,
    %26 := Vector.replicate 8 .poison,
    %225 := .value 7#64, %226 := .value 4#64, %227 := .value 3#64,
    %228 := .value 26#64, %229 := Vector.replicate 2 (.value 26#64),
    %230 := .value 16#64, %231 := Vector.replicate 4 (.value 26#64),
    %232 := .value 72#64, %233 := .value 2#64, %234 := .value 104#64,
    %235 := .value 136#64, %236 := .value 152#64]

theorem OutputReady.of_frame (h : OutputReady E r)
    (hf : RegisterFrame 421 avx2Kernel.Γ.n E E') : OutputReady E' r := by
  rcases h with ⟨h0, h3, h5, h10, h13, h20, h26, h225, h226, h227,
    h228, h229, h230, h231, h232, h233, h234, h235, h236⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hf.read _ (by decide)]
  all_goals assumption

/-- The memory invariant needed at each narrow arithmetic boundary. Scratch
ranges, output allocation and cached table are concrete objects. -/
structure BackendReady (r table : Pointer) (slots : SetupSlots) (A : Extended F)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) : Prop where
  outputRegisters : OutputReady E r
  wellFormed : s.WF
  output : SmallRange s.mem r 160
  scratch : ∀ i, Buffer s.mem (slots i) 160
  tableRange : SmallRange s.mem table 1280
  tableValues : ∀ k : Fin 8,
    Avx2PointAdd.pointReduced (packedPoint s.mem (table.add (BitVec.ofNat 64 (160 * k.val)))) ∧
    Avx2PointAdd.pointValue (packedPoint s.mem (table.add (BitVec.ofNat 64 (160 * k.val)))) =
      avx2Cache (Tables.avx2Width5 A k)

theorem backendReady_stable : ContextStable (BackendReady r table slots A) := by
  intro E E' s hf h
  exact ⟨h.outputRegisters.of_frame hf, h.wellFormed, h.output, h.scratch,
    h.tableRange, h.tableValues⟩

/-- A constructor frame transports all digit-array bytes, rather than merely
asserting that the arithmetic blocks can load some digits. -/
theorem DigitMemory.of_tableFrame (h : DigitMemory s da db a b)
    (hf : TableFrame s s' table) (hA : da.id ≠ table.id) (hB : db.id ≠ table.id) :
    DigitMemory s' da db a b := by
  refine ⟨hf.live da 256 h.bufferA, hf.live db 256 h.bufferB, ?_, ?_⟩
  · intro i
    rw [hf.read _ 8 (Range.disjoint_of_id_ne (by simpa using hA))]
    exact h.readA i
  · intro i
    rw [hf.read _ 8 (Range.disjoint_of_id_ne (by simpa using hB))]
    exact h.readB i

theorem prefixState_digits (s : GlobalState) (a b : BitVec 256) (hwf : s.WF) :
    DigitMemory (prefixState s a b) (avx2StackPtr s 29) (avx2StackPtr s 28)
      a.toNat b.toNat := by
  let sa := nafPhase 5 (avx2Stack s 30) (avx2StackPtr s 29) (avx2StackPtr s 21) a
  have hA : Buffer (avx2Stack s 30).mem (avx2StackPtr s 29) 256 :=
    avx2Stack_buffer hwf 29 30 (by decide) (by decide)
  have hB : Buffer sa.mem (avx2StackPtr s 28) 256 :=
    nafPhase_buffer 5 _ _ _ a (avx2Stack_buffer hwf 28 30 (by decide) (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nafPhase_buffer 8 _ _ _ b (nafPhase_buffer 5 _ _ _ a hA)
  · exact nafPhase_buffer 8 _ _ _ b hB
  · intro i
    unfold prefixState
    rw [nafPhase_read_other 8 sa (avx2StackPtr s 28) (avx2StackPtr s 20)
      ((avx2StackPtr s 29).add (BitVec.ofNat 64 i.val)) b 8
      (by simpa using avx2Stack_separate s 28 29 (by decide))
      (by simpa using avx2Stack_separate s 20 29 (by decide))]
    exact nafPhase_digits 5 (Or.inl rfl) _ _ _ a hA
      (avx2Stack_separate s 21 29 (by decide)) i
  · intro i
    exact nafPhase_digits 8 (Or.inr rfl) sa _ _ b hB
      (avx2Stack_separate s 20 28 (by decide)) i

/-- The packed identity in the real table-setup successor. -/
def packedIdentity : Avx2PointAdd.Point :=
  let zero : Avx2FieldMul.Limbs := fun _ => 0
  let one : Avx2FieldMul.Limbs := fun i => if i.val = 0 then 1 else 0
  ⟨zero, one, one, zero⟩

theorem packedIdentity_reduced : Avx2PointAdd.pointReduced packedIdentity := by
  unfold Avx2PointAdd.pointReduced packedIdentity Avx2PointAdd.reduced
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro i
  all_goals fin_cases i <;> norm_num [Avx2PointAdd.radix]

theorem packedIdentity_value :
    Avx2PointAdd.pointValue packedIdentity = (identityPoint : Extended F) := by
  ext <;> norm_num [Avx2PointAdd.pointValue, Avx2PointAdd.value, packedIdentity,
    identityPoint, Field.decode10, Field.exponent, Fin.sum_univ_succ]
  all_goals rfl

theorem tableSetupResult_point (E : ⟪avx2Kernel.Γ⟫) (slots : SetupSlots)
    (table : Pointer) (pos : Fin 256) :
    PointAt .loop (tableSetupResult E slots table pos) identityPoint := by
  refine ⟨packedIdentity, packedIdentity_reduced, packedIdentity_value, ?_⟩
  intro k
  fin_cases k <;> simp [PointReads, pointReg, tableSetupResult, packedIdentity,
    packPoint, Avx2PointAdd.Phases.evenIndex, Avx2PointAdd.Phases.oddIndex,
    Avx2PointAdd.word, Ty.wrap_vec, mlir_env]
  all_goals decide +kernel

/-- The final block interface mentions neither scalar digits nor a ladder
result. Its continuation is a return, so this is a bb34-only obligation. -/
def OutputBlock (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (ctx : LocalContext) (r : Pointer) : Prop :=
  ∀ E s Q, ctx E s → PointAt .afterB E Q →
    ∃ s', (avx2Kernel p g).runFrom E 34 s = .value (.nil, s') ∧
      SmallRange s'.mem r 160 ∧ readPoint s' r = Q

theorem unpackInput_of_ready (h : OutputReady E r)
    (hp : PointReads .afterB E P) : unpackInput E r (packPoint P) = E := by
  rcases h with ⟨h0, h3, h5, h10, h13, h20, h26, h225, h226, h227,
    h228, h229, h230, h231, h232, h233, h234, h235, h236⟩
  have hp0 : E.read (%808) = Ty.wrap (packPoint P 0) := by
    simpa [pointReg] using hp 0
  have hp1 : E.read (%807) = Ty.wrap (packPoint P 1) := by
    simpa [pointReg] using hp 1
  have hp2 : E.read (%806) = Ty.wrap (packPoint P 2) := by
    simpa [pointReg] using hp 2
  have hp3 : E.read (%805) = Ty.wrap (packPoint P 3) := by
    simpa [pointReg] using hp 3
  have hp4 : E.read (%809) = Ty.wrap (packPoint P 4) := by
    simpa [pointReg] using hp 4
  have hargs : Function.update E.args 0 (.value r) = E.args :=
    Function.update_eq_self_iff.mpr h0.symm
  unfold unpackInput
  rw [hargs]
  rw [Env.write_of_read E (%3) h3,
    Env.write_of_read E (%5) h5, Env.write_of_read E (%10) h10,
    Env.write_of_read E (%13) h13, Env.write_of_read E (%20) h20,
    Env.write_of_read E (%26) h26, Env.write_of_read E (%225) h225,
    Env.write_of_read E (%226) h226, Env.write_of_read E (%227) h227,
    Env.write_of_read E (%228) h228, Env.write_of_read E (%229) h229,
    Env.write_of_read E (%230) h230, Env.write_of_read E (%231) h231,
    Env.write_of_read E (%232) h232, Env.write_of_read E (%233) h233,
    Env.write_of_read E (%234) h234, Env.write_of_read E (%235) h235,
    Env.write_of_read E (%236) h236]
  simpa only [Ty.wrap_vec] using
    (show E[%808 := Ty.wrap (packPoint P 0), %807 := Ty.wrap (packPoint P 1),
      %806 := Ty.wrap (packPoint P 2), %805 := Ty.wrap (packPoint P 3),
      %809 := Ty.wrap (packPoint P 4)] = E by
        rw [Env.write_of_read E (%808) hp0, Env.write_of_read E (%807) hp1,
          Env.write_of_read E (%806) hp2, Env.write_of_read E (%805) hp3,
          Env.write_of_read E (%809) hp4])

theorem unpackStore_range {s : GlobalState} (h : SmallRange s.mem r 160) (v : UnpackBlocks) :
    SmallRange (unpackStore s.mem r v) r 160 := by
  unfold unpackStore
  repeat' apply SmallRange.storeAt
  exact h

/-- Byte-layout readback property discharged by `unpack_readback`. -/
def UnpackReadback : Prop :=
  ∀ (s : GlobalState) (r : Pointer) (P : Avx2PointAdd.Point),
    SmallRange s.mem r 160 → Avx2PointAdd.pointReduced P →
    readPoint {s with mem := unpackStore s.mem r (packPoint P)} r =
      Avx2PointAdd.pointValue P

theorem unpack_readback : UnpackReadback := unpackStore_readPoint

theorem outputBlock_of_unpack_readback (hread : UnpackReadback)
    (hready : ∀ E s, ctx E s → OutputReady E r ∧ SmallRange s.mem r 160) :
    OutputBlock p g ctx r := by
  intro E s Q hc hp
  obtain ⟨P, hP, hQ, hreads⟩ := hp
  obtain ⟨hreg, hrange⟩ := hready E s hc
  have hrun := unpack_run p g E r (packPoint P) s hrange
  rw [unpackInput_of_ready hreg hreads] at hrun
  exact ⟨_, hrun, unpackStore_range hrange _, (hread s r P hrange hP).trans hQ⟩

/-- The exact final block needs only its live-in constants and output allocation. -/
theorem outputBlock_of_ready
    (hready : ∀ E s, ctx E s → OutputReady E r ∧ SmallRange s.mem r 160) :
    OutputBlock p g ctx r :=
  outputBlock_of_unpack_readback unpack_readback hready

/-- The frame-erase operation keeps the actual caller allocation. -/
theorem smallRange_eraseFrom (h : SmallRange m r bytes) (hr : r.id.id < cutoff) :
    SmallRange (m.eraseFrom cutoff) r bytes := by
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  refine ⟨b, ?_, hsmall, hsize⟩
  simpa [MemoryState.eraseFrom, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_filter', hr] using hb

theorem readAt_eraseFrom (m : MemoryState) (q : Pointer) (width : Nat)
    (hq : q.id.id < cutoff) : (m.eraseFrom cutoff).readAt q width = m.readAt q width := by
  simp [MemoryState.readAt, MemoryState.eraseFrom, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_filter', hq, Option.filter]
  cases m.mem[q.id]? <;> rfl

theorem readPoint_eraseFrom (s : GlobalState) (r : Pointer) (hr : r.id.id < cutoff) :
    readPoint {s with mem := s.mem.eraseFrom cutoff} r = readPoint s r := by
  have hcoordinate (c : Fin 4) :
      Conformance.BackendExecution.readCoordinate {s with mem := s.mem.eraseFrom cutoff} r c =
        Conformance.BackendExecution.readCoordinate s r c := by
    have hwords : (fun limb : Fin 5 => (s.mem.eraseFrom cutoff).readAt
        (r.add (BitVec.ofNat 64 (40 * c.val + 8 * limb.val))) 64) =
        (fun limb : Fin 5 => s.mem.readAt
          (r.add (BitVec.ofNat 64 (40 * c.val + 8 * limb.val))) 64) := by
      funext limb
      exact readAt_eraseFrom s.mem _ 64 (by simpa using hr)
    unfold Conformance.BackendExecution.readCoordinate
    rw [hwords]
  simp only [readPoint, hcoordinate]

theorem smallRange_pointReadable (h : SmallRange s.mem r 160) : PointReadable s r := by
  refine ⟨by simpa using h.fits, ?_⟩
  have := h.offset_lt
  norm_num at this ⊢
  omega

/-- The full imported descending ladder and final output compose. The only
point-operation premises are the five individual blocks and bb34. -/
theorem ladder_to_output_run
    (hc : ArithmeticBlocks p g ctx a b da db table) (hs : ContextStable ctx)
    (hout : OutputBlock p g ctx r) (n : Nat) (hn : n < 256)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (Q : Extended F)
    (hready : LadderReady ctx a b da db E s ⟨n, hn⟩) (hpoint : PointAt .loop E Q) :
    ∃ s', (avx2Kernel p g).runFrom E 18 s = .value (.nil, s') ∧
      SmallRange s'.mem r 160 ∧
      readPoint s' r = run (avx2Step table) (nafDigits 5 a) (nafDigits 8 b) n Q := by
  obtain ⟨EF, sf, hrun, hr, hp⟩ := ladder_run hc hs n hn E s Q hready hpoint
  obtain ⟨s', hreturn, houtput, hread⟩ := hout EF sf _ hr.localContext hp
  exact ⟨s', hrun.trans hreturn, houtput, hread⟩

set_option maxHeartbeats 1000000 in
/-- The real prefix establishes all output and scratch invariants used by the ladder. -/
theorem prefix_backendReady (g : Avx2CFG.Globals) (i : Invocation) (s : GlobalState)
    (hinput : Input i s) (ES : ⟪avx2Kernel.Γ⟫) (s' : GlobalState)
    (hframe : RegisterFrame 268 421 (entryLoopEnv (Env.init i.args.get) g s) ES)
    (htable : TableFrame
      (prefixState s (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256))
      s' (avx2StackPtr s 27))
    (hvalues : ∀ k : Fin 8,
      Avx2PointAdd.pointReduced (packedPoint s'.mem
        ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))) ∧
      Avx2PointAdd.pointValue (packedPoint s'.mem
        ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))) =
        avx2Cache (Tables.avx2Width5 (readPoint s i.pointA) k)) :
    BackendReady i.output (avx2StackPtr s 27) (stackSetupSlots s) (readPoint s i.pointA)
      (tableSetupResult ES (stackSetupSlots s) (avx2StackPtr s 27)
        (scalarStartIndex (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256))) s' := by
  have hreg : OutputReady ES i.output := by
    refine ⟨(hframe.read (%arg0) (by decide)).trans ?_,
      (hframe.read (%3) (by decide)).trans ?_,
      (hframe.read (%5) (by decide)).trans ?_,
      (hframe.read (%10) (by decide)).trans ?_,
      (hframe.read (%13) (by decide)).trans ?_,
      (hframe.read (%20) (by decide)).trans ?_,
      (hframe.read (%26) (by decide)).trans ?_,
      (hframe.read (%225) (by decide)).trans ?_,
      (hframe.read (%226) (by decide)).trans ?_,
      (hframe.read (%227) (by decide)).trans ?_,
      (hframe.read (%228) (by decide)).trans ?_,
      (hframe.read (%229) (by decide)).trans ?_,
      (hframe.read (%230) (by decide)).trans ?_,
      (hframe.read (%231) (by decide)).trans ?_,
      (hframe.read (%232) (by decide)).trans ?_,
      (hframe.read (%233) (by decide)).trans ?_,
      (hframe.read (%234) (by decide)).trans ?_,
      (hframe.read (%235) (by decide)).trans ?_,
      (hframe.read (%236) (by decide)).trans ?_⟩
    all_goals simp [entryLoopEnv, avx2EntryEnv, Env.init, Invocation.args, Vals.get, mlir_env] <;> decide +kernel
  refine ⟨?_, htable.wellFormed,
    htable.live _ _ (prefixState_buffer _ _ _ hinput.wellFormed hinput.output), ?_,
    htable.live _ _ (prefixState_stack_buffer _ _ _ hinput.wellFormed 27 (by decide)),
    hvalues⟩
  · rcases hreg with ⟨harg0, h3, h5, h10, h13, h20, h26, h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235, h236⟩
    change ES.args 0 = .value i.output at harg0
    constructor <;> simp [tableSetupResult, tableSetupInput, mlir_env,
      harg0, h3, h5, h10, h13, h20, h26, h225, h226, h227, h228, h229, h230, h231, h232, h233, h234, h235, h236]
  · intro k
    apply htable.live
    have hsize : avx2StackSize (setupStackIndex k).val < 2 ^ 63 := by
      rw [setupStackIndex_size]
      decide
    simpa only [stackSetupSlots, setupStackIndex_size, Buffer, SmallRange] using
      prefixState_stack_buffer s (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256)
        hinput.wellFormed (setupStackIndex k) hsize

set_option maxHeartbeats 1000000 in
/-- A final backend contract from the real entry environment. This theorem
assumes only the concrete entry invariant at the table constructor's returned
state; NAF generation, start-index scan, all digit dispatches and the entire
descending induction are executed by the imported CFG proofs. -/
theorem backend_refines_of_local_blocks
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals) (htable : TableContract p.call0)
    (i : Invocation) (s : GlobalState) (hinput : Input i s)
    (ctx : LocalContext) (hs : ContextStable ctx)
    (hc : ArithmeticBlocks p g ctx
      (s.mem.readAt i.scalarA 256).toNat (s.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr s 29) (avx2StackPtr s 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint s i.pointA))))
    (hout : OutputBlock p g ctx i.output)
    (hcontext : ∀ ES s',
      RegisterFrame 268 421 (entryLoopEnv (Env.init i.args.get) g s) ES →
      TableFrame (prefixState s (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256))
        s' (avx2StackPtr s 27) →
      (∀ k : Fin 8,
        Avx2PointAdd.pointReduced (packedPoint s'.mem
          ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))) ∧
        Avx2PointAdd.pointValue (packedPoint s'.mem
          ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))) =
          avx2Cache (Tables.avx2Width5 (readPoint s i.pointA) k)) →
      ctx (tableSetupResult ES (stackSetupSlots s) (avx2StackPtr s 27)
        (scalarStartIndex (s.mem.readAt i.scalarA 256) (s.mem.readAt i.scalarB 256))) s') :
    RefinesAt (avx2Kernel p g).call avx2Math i s := by
  let a := s.mem.readAt i.scalarA 256
  let b := s.mem.readAt i.scalarB 256
  let E : ⟪avx2Kernel.Γ⟫ := Env.init i.args.get
  obtain ⟨ES, st, hprefix, hframe, htableFrame, hvalues⟩ := prefix_to_ladder_run p g htable
    E s i.scalarA i.scalarB i.pointA a b hinput.wellFormed hinput.scalarA hinput.scalarB
    hinput.pointA hinput.pointLimbs rfl rfl
    (by simp [E, Env.init, Invocation.args, Vals.get])
    (by simp [E, Env.init, Invocation.args, Vals.get])
    (by simp [E, Env.init, Invocation.args, Vals.get])
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
      hcontext ES st hframe htableFrame hvalues⟩
  obtain ⟨s', hrun, hrange, hread⟩ := ladder_to_output_run hc hs hout
    (scalarStartIndex a b).val (scalarStartIndex a b).isLt EL st identityPoint hready
    (tableSetupResult_point ES _ _ _)
  have hfull : (avx2Kernel p g).run i.args s = .value (.nil, s') := by
    rw [Func.run_runFrom_eq]
    exact hprefix.trans hrun
  have hcaller : i.output.id.id < s.alloc.nextFreeBlock :=
    hinput.wellFormed.lt hinput.output.fits.mem
  refine ⟨{s' with mem := s'.mem.eraseFrom s.alloc.nextFreeBlock},
    Func.call_of_run hfull, smallRange_pointReadable (smallRange_eraseFrom hrange hcaller), ?_⟩
  rw [readPoint_eraseFrom s' i.output hcaller, hread]
  rfl

/-- Backend refinement with the output block and initial ladder context discharged. -/
theorem backend_refines_of_arithmetic_blocks
    (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals) (htable : TableContract p.call0)
    (i : Invocation) (s : GlobalState) (hinput : Input i s)
    (hc : ArithmeticBlocks p g
      (BackendReady i.output (avx2StackPtr s 27) (stackSetupSlots s) (readPoint s i.pointA))
      (s.mem.readAt i.scalarA 256).toNat (s.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr s 29) (avx2StackPtr s 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint s i.pointA)))) :
    RefinesAt (avx2Kernel p g).call avx2Math i s :=
  backend_refines_of_local_blocks p g htable i s hinput _ backendReady_stable hc
    (outputBlock_of_ready (fun _ _ h => ⟨h.outputRegisters, h.output⟩))
    (fun ES s' hf ht hv => prefix_backendReady g i s hinput ES s' hf ht hv)

end Agave.Ed25519.DoubleBase.ExecutionAvx2
