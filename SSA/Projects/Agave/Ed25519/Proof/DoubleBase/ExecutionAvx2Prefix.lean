import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Stack
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2TotalNAF
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ScanLoop
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2TableSetup

/-! Composition of the actual entry, both NAF emitters, descending scan and
cached-table setup. The state formulas below name the exact stores already
proved for the imported blocks; they do not replace the executable CFG. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR NAF
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

/-- Memory after initialization and all source-directed NAF byte stores. -/
def nafPhase (width : Nat) (s : GlobalState) (digits scratch : Pointer)
    (scalar : BitVec 256) : GlobalState :=
  let initialized := nafInitialized s digits scratch scalar
  {initialized with mem := (NAF.Memory.storeLoop width digits 256 0
    ⟨scalar.toNat, 0⟩ initialized.mem)}

theorem nafPhase_buffer (width : Nat) (s : GlobalState) (digits scratch : Pointer)
    (scalar : BitVec 256) (h : Buffer s.mem q bytes) :
    Buffer (nafPhase width s digits scratch scalar).mem q bytes :=
  NAF.Memory.storeLoop_buffer width digits 256 0 ⟨scalar.toNat, 0⟩ _ (nafSetup_buffer h)

theorem nafPhase_wf (width : Nat) (s : GlobalState) (digits scratch : Pointer)
    (scalar : BitVec 256) (hwf : s.WF) :
    (nafPhase width s digits scratch scalar).WF :=
  storeLoop_wf width digits 256 0 ⟨scalar.toNat, 0⟩ _ (nafSetup_wf hwf)

theorem nafPhase_read_other (width : Nat) (s : GlobalState) (digits scratch q : Pointer)
    (scalar : BitVec 256) (bits : Nat) (hdq : digits.id ≠ q.id)
    (hsq : scratch.id ≠ q.id) :
    (nafPhase width s digits scratch scalar).mem.readAt q bits = s.mem.readAt q bits := by
  unfold nafPhase
  rw [NAF.Memory.storeLoop_preserves_other_block width digits 256 0 _ _ q bits hdq,
    nafSetup_read_other s digits scratch q scalar bits hdq hsq]

theorem nafPhase_digits (width : Nat) (hwidth : NAF.Supported width)
    (s : GlobalState) (digits scratch : Pointer) (scalar : BitVec 256)
    (hdigits : Buffer s.mem digits 256) (hsd : scratch.id ≠ digits.id)
    (i : Fin 256) :
    (nafPhase width s digits scratch scalar).mem.readAt
        (digits.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (sourceDigits width scalar.toNat i) :=
  NAF.Memory.storeLoop_sourceDigits width hwidth scalar.toNat digits _
    (nafSetup_buffer hdigits) (nafSetup_digits_zero s digits scratch scalar hdigits hsd) i

def entryLoopEnv (E : ⟪avx2Kernel.Γ⟫) (g : Avx2CFG.Globals)
    (s : GlobalState) : ⟪avx2Kernel.Γ⟫ :=
  (avx2EntryEnv E g s)[%270 := .value 0#64]

/-- Complete actual entry and first emitter. Fresh allocation derives all
scratch contents, disjointness and byte-output initialization. -/
theorem first_naf_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (input : Pointer) (scalar : BitVec 256)
    (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (hscalar : s.mem.readAt input 256 = scalar) (harg : E.args 1 = .value input) :
    ∃ E' : ⟪avx2Kernel.Γ⟫,
      (avx2Kernel p g).runFrom E 0 s =
        (avx2Kernel p g).runFrom E' 7
          (nafPhase 5 (avx2Stack s 30) (avx2StackPtr s 29) (avx2StackPtr s 21) scalar) ∧
      RegisterFrame 268 298 (entryLoopEnv E g s) E' := by
  let initial := nafInitialized (avx2Stack s 30) (avx2StackPtr s 29)
    (avx2StackPtr s 21) scalar
  have hs : Buffer (avx2Stack s 30).mem (avx2StackPtr s 21) 40 :=
    avx2Stack_buffer hwf 21 30 (by decide) (by decide)
  have hd : Buffer (avx2Stack s 30).mem (avx2StackPtr s 29) 256 :=
    avx2Stack_buffer hwf 29 30 (by decide) (by decide)
  have hsep := avx2Stack_separate s 29 21 (by decide)
  have hbits : initial.mem.readAt (avx2StackPtr s 21) 320 =
      WordWindow.scalarBuffer scalar :=
    nafSetup_scalar_buffer _ _ _ scalar hs hsep
      (avx2Stack_zero hwf 21 30 320 (by decide) (by decide))
  obtain ⟨E', hrun, _, hframe⟩ := avx2_naf5_loop_run p g 256 (entryLoopEnv E g s)
    (avx2StackPtr s 21) (avx2StackPtr s 29) scalar 0 0 initial (by decide)
    (nafSetup_buffer hs) hbits (nafSetup_buffer hd)
    (by simp [entryLoopEnv, avx2EntryEnv, mlir_env]) hsep
  have hnormalized := avx2EntryEnv_loop E g s
  change loopEnv5 (entryLoopEnv E g s) (avx2StackPtr s 21) 0 0 =
    entryLoopEnv E g s at hnormalized
  rw [hnormalized] at hrun hframe
  refine ⟨E', ?_, hframe⟩
  exact (avx2_entry_run p g E s input scalar hwf hinput hscalar harg).trans
    (by simpa only [nafPhase, initial, entryLoopEnv, Fin.val_zero, pow_zero, Nat.div_one] using hrun)

/-- Exact constants and object registers consumed by the second emitter. -/
def SecondNAFReady (E : ⟪avx2Kernel.Γ⟫) (digits scratch : Pointer) : Prop :=
  E ⊨ [%1 := .value 0#8, %2 := .value 256#64, %3 := .value 32#64,
    %4 := .value 0#64, %5 := .value 6#64, %6 := .value 63#64,
    %8 := .value 8#64, %10 := .value 1#64, %15 := .value 56#64,
    %16 := .value 255#64, %17 := .value 127#64, %18 := .value 248#64,
    %257 := .value scratch, %265 := .value digits]

theorem setupInput8_of_ready (E : ⟪avx2Kernel.Γ⟫) (digits scratch : Pointer)
    (h : SecondNAFReady E digits scratch) : setupInput8 E digits scratch = E := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h8, h10, h15, h16, h17, h18, hs, hd⟩
  unfold setupInput8
  rw [Env.write_of_read E (%1) h1, Env.write_of_read E (%2) h2, Env.write_of_read E (%3) h3,
    Env.write_of_read E (%4) h4, Env.write_of_read E (%257) hs, Env.write_of_read E (%265) hd]

theorem setupResult8_loop (E : ⟪avx2Kernel.Γ⟫) (digits scratch : Pointer)
    (h : SecondNAFReady E digits scratch) :
    loopEnv8 ((setupResult8 E digits scratch)[%301 := .value 0#64]) scratch 0 0 =
      (setupResult8 E digits scratch)[%301 := .value 0#64] := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h8, h10, h15, h16, h17, h18, hs, hd⟩
  apply loopEnv8_of_reads <;> simp_all [setupResult8, setupInput8, mlir_env]

theorem setupResult8_frame (E : ⟪avx2Kernel.Γ⟫) (digits scratch : Pointer)
    (h : SecondNAFReady E digits scratch) :
    RegisterFrame 298 327 E ((setupResult8 E digits scratch)[%301 := .value 0#64]) := by
  unfold setupResult8
  rw [setupInput8_of_ready E digits scratch h]
  iterate 4 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

/-- The complete second emitter, with an exact successor and frame. Its only
scalar assumption identifies the caller's 32 input bytes. -/
theorem second_naf_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (digits scratch input : Pointer)
    (scalar : BitVec 256) (hready : SecondNAFReady E digits scratch)
    (hdigits : Buffer s.mem digits 256) (hscratch : Buffer s.mem scratch 40)
    (hinput : Buffer s.mem input 32) (hdi : digits.id ≠ input.id)
    (hsi : scratch.id ≠ input.id) (hds : digits.id ≠ scratch.id)
    (hscalar : s.mem.readAt input 256 = scalar) (harg : E.args 3 = .value input)
    (hzero : s.mem.readAt scratch 320 = 0) :
    ∃ E' : ⟪avx2Kernel.Γ⟫,
      (avx2Kernel p g).runFrom E 7 s =
        (avx2Kernel p g).runFrom E' 14 (nafPhase 8 s digits scratch scalar) ∧
      RegisterFrame 298 327 E E' := by
  let initial := nafInitialized s digits scratch scalar
  let next := (setupResult8 E digits scratch)[%301 := .value 0#64]
  have hsetup := setup8_run p g E s digits scratch input scalar hdigits hscratch
    hinput hdi hsi hscalar harg
  rw [setupInput8_of_ready E digits scratch hready] at hsetup
  obtain ⟨E', hrun, _, hframe⟩ := avx2_naf8_loop_run p g 256 next scratch digits
    scalar 0 0 initial (by decide) (nafSetup_buffer hscratch)
    (nafSetup_scalar_buffer s digits scratch scalar hscratch hds hzero)
    (nafSetup_buffer hdigits) (by simp [next, setupResult8, setupInput8, mlir_env]) hds
  have hnormalized := setupResult8_loop E digits scratch hready
  change loopEnv8 next scratch 0 0 = next at hnormalized
  rw [hnormalized] at hrun hframe
  refine ⟨E', hsetup.trans ?_, (setupResult8_frame E digits scratch hready).trans
    (hframe.weaken (by decide) (by decide))⟩
  simpa only [nafPhase, initial, Fin.val_zero, pow_zero, Nat.div_one] using hrun

/-- Concrete state after the complete scalar prelude. -/
def prefixState (s : GlobalState) (a b : BitVec 256) : GlobalState :=
  nafPhase 8
    (nafPhase 5 (avx2Stack s 30) (avx2StackPtr s 29) (avx2StackPtr s 21) a)
    (avx2StackPtr s 28) (avx2StackPtr s 20) b

/-- The actual entry, both full NAF loops and descending scan compose. Every
live-in value below register 268 is preserved, including all point scratch
objects and global-table pointers needed by the successor block. -/
theorem prefix_to_table_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (inputA inputB : Pointer)
    (a b : BitVec 256) (hwf : s.WF)
    (ha : Buffer s.mem inputA 32) (hb : Buffer s.mem inputB 32)
    (haRead : s.mem.readAt inputA 256 = a) (hbRead : s.mem.readAt inputB 256 = b)
    (haArg : E.args 1 = .value inputA) (hbArg : E.args 3 = .value inputB) :
    ∃ E' : ⟪avx2Kernel.Γ⟫,
      (avx2Kernel p g).runFrom E 0 s =
        (avx2Kernel p g).runFrom E' 15 (prefixState s a b) ∧
      RegisterFrame 268 421 (entryLoopEnv E g s) E' ∧
      E'.read (%412) = .value (BitVec.ofNat 64
        (startIndex (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255)) := by
  let sa := nafPhase 5 (avx2Stack s 30) (avx2StackPtr s 29) (avx2StackPtr s 21) a
  let digitsA := avx2StackPtr s 29
  let digitsB := avx2StackPtr s 28
  let scratchB := avx2StackPtr s 20
  obtain ⟨E5, hrun5, hframe5⟩ := first_naf_run p g E s inputA a hwf ha haRead haArg
  have hready8 : SecondNAFReady E5 digitsB scratchB := by
    unfold SecondNAFReady
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      rw [hframe5.read _ (by decide)]
      simp [entryLoopEnv, avx2EntryEnv, digitsB, scratchB, mlir_env]
  have hbufA : Buffer sa.mem digitsA 256 :=
    nafPhase_buffer 5 _ _ _ a (avx2Stack_buffer hwf 29 30 (by decide) (by decide))
  have hbufB : Buffer sa.mem digitsB 256 :=
    nafPhase_buffer 5 _ _ _ a (avx2Stack_buffer hwf 28 30 (by decide) (by decide))
  have hscratchB : Buffer sa.mem scratchB 40 :=
    nafPhase_buffer 5 _ _ _ a (avx2Stack_buffer hwf 20 30 (by decide) (by decide))
  have hinputB : Buffer sa.mem inputB 32 :=
    nafPhase_buffer 5 _ _ _ a (avx2Stack_existing hwf hb 30)
  have hreadB : sa.mem.readAt inputB 256 = b := by
    rw [nafPhase_read_other 5 _ _ _ inputB a 256
      (avx2Stack_separate_caller hwf hb 29) (avx2Stack_separate_caller hwf hb 21),
      avx2Stack_read_existing hwf hb 30 256, hbRead]
  have hzeroB : sa.mem.readAt scratchB 320 = 0 := by
    rw [nafPhase_read_other 5 _ _ _ scratchB a 320
      (avx2Stack_separate s 29 20 (by decide))
      (avx2Stack_separate s 21 20 (by decide)),
      avx2Stack_zero hwf 20 30 320 (by decide) (by decide)]
  have hargB : E5.args 3 = .value inputB := by
    rw [hframe5.arguments]
    exact hbArg
  obtain ⟨E8, hrun8, hframe8⟩ := second_naf_run p g E5 sa digitsB scratchB inputB b
    hready8 hbufB hscratchB hinputB (avx2Stack_separate_caller hwf hb 28)
    (avx2Stack_separate_caller hwf hb 20) (avx2Stack_separate s 28 20 (by decide))
    hreadB hargB hzeroB
  have hframe58 : RegisterFrame 268 327 (entryLoopEnv E g s) E8 :=
    (hframe5.weaken (by decide) (by decide)).trans
      (hframe8.weaken (by decide) (by decide))
  have htwo : E8.read (%2) = .value 256#64 := by
    rw [hframe58.read _ (by decide)]
    simp [entryLoopEnv, avx2EntryEnv, mlir_env]
  have hscanReady : ScanReady E8 digitsA digitsB := by
    constructor
    all_goals
      rw [hframe58.read _ (by decide)]
      simp [entryLoopEnv, avx2EntryEnv, digitsA, digitsB, mlir_env]
  let scanStart := E8[%411 := .value 256#64]
  have hscanReady' : ScanReady scanStart digitsA digitsB := hscanReady.back 256
  have hreadDigitsA (i : Fin 256) :
      (prefixState s a b).mem.readAt (digitsA.add (BitVec.ofNat 64 i.val)) 8 =
        Execution.nafByte 5 a.toNat i.val := by
    unfold prefixState
    rw [nafPhase_read_other 8 sa digitsB scratchB
      (digitsA.add (BitVec.ofNat 64 i.val)) b 8
      (by simpa [digitsA, digitsB] using avx2Stack_separate s 28 29 (by decide))
      (by simpa [digitsA, scratchB] using avx2Stack_separate s 20 29 (by decide))]
    exact nafPhase_digits 5 (Or.inl rfl) _ digitsA (avx2StackPtr s 21) a
      (avx2Stack_buffer hwf 29 30 (by decide) (by decide))
      (avx2Stack_separate s 21 29 (by decide)) i
  have hreadDigitsB (i : Fin 256) :
      (prefixState s a b).mem.readAt (digitsB.add (BitVec.ofNat 64 i.val)) 8 =
        Execution.nafByte 8 b.toNat i.val :=
    nafPhase_digits 8 (Or.inr rfl) sa digitsB scratchB b hbufB
      (avx2Stack_separate s 20 28 (by decide)) i
  obtain ⟨ES, hrunScan, _, hframeScan, hindex⟩ := scan_naf_run p g digitsA digitsB
    a.toNat b.toNat (prefixState s a b)
    (nafPhase_buffer 8 sa digitsB scratchB b hbufA)
    (nafPhase_buffer 8 sa digitsB scratchB b hbufB)
    hreadDigitsA hreadDigitsB scanStart hscanReady' (by simp [scanStart, mlir_env])
  have hentry := scan_entry_run p g E8 (prefixState s a b)
  rw [htwo] at hentry
  have hframeStart : RegisterFrame 268 421 (entryLoopEnv E g s) scanStart :=
    (hframe58.weaken (by decide) (by decide)).write _ _ (by decide)
  refine ⟨ES, hrun5.trans (hrun8.trans (hentry.trans hrunScan)),
    hframeStart.trans (hframeScan.weaken (by decide) (by decide)), hindex⟩

theorem prefixState_buffer (s : GlobalState) (a b : BitVec 256)
    (hwf : s.WF) (h : Buffer s.mem q bytes) :
    Buffer (prefixState s a b).mem q bytes :=
  nafPhase_buffer 8 _ _ _ b (nafPhase_buffer 5 _ _ _ a (avx2Stack_existing hwf h 30))

theorem prefixState_stack_buffer (s : GlobalState) (a b : BitVec 256)
    (hwf : s.WF) (i : Fin 30) (hsize : avx2StackSize i.val < 2 ^ 63) :
    Buffer (prefixState s a b).mem (avx2StackPtr s i.val) (avx2StackSize i.val) :=
  nafPhase_buffer 8 _ _ _ b (nafPhase_buffer 5 _ _ _ a
    (avx2Stack_buffer hwf i.val 30 i.isLt hsize))

theorem prefixState_wf (s : GlobalState) (a b : BitVec 256) (hwf : s.WF) :
    (prefixState s a b).WF :=
  nafPhase_wf 8 _ _ _ b (nafPhase_wf 5 _ _ _ a (avx2Stack_wf hwf 30))

/-- Every readable caller object is unchanged throughout the complete prelude. -/
theorem prefixState_read (s : GlobalState) (a b : BitVec 256) (hwf : s.WF)
    (q : Pointer) (bytes bits : Nat) (h : Buffer s.mem q bytes) :
    (prefixState s a b).mem.readAt q bits = s.mem.readAt q bits := by
  unfold prefixState
  rw [nafPhase_read_other 8 _ _ _ q b bits
    (avx2Stack_separate_caller hwf h 28) (avx2Stack_separate_caller hwf h 20),
    nafPhase_read_other 5 _ _ _ q a bits
    (avx2Stack_separate_caller hwf h 29) (avx2Stack_separate_caller hwf h 21),
    avx2Stack_read_existing hwf h 30 bits]

theorem prefixState_point (s : GlobalState) (a b : BitVec 256) (hwf : s.WF)
    (point : Pointer) (hpoint : Buffer s.mem point 160) :
    Conformance.BackendExecution.readPoint (prefixState s a b) point =
      Conformance.BackendExecution.readPoint s point := by
  have hcoordinate (c : Fin 4) :
      Conformance.BackendExecution.readCoordinate (prefixState s a b) point c =
        Conformance.BackendExecution.readCoordinate s point c := by
    have hwords : (fun limb : Fin 5 => (prefixState s a b).mem.readAt
        (point.add (BitVec.ofNat 64 (40 * c.val + 8 * limb.val))) 64) =
        (fun limb : Fin 5 => s.mem.readAt
          (point.add (BitVec.ofNat 64 (40 * c.val + 8 * limb.val))) 64) := by
      funext limb
      exact prefixState_read s a b hwf _ 8 64
        (hpoint.slice (40 * c.val + 8 * limb.val) 8 (by
          have := c.isLt; have := limb.isLt; omega))
    unfold Conformance.BackendExecution.readCoordinate
    rw [hwords]
  simp only [Conformance.BackendExecution.readPoint, hcoordinate]

theorem prefixState_pointLimbs (s : GlobalState) (a b : BitVec 256) (hwf : s.WF)
    (point : Pointer) (hpoint : Buffer s.mem point 160) (hlimbs : serialLimbsBounded s point) :
    serialLimbsBounded (prefixState s a b) point := by
  intro c limb
  rw [prefixState_read s a b hwf _ 8 64
    (hpoint.slice (40 * c.val + 8 * limb.val) 8 (by
      have := c.isLt; have := limb.isLt; omega))]
  exact hlimbs c limb

/-- Stack-object indices in block 15's exact first-use order. -/
def setupStackIndex : Fin 21 → Fin 30 :=
  ![19, 18, 26, 12, 10, 9, 25, 17, 16, 14, 13, 24, 3, 1, 0, 23, 8, 7, 5, 4, 22]

def stackSetupSlots (s : GlobalState) : SetupSlots :=
  fun i => avx2StackPtr s (setupStackIndex i).val

theorem setupStackIndex_size : ∀ i : Fin 21, avx2StackSize (setupStackIndex i).val = 160 := by
  decide +kernel

def scalarStartIndex (a b : BitVec 256) : Fin 256 :=
  ⟨startIndex (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255,
    by have := startIndex_le (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255; omega⟩

set_option maxHeartbeats 1000000 in
/-- Complete actual prelude into the point ladder, conditional only on the
separately compiled dynamic table constructor. The state at the first doubling
has the actual table values, live-memory frame and exact packed identity. -/
theorem prefix_to_ladder_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (htable : TableContract p.call0) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (inputA inputB point : Pointer) (a b : BitVec 256) (hwf : s.WF)
    (ha : Buffer s.mem inputA 32) (hb : Buffer s.mem inputB 32)
    (hpoint : Buffer s.mem point 160) (hlimbs : serialLimbsBounded s point)
    (haRead : s.mem.readAt inputA 256 = a) (hbRead : s.mem.readAt inputB 256 = b)
    (haArg : E.args 1 = .value inputA) (hbArg : E.args 3 = .value inputB)
    (hpointArg : E.args 2 = .value point) :
    ∃ (ES : ⟪avx2Kernel.Γ⟫) (s' : GlobalState),
      (avx2Kernel p g).runFrom E 0 s =
        (avx2Kernel p g).runFrom
          (tableSetupResult ES (stackSetupSlots s) (avx2StackPtr s 27) (scalarStartIndex a b))
          18 s' ∧
      RegisterFrame 268 421 (entryLoopEnv E g s) ES ∧
      TableFrame (prefixState s a b) s' (avx2StackPtr s 27) ∧
      ∀ k : Fin 8,
        let cached := packedPoint s'.mem
          ((avx2StackPtr s 27).add (BitVec.ofNat 64 (160 * k.val)))
        Avx2PointAdd.pointReduced cached ∧
        Avx2PointAdd.pointValue cached = PointArithmetic.avx2Cache
          (Tables.avx2Width5 (Conformance.BackendExecution.readPoint s point) k) := by
  obtain ⟨ES, hrun, hframe, hindex⟩ :=
    prefix_to_table_run p g E s inputA inputB a b hwf ha hb haRead hbRead haArg hbArg
  have hready : TableSetupReady ES (stackSetupSlots s) (avx2StackPtr s 27)
      (scalarStartIndex a b) := by
    unfold TableSetupReady
    refine ⟨(hframe.read (%3) (by decide)).trans ?_,
      (hframe.read (%20) (by decide)).trans ?_,
      (hframe.read (%21) (by decide)).trans ?_,
      (hframe.read (%22) (by decide)).trans ?_,
      (hframe.read (%24) (by decide)).trans ?_,
      (hframe.read (%25) (by decide)).trans ?_,
      (hframe.read (%256) (by decide)).trans ?_,
      (hframe.read (%255) (by decide)).trans ?_,
      (hframe.read (%263) (by decide)).trans ?_,
      (hframe.read (%249) (by decide)).trans ?_,
      (hframe.read (%247) (by decide)).trans ?_,
      (hframe.read (%246) (by decide)).trans ?_,
      (hframe.read (%262) (by decide)).trans ?_,
      (hframe.read (%254) (by decide)).trans ?_,
      (hframe.read (%253) (by decide)).trans ?_,
      (hframe.read (%251) (by decide)).trans ?_,
      (hframe.read (%250) (by decide)).trans ?_,
      (hframe.read (%261) (by decide)).trans ?_,
      (hframe.read (%240) (by decide)).trans ?_,
      (hframe.read (%238) (by decide)).trans ?_,
      (hframe.read (%237) (by decide)).trans ?_,
      (hframe.read (%260) (by decide)).trans ?_,
      (hframe.read (%245) (by decide)).trans ?_,
      (hframe.read (%244) (by decide)).trans ?_,
      (hframe.read (%242) (by decide)).trans ?_,
      (hframe.read (%241) (by decide)).trans ?_,
      (hframe.read (%259) (by decide)).trans ?_,
      (hframe.read (%264) (by decide)).trans ?_, hindex⟩
    all_goals
      simp [entryLoopEnv, avx2EntryEnv, stackSetupSlots, setupStackIndex, mlir_env] <;>
        decide +kernel
  have harg : ES.args 2 = .value point := by
    rw [hframe.arguments]
    exact hpointArg
  have hslots (i : Fin 21) : Buffer (prefixState s a b).mem (stackSetupSlots s i) 160 := by
    have hsize : avx2StackSize (setupStackIndex i).val < 2 ^ 63 := by
      rw [setupStackIndex_size]; decide
    simpa only [stackSetupSlots, setupStackIndex_size] using
      prefixState_stack_buffer s a b hwf (setupStackIndex i) hsize
  obtain ⟨s', htableRun, htableFrame, hvalues⟩ := table_setup_run p g htable ES
    (stackSetupSlots s) (avx2StackPtr s 27) point (scalarStartIndex a b)
    (prefixState s a b) (prefixState_wf s a b hwf) harg
    (prefixState_stack_buffer s a b hwf 27 (by decide))
    (prefixState_buffer s a b hwf hpoint)
    (Range.disjoint_of_id_ne (avx2Stack_separate_caller hwf hpoint 27))
    (prefixState_pointLimbs s a b hwf point hpoint hlimbs) hslots
  rw [tableSetupInput_of_ready ES _ _ _ hready] at htableRun
  refine ⟨ES, s', hrun.trans htableRun, hframe, htableFrame, ?_⟩
  simpa only [prefixState_point s a b hwf point hpoint] using hvalues

end Agave.Ed25519.DoubleBase.ExecutionAvx2
