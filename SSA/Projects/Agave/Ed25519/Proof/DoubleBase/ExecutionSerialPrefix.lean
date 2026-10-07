import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialPrefixMemory

/-!
# Actual serial entry through both NAF loops and the highest-digit scan

The theorem starts from the two scalar pointer reads and memory well-formedness.
It executes the entry, both complete inlined emitters, and the descending scan.
No point operation is invoked before its final continuation at block 16.
-/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

def serialInitial5 (E : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) : ⟪serialKernel.Γ⟫ :=
  (serialEntryEnv E g s)[%45 := .value 0#64]

theorem serialInitial5_normalized (E : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) :
    loopEnv5 (serialInitial5 E g s) (serialStackPtr s 1) 0 0 = serialInitial5 E g s := by
  apply loopEnv5_of_reads
  all_goals simp [serialInitial5, serialEntryEnv, mlir_env]

/-- Execution of entry and the complete first emitter, with an exact retained
state for width-eight setup. -/
theorem serial_prefix5_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) (input : Pointer) (a : BitVec 256)
    (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (ha : s.mem.readAt input 256 = a) (harg : E.args 1 = .value input) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom E 0 s =
        (serialKernel p g).runFrom final 7 (serialNAFState5 s a) ∧
      PrefixEq (serialInitial5 E g s) final 43 := by
  let init := nafInitialized (serialStack s 12) (serialStackPtr s 11) (serialStackPtr s 1) a
  have hs : Buffer (serialStack s 12).mem (serialStackPtr s 1) 40 :=
    serialStack_buffer hwf 1 12 (by decide) (by decide)
  have hd : Buffer (serialStack s 12).mem (serialStackPtr s 11) 256 :=
    serialStack_buffer hwf 11 12 (by decide) (by decide)
  have hbits : init.mem.readAt (serialStackPtr s 1) 320 = NAF.WordWindow.scalarBuffer a :=
    nafSetup_scalar_buffer _ _ _ _ hs (serialStack_separate s 1 11 (by decide))
      (serialStack_words_zero s hwf 1)
  obtain ⟨final, hloop, _, hframe⟩ := serial_naf5_loop_run p g 256
    (serialInitial5 E g s) (serialStackPtr s 1) (serialStackPtr s 11) a 0 0 init
    (by decide) (nafSetup_buffer hs) hbits (nafSetup_buffer hd)
    (by simp [serialInitial5, serialEntryEnv, mlir_env])
    (serialStack_separate s 11 1 (by decide))
  rw [serialInitial5_normalized] at hloop hframe
  refine ⟨final, ?_, hframe⟩
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 0 = serialKernel.bb0 g from rfl,
    serial_entry_block E g s input a hwf hinput ha harg]
  simp only [PoisonOr.value_bind, Func.continue]
  rw [serial5_carry_entry p g]
  have hstart : (serialEntryEnv E g s)[%45 := (serialEntryEnv E g s).read (%43)] =
      serialInitial5 E g s := by
    simp [serialInitial5, serialEntryEnv, mlir_env]
  rw [hstart]
  simpa only [Fin.val_zero, pow_zero, Nat.div_one, init, serialNAFState5, emittedNAF] using hloop

/-- Registers established by entry remain available at width-eight setup. -/
theorem setupInput8_of_prefix (E F : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (hframe : PrefixEq (serialInitial5 E g s) F 43) :
    setupInput8 F (serialStackPtr s 10) (serialStackPtr s 0) = F := by
  have h1 : F.read (%1) = .value 0#8 := by
    rw [hframe.read (%1) (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h2 : F.read (%2) = .value 256#64 := by
    rw [hframe.read (%2) (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h3 : F.read (%3) = .value 32#64 := by
    rw [hframe.read (%3) (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h4 : F.read (%4) = .value 0#64 := by
    rw [hframe.read (%4) (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h30 : F.read (%30) = .value (serialStackPtr s 0) := by
    rw [hframe.read (%30) (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  have h40 : F.read (%40) = .value (serialStackPtr s 10) := by
    rw [hframe.read (%40) (by intro i ht he; cases he; decide)]
    simp [serialInitial5, serialEntryEnv, mlir_env]
  unfold setupInput8
  rw [Env.write_of_read F (%1) h1, Env.write_of_read F (%2) h2,
    Env.write_of_read F (%3) h3, Env.write_of_read F (%4) h4,
    Env.write_of_read F (%30) h30, Env.write_of_read F (%40) h40]

def serialInitial8 (F : ⟪serialKernel.Γ⟫) (s : GlobalState) : ⟪serialKernel.Γ⟫ :=
  (setupResult8 F (serialStackPtr s 10) (serialStackPtr s 0))[%76 := .value 0#64]

theorem serialInitial8_prefix (E F : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (hframe : PrefixEq (serialInitial5 E g s) F 43) :
    PrefixEq F (serialInitial8 F s) 43 := by
  unfold serialInitial8 setupResult8
  rw [setupInput8_of_prefix E F g s hframe]
  repeat' apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem serialInitial8_normalized (E F : ⟪serialKernel.Γ⟫) (g : SerialCFG.Globals)
    (s : GlobalState) (hframe : PrefixEq (serialInitial5 E g s) F 43) :
    loopEnv8 (serialInitial8 F s) (serialStackPtr s 0) 0 0 = serialInitial8 F s := by
  apply loopEnv8_of_reads
  all_goals simp [serialInitial8, setupResult8, setupInput8, mlir_env]
  all_goals first | rfl |
    (rw [hframe.read _ (by intro i ht he; cases he; decide)];
      simp [serialInitial5, serialEntryEnv, mlir_env])

/-- The second scalar is still the caller's value after the first emitter. -/
theorem serial_prefix5_scalarB (s : GlobalState) (a b : BitVec 256)
    (input : Pointer) (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (hb : s.mem.readAt input 256 = b) :
    (serialNAFState5 s a).mem.readAt input 256 = b := by
  rw [serialNAFState5_read_other _ _ _ _
    (serialStack_separate_caller hwf hinput 11)
    (serialStack_separate_caller hwf hinput 1),
    serialStack_read_existing hwf hinput, hb]

/-- Actual width-eight setup and complete emitter. The only scalar premise is
its original caller read; scratch bytes and all interior ranges are derived. -/
theorem serial_prefix8_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E F : ⟪serialKernel.Γ⟫) (s : GlobalState) (input : Pointer) (a b : BitVec 256)
    (hwf : s.WF) (hinput : Buffer s.mem input 32)
    (hb : s.mem.readAt input 256 = b) (harg : E.args 3 = .value input)
    (hframe : PrefixEq (serialInitial5 E g s) F 43) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom F 7 (serialNAFState5 s a) =
        (serialKernel p g).runFrom final 14 (serialNAFState8 s a b) ∧
      PrefixEq (serialInitial5 E g s) final 43 := by
  have hbaseS : Buffer (serialStack s 12).mem (serialStackPtr s 0) 40 :=
    serialStack_buffer hwf 0 12 (by decide) (by decide)
  have hbaseD : Buffer (serialStack s 12).mem (serialStackPtr s 10) 256 :=
    serialStack_buffer hwf 10 12 (by decide) (by decide)
  have hs := serialNAFState5_buffer (a := a) hbaseS
  have hd := serialNAFState5_buffer (a := a) hbaseD
  have hi := serialNAFState5_buffer (a := a) (serialStack_existing hwf hinput 12)
  have hread := serial_prefix5_scalarB s a b input hwf hinput hb
  have hargs : F.args 3 = .value input := by
    rw [hframe.1]
    simpa only [serialInitial5, serialEntryEnv, Env.write, Env.set] using harg
  have hsetup := serial8_setup_block F (serialNAFState5 s a)
    (serialStackPtr s 10) (serialStackPtr s 0) input b hd hs hi
    (serialStack_separate_caller hwf hinput 10)
    (serialStack_separate_caller hwf hinput 0) hread hargs
  rw [setupInput8_of_prefix E F g s hframe] at hsetup
  let init := nafInitialized (serialNAFState5 s a) (serialStackPtr s 10) (serialStackPtr s 0) b
  have hzero : (serialNAFState5 s a).mem.readAt (serialStackPtr s 0) 320 = 0 := by
    rw [serialNAFState5_read_other _ _ _ _
      (serialStack_separate s 11 0 (by decide)) (serialStack_separate s 1 0 (by decide))]
    exact serialStack_words_zero s hwf 0
  have hbits : init.mem.readAt (serialStackPtr s 0) 320 = NAF.WordWindow.scalarBuffer b :=
    nafSetup_scalar_buffer _ _ _ _ hs (serialStack_separate s 0 10 (by decide)) hzero
  obtain ⟨final, hloop, _, hloopframe⟩ := serial_naf8_loop_run p g 256
    (serialInitial8 F s) (serialStackPtr s 0) (serialStackPtr s 10) b 0 0 init
    (by decide) (nafSetup_buffer hs) hbits (nafSetup_buffer hd)
    (by simp [serialInitial8, setupResult8, setupInput8, mlir_env])
    (serialStack_separate s 10 0 (by decide))
  rw [serialInitial8_normalized E F g s hframe] at hloop hloopframe
  refine ⟨final, ?_, hframe.trans ((serialInitial8_prefix E F g s hframe).trans
    (hloopframe.mono (by decide)))⟩
  rw [Func.runFrom_eq, show (serialKernel p g).blocks 7 = serialKernel.bb7 from rfl, hsetup]
  simp only [PoisonOr.value_bind, Func.continue]
  rw [serial8_carry_entry p g]
  have hstart : (setupResult8 F (serialStackPtr s 10) (serialStackPtr s 0))[
      %76 := (setupResult8 F (serialStackPtr s 10) (serialStackPtr s 0)).read (%74)] =
      serialInitial8 F s := by
    simp [serialInitial8, setupResult8, setupInput8, mlir_env]
  rw [hstart]
  simpa only [Fin.val_zero, pow_zero, Nat.div_one, init, serialNAFState8, emittedNAF] using hloop

/-- Entry through both source-correct digit arrays, retaining the original
continuation and all persistent registers. -/
theorem serial_naf_prefix (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) (inputA inputB : Pointer) (a b : BitVec 256)
    (hwf : s.WF) (hA : Buffer s.mem inputA 32) (hB : Buffer s.mem inputB 32)
    (ha : s.mem.readAt inputA 256 = a) (hb : s.mem.readAt inputB 256 = b)
    (hargA : E.args 1 = .value inputA) (hargB : E.args 3 = .value inputB) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialKernel p g).runFrom E 0 s =
        (serialKernel p g).runFrom final 14 (serialNAFState8 s a b) ∧
      PrefixEq (serialInitial5 E g s) final 43 := by
  obtain ⟨F, hrun5, hframe5⟩ := serial_prefix5_run p g E s inputA a hwf hA ha hargA
  obtain ⟨final, hrun8, hframe8⟩ := serial_prefix8_run p g E F s inputB a b hwf hB hb hargB hframe5
  exact ⟨final, hrun5.trans hrun8, hframe8⟩

end Agave.Ed25519.DoubleBase.RIR
