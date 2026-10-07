import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorEntryStart
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorEntryRegisters
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorLoop

namespace Agave.Ed25519.Tables.SerialConstructorEntry
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.RIR (PrefixEq completedState completedState_writesOnly completedState_readPoint)
open DoubleBase.SerialContracts (readPoint readProjective readCached)
open SerialConstructorStack
open SerialConstructorCallFrame (slots)
open SerialConstructorState (Frame)
open SerialConstructorEntrySuffix
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- The exact prefix supplies every address used by the original suffix. -/
theorem suffixInput_of_prefix (E F : ⟪SerialConstructor.kernel.Γ⟫)
    (g : SerialConstructor.Globals) (s : GlobalState) (input : Pointer)
    (hf : PrefixEq (initial E g s) F 37)
    (h37 : F.read (%37) = .value (input.add 40))
    (h87 : F.read (%87) = .value (input.add 80)) :
    suffixInput F (slots s) (stackPtr s 7) input = F := by
  have h1 : F.read (%1) = .value (40#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h2 : F.read (%2) = .value (48#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h3 : F.read (%3) = .value (56#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h4 : F.read (%4) = .value (64#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h5 : F.read (%5) = .value (72#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h6 : F.read (%6) = .value (8#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h7 : F.read (%7) = .value (16#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h8 : F.read (%8) = .value (24#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h9 : F.read (%9) = .value (32#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h15 : F.read (%15) = .value (80#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h16 : F.read (%16) = .value (120#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h18 : F.read (%18) = .value (160#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h19 : F.read (%19) = .value (320#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h20 : F.read (%20) = .value (480#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h21 : F.read (%21) = .value (640#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h22 : F.read (%22) = .value (800#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h23 : F.read (%23) = .value (960#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h24 : F.read (%24) = .value (1120#64) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h29 : F.read (%29) = .value (stackPtr s 0) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h30 : F.read (%30) = .value (stackPtr s 1) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h31 : F.read (%31) = .value (stackPtr s 2) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h32 : F.read (%32) = .value (stackPtr s 3) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h33 : F.read (%33) = .value (stackPtr s 4) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h34 : F.read (%34) = .value (stackPtr s 5) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h35 : F.read (%35) = .value (stackPtr s 6) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  have h36 : F.read (%36) = .value (stackPtr s 7) := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    simp [initial, constants, mlir_env]
  change F.read (%29) = .value (slots s 0) at h29
  change F.read (%30) = .value (slots s 1) at h30
  change F.read (%31) = .value (slots s 2) at h31
  change F.read (%32) = .value (slots s 3) at h32
  change F.read (%33) = .value (slots s 4) at h33
  change F.read (%34) = .value (slots s 5) at h34
  change F.read (%35) = .value (slots s 6) at h35
  change F.read (%37) = .value (input.add 40#64) at h37
  change F.read (%87) = .value (input.add 80#64) at h87
  unfold suffixInput
  rw [Env.write_of_read F (%1) h1,
    Env.write_of_read F (%2) h2,
    Env.write_of_read F (%3) h3,
    Env.write_of_read F (%4) h4,
    Env.write_of_read F (%5) h5,
    Env.write_of_read F (%6) h6,
    Env.write_of_read F (%7) h7,
    Env.write_of_read F (%8) h8,
    Env.write_of_read F (%9) h9,
    Env.write_of_read F (%15) h15,
    Env.write_of_read F (%16) h16,
    Env.write_of_read F (%18) h18,
    Env.write_of_read F (%19) h19,
    Env.write_of_read F (%20) h20,
    Env.write_of_read F (%21) h21,
    Env.write_of_read F (%22) h22,
    Env.write_of_read F (%23) h23,
    Env.write_of_read F (%24) h24,
    Env.write_of_read F (%29) h29,
    Env.write_of_read F (%30) h30,
    Env.write_of_read F (%31) h31,
    Env.write_of_read F (%32) h32,
    Env.write_of_read F (%33) h33,
    Env.write_of_read F (%34) h34,
    Env.write_of_read F (%35) h35,
    Env.write_of_read F (%36) h36,
    Env.write_of_read F (%37) h37,
    Env.write_of_read F (%87) h87]

/-- Complete original entry, reaching the loop with its mathematical invariant. -/
theorem entry_run (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (hp : p.call1 = (SerialPoint.double Encoding.Decompress.Execution.Pow2k.program.call).call)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (input : Pointer)
    (hwf : s.WF) (hg : SerialConstructorContext.GlobalsReady g s)
    (hi : Buffer s.mem input 160) (hA : SerialPoint.PointTight (readPoint s input))
    (harg : E.args 1 = .value input) :
    ∃ F t,
      (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).runFrom E 0 s =
        (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).runFrom F 2 t ∧
      PrefixEq (initial E g s) F 37 ∧
      Frame (slots s) (stackPtr s 7) (stack s 8) t ∧
      SerialConstructorLoopRegisters.Ready g (slots s) (stackPtr s 7) F ∧
      F.read (%140) = .value 0#64 ∧
      SerialConstructorState.Ready g (slots s) (stackPtr s 7) t ∧
      readPoint t (stackPtr s 5) = SerialConstructorArithmetic.double (readPoint s input) ∧
      readCached t (stackPtr s 7) = SerialConstructorArithmetic.entries (readPoint s input) 0 := by
  obtain ⟨M, hprefix, hregs, hframe, hready, hcache, hinput, h37, h87⟩ :=
    SerialConstructorEntryStart.entry_cache p g E s input hwf hg hi hA harg
  let v := SerialConstructorEntryStart.cacheState s g input
  let P := preparedState v (slots s) (stackPtr s 7) input
  have hpbuf : Buffer v.mem (stackPtr s 0) 120 := by
    simpa [SerialConstructorState.bytes,slots] using hready.scratch 0
  have hib : Buffer v.mem input 160 := hframe.buffer (stack_existing hwf hi 8)
  have hprep := preparedState_frame v (slots s) (stackPtr s 7) input hready.wf
    hready.tableBuffer hpbuf
  have hrp := hready.preserve hprep
  have hproj := preparedState_readProjective v (slots s) (stackPtr s 7) input hpbuf hib
    (stack_separate_caller hwf hi 7) (stack_separate_caller hwf hi 0)
  change readProjective P (stackPtr s 0) = readProjective v input at hproj
  have hAt : SerialPoint.PointTight (readPoint v input) := hinput.symm ▸ hA
  have hPt : SerialPoint.PointTight (readProjective P (stackPtr s 0)) := by
    rw [hproj]
    exact ⟨hAt.1,hAt.2.1,hAt.2.2.1,by intro i; change (0 : Nat) < 2^52; decide⟩
  obtain ⟨u,hcall,hu,hread,hbound⟩ := SerialPoint.Execution.double_contract
    P (stackPtr s 1) (stackPtr s 0) hrp.wf (hrp.point 1 (by decide))
    (by exact hrp.scratch 0)
    (Range.disjoint_of_id_ne (stack_separate s 1 0 (by decide))) hPt
  have hru := hrp.preserve (Frame.slot 1 hu)
  have hcall' : (SerialCacheExecution.primitives p).call1
      (.cons (.value (stackPtr s 1)) (.cons (.value (stackPtr s 0)) .nil)) P = .value (.nil,u) := by
    simpa only [SerialCacheExecution.primitives,hp] using hcall
  have hargM : M.args 1 = .value input := by
    rw [hregs.1]
    simpa only [initial, constants, Env.write_args] using harg
  have hin := suffixInput_of_prefix E M g s input hregs h37 h87
  have hsuffix := suffix_run (SerialCacheExecution.primitives p) g rfl M (slots s)
    (stackPtr s 7) input v u hargM hready.scratch hready.tableBuffer hib
    (hready.separateTable 6).symm (stack_separate_caller hwf hi 0)
    hcall' hru.wf hru.scratch
  rw [hin] at hsuffix
  let N := suffixResult M (slots s) (stackPtr s 7) input
  let F := N[%140 := .value 0#64]
  let t := completedState u (stackPtr s 5) (stackPtr s 1)
  have ht := completedState_writesOnly u (stackPtr s 5) (stackPtr s 1)
    hru.wf (hru.point 5 (by decide))
  have hrt := hru.preserve (Frame.slot 5 ht)
  have hfN : PrefixEq M N 100 := by
    have h := suffixResult_prefix M (slots s) (stackPtr s 7) input
    rwa [hin] at h
  have hfF : PrefixEq (initial E g s) F 37 :=
    (hregs.trans (hfN.mono (by decide))).write _ _ (by decide)
  have hcN : constants N g = N := constants_of_prefix E N g
    ((initial_prefix E g s).trans ((hregs.mono (by decide)).trans (hfN.mono (by decide))))
  have hrN := SerialConstructorLoopRegisters.suffix_ready M g (slots s) (stackPtr s 7) input hcN
  have hrF : SerialConstructorLoopRegisters.Ready g (slots s) (stackPtr s 7) F :=
    hrN.preserve ((PrefixEq.refl N 140).write (%140) (.value 0#64) (by decide))
  have h25 : N.read (%25) = .value 0#64 := by
    have hh := congrArg (fun Q : ⟪SerialConstructor.kernel.Γ⟫ => Q.read (%25)) hcN
    simpa [constants,mlir_env] using hh.symm
  have hbody : List.foldlM Instr.run E
      (SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).body s =
      .value (N,t) := by
    rw [← List.take_append_drop 117 (SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).body,
      List.foldlM_append,EffectM.bind_eq,hprefix,PoisonOr.value_bind]
    exact hsuffix
  have hexit : (SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).exit.run
      SerialConstructor.kernel.blockParams N t = .value ((F,.inr 2),t) := by
    simp [SerialConstructor.kernel.bb0,SerialConstructor.kernel.blockParams,Exit.run,
      Jump.run,Regs.read_cons,Regs.read_nil,Env.writeMany_cons,Env.writeMany_nil,h25,F,EffectM.pure_eq]
    rfl
  have hblock : (SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).run
      SerialConstructor.kernel.blockParams E s = .value ((F,.inr 2),t) := by
    rw [BasicBlock.run, EffectM.bind_eq, hbody, PoisonOr.value_bind]
    exact hexit
  refine ⟨F,t,?_,hfF,hframe.trans (hprep.trans ((Frame.slot 1 hu).trans (Frame.slot 5 ht))),
    hrF,by simp [F,mlir_env],hrt,?_,?_⟩
  · rw [Func.runFrom_eq,
      show (SerialConstructor.kernel (SerialCacheExecution.primitives p) g).blocks 0 =
        SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g from rfl,
      hblock]
    rfl
  · rw [completedState_readPoint u (stackPtr s 5) (stackPtr s 1)
      (hru.point 5 (by decide)) (hru.point 1 (by decide)) (stack_separate s 5 1 (by decide)) hbound,hread,hproj]
    change SerialPoint.asExtended (SerialPoint.doubleCompleted (readPoint v input)) = _
    rw [hinput]
  · have hzero := preparedState_readCached_zero v (slots s) (stackPtr s 7) input hready.wf
      hready.tableBuffer (hready.point 6 (by decide)) (hready.separateTable 0)
    rw [SerialConstructorState.cached_read_ne ht (stack_separate s 5 7 (by decide)),
      SerialConstructorState.cached_read_ne hu (stack_separate s 1 7 (by decide)),hzero]
    exact hcache

end Agave.Ed25519.Tables.SerialConstructorEntry
