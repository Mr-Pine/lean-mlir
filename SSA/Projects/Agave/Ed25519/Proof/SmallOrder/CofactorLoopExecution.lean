import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorCall
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorMemory

namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution SerialFieldMul
open Reduce64.Execution (SmallRange)
open Verifier.Execution.PointMulByPow2
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000

structure LoopRegisters (E : Env program.Γ) (completed projective temporary : Pointer) : Prop where
  one : E.read (%0) = .value 1#32
  length : E.read (%5) = .value 120#64
  temporaryBase : E.read (%7) = .value temporary
  projectiveBase : E.read (%8) = .value projective
  completedBase : E.read (%9) = .value completed
  completedT : E.read (%16) = .value (completed.add 120#64)
  completedY : E.read (%17) = .value (completed.add 40#64)
  completedZ : E.read (%18) = .value (completed.add 80#64)
  temporaryY : E.read (%19) = .value (temporary.add 40#64)
  temporaryZ : E.read (%20) = .value (temporary.add 80#64)

/-- Direct evaluation of one exact eight-instruction loop prefix. All three
field calls are discharged by the imported kernel theorem. -/
theorem loopPrefix_run (p : Primitives) (hfield : p.fieldMul = kernel.call)
    (E : Env program.Γ) (s : GlobalState) (completed projective temporary : Pointer)
    (n : BitVec 32) (hn : ¬ n.uaddOverflow 1#32)
    (he : LoopRegisters E completed projective temporary)
    (hcounter : E.read (%27) = .value n) (hwf : s.WF)
    (hc : SmallRange s.mem completed 160) (hp : SmallRange s.mem projective 120)
    (ht : SmallRange s.mem temporary 120) (hne : projective.id ≠ temporary.id)
    (hdouble : p.projectiveDouble (.cons (.value completed) (.cons (.value projective) .nil)) s =
      .value (.nil, doubleState s completed projective)) :
    List.foldlM Instr.run E (CofactorPhases.loopPrefix p) s =
      .value (E[%28 := .value (n + 1)], loopState s completed projective temporary) := by
  let s0 := doubleState s completed projective
  let s1 := mulState s0 temporary completed (completed.add 120#64)
  let s2 := mulState s1 (temporary.add 40#64) (completed.add 40#64) (completed.add 80#64)
  let s3 := mulState s2 (temporary.add 80#64) (completed.add 80#64) (completed.add 120#64)
  have wf0 : s0.WF := pointPost_wf s hwf _ _ _
  have wf1 : s1.WF := wf_storeLimbs wf0 _ _
  have wf2 : s2.WF := wf_storeLimbs wf1 _ _
  have hc0 : SmallRange s0.mem completed 160 := doubleState_range hc _ _
  have ht0 : SmallRange s0.mem temporary 120 := doubleState_range ht _ _
  have hc1 : SmallRange s1.mem completed 160 := mulState_range hc0 _ _ _
  have ht1 : SmallRange s1.mem temporary 120 := mulState_range ht0 _ _ _
  have hc2 : SmallRange s2.mem completed 160 := mulState_range hc1 _ _ _
  have ht2 : SmallRange s2.mem temporary 120 := mulState_range ht1 _ _ _
  have ht3 : SmallRange s3.mem temporary 120 := mulState_range ht2 _ _ _
  have hp3 : SmallRange s3.mem projective 120 :=
    mulState_range (mulState_range (mulState_range (doubleState_range hp _ _) _ _ _) _ _ _) _ _ _
  have hc00 := smallRange_add hc0 (k := 0) (count := 40) (by decide)
  have ht00 := smallRange_add ht0 (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hc00 ht00
  have h1 := kernel_call temporary completed (completed.add 120#64) s0 wf0 ht00 hc00
    (smallRange_add hc0 (k := 120) (by decide))
  have h2 := kernel_call (temporary.add 40#64) (completed.add 40#64) (completed.add 80#64) s1 wf1
    (smallRange_add ht1 (k := 40) (by decide))
    (smallRange_add hc1 (k := 40) (by decide)) (smallRange_add hc1 (k := 80) (by decide))
  have h3 := kernel_call (temporary.add 80#64) (completed.add 80#64) (completed.add 120#64) s2 wf2
    (smallRange_add ht2 (k := 80) (by decide))
    (smallRange_add hc2 (k := 80) (by decide)) (smallRange_add hc2 (k := 120) (by decide))
  change kernel.call _ s0 = .value (.nil, s1) at h1
  change kernel.call _ s1 = .value (.nil, s2) at h2
  change kernel.call _ s2 = .value (.nil, s3) at h3
  simp only [kernel.args] at h1 h2 h3
  have hcopy := run_memcpy (env := E[%28 := .value (n + 1)])
    (len := 120#64) (by decide : (120#64).toNat = 120)
    (Range.disjoint_of_id_ne hne) hp3.fits ht3.fits
  dsimp only [s0, s1, s2, s3] at h1 h2 h3 hcopy
  have hadd : BinOp.compute (.add {nuw := true}) (.value n) (.value 1#32) = .value (n + 1) := by
    simp [BinOp.compute, Operation.add, hn]
  simp (disch := decide) only [CofactorPhases.loopPrefix, program.bb3, List.take, List.foldlM_cons,
    List.foldlM_nil, Instr.run, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    he.one, he.length, he.temporaryBase, he.projectiveBase, he.completedBase, he.completedT,
    he.completedY, he.completedZ, he.temporaryY, he.temporaryZ, hcounter, hadd,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil, mlir_env,
    hfield, hdouble, h1, h2, h3, hcopy]
  rfl


structure FinalRegisters (E : Env program.Γ) (out completed projective : Pointer) : Prop where
  outBase : E.read (%arg0) = .value out
  completedBase : E.read (%6) = .value completed
  projectiveBase : E.read (%8) = .value projective

/-- The separate last block doubles once and performs all four exact field
multiplications before returning. -/
theorem finalBlock_run (p : Primitives) (hfield : p.fieldMul = kernel.call)
    (E : Env program.Γ) (s : GlobalState) (out completed projective : Pointer)
    (he : FinalRegisters E out completed projective) (hwf : s.WF)
    (hc : SmallRange s.mem completed 160) (ho : SmallRange s.mem out 160)
    (hdouble : p.projectiveDouble (.cons (.value completed) (.cons (.value projective) .nil)) s =
      .value (.nil, doubleState s completed projective)) :
    (program p).runFrom E 2 s = .value (.nil, finalState s out completed projective) := by
  let s0 := doubleState s completed projective
  let s1 := mulState s0 out completed (completed.add 120#64)
  let s2 := mulState s1 (out.add 40#64) (completed.add 40#64) (completed.add 80#64)
  let s3 := mulState s2 (out.add 80#64) (completed.add 80#64) (completed.add 120#64)
  let s4 := mulState s3 (out.add 120#64) completed (completed.add 40#64)
  have wf0 : s0.WF := pointPost_wf s hwf _ _ _
  have wf1 : s1.WF := wf_storeLimbs wf0 _ _
  have wf2 : s2.WF := wf_storeLimbs wf1 _ _
  have wf3 : s3.WF := wf_storeLimbs wf2 _ _
  have hc0 : SmallRange s0.mem completed 160 := doubleState_range hc _ _
  have ho0 : SmallRange s0.mem out 160 := doubleState_range ho _ _
  have hc1 : SmallRange s1.mem completed 160 := mulState_range hc0 _ _ _
  have ho1 : SmallRange s1.mem out 160 := mulState_range ho0 _ _ _
  have hc2 : SmallRange s2.mem completed 160 := mulState_range hc1 _ _ _
  have ho2 : SmallRange s2.mem out 160 := mulState_range ho1 _ _ _
  have hc3 : SmallRange s3.mem completed 160 := mulState_range hc2 _ _ _
  have ho3 : SmallRange s3.mem out 160 := mulState_range ho2 _ _ _
  have hc00 := smallRange_add hc0 (k := 0) (count := 40) (by decide)
  have ho00 := smallRange_add ho0 (k := 0) (count := 40) (by decide)
  have hc30 := smallRange_add hc3 (k := 0) (count := 40) (by decide)
  simp only [Pointer.add_zero] at hc00 ho00 hc30
  have h1 := kernel_call out completed (completed.add 120#64) s0 wf0 ho00 hc00
    (smallRange_add hc0 (k := 120) (by decide))
  have h2 := kernel_call (out.add 40#64) (completed.add 40#64) (completed.add 80#64) s1 wf1
    (smallRange_add ho1 (k := 40) (by decide))
    (smallRange_add hc1 (k := 40) (by decide)) (smallRange_add hc1 (k := 80) (by decide))
  have h3 := kernel_call (out.add 80#64) (completed.add 80#64) (completed.add 120#64) s2 wf2
    (smallRange_add ho2 (k := 80) (by decide))
    (smallRange_add hc2 (k := 80) (by decide)) (smallRange_add hc2 (k := 120) (by decide))
  have h4 := kernel_call (out.add 120#64) completed (completed.add 40#64) s3 wf3
    (smallRange_add ho3 (k := 120) (by decide)) hc30
    (smallRange_add hc3 (k := 40) (by decide))
  change kernel.call _ s0 = .value (.nil, s1) at h1
  change kernel.call _ s1 = .value (.nil, s2) at h2
  change kernel.call _ s2 = .value (.nil, s3) at h3
  change kernel.call _ s3 = .value (.nil, s4) at h4
  simp only [kernel.args] at h1 h2 h3 h4
  have gc120 := hc0.gep (k := 120) (by decide)
  have gc40 := hc1.gep (k := 40) (by decide)
  have gc80 := hc1.gep (k := 80) (by decide)
  have go40 := ho1.gep (k := 40) (by decide)
  have go80 := ho2.gep (k := 80) (by decide)
  have go120 := ho3.gep (k := 120) (by decide)
  norm_num only [Nat.cast_ofNat] at gc120 gc40 gc80 go40 go80 go120
  dsimp only [s0, s1, s2, s3, s4] at h1 h2 h3 h4 gc120 gc40 gc80 go40 go80 go120
  have houtArg : E.args 0 = .value out := he.outBase
  rw [Func.runFrom_eq, CofactorPhases.block_two]
  simp (disch := decide) only [BasicBlock.run, program.bb2, List.foldlM_cons,
    List.foldlM_nil, Instr.run, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil, mlir_env,
    he.outBase, houtArg, he.completedBase, he.projectiveBase,
    hfield, hdouble, h1, h2, h3, h4, GepIndex.inboundsOffset,
    EffectM.get_eq, List.map_cons, List.map_nil, Operation.gepInboundsIndex, gc120, gc40, gc80, go40, go80, go120,
    Exit.run]
  rfl


theorem loopState_wf (s : GlobalState) (completed projective temporary : Pointer) (hwf : s.WF) :
    (loopState s completed projective temporary).WF := by
  simp only [loopState, mulState, copyState, storeLimbs, GlobalState.WF_storeAt]
  exact pointPost_wf s hwf completed (doubleWordTrace (readPointWords s projective)) 5

/-- The two imported loop blocks and the separate final block compose with
no phase-run hypothesis; only the lower double's already proved call is used. -/
theorem two_loops_run (p : Primitives) (hfield : p.fieldMul = kernel.call)
    (hdouble : ∀ (out input : Pointer) (s : GlobalState), s.WF →
      SmallRange s.mem out 160 → SmallRange s.mem input 120 →
      p.projectiveDouble (.cons (.value out) (.cons (.value input) .nil)) s =
        .value (.nil, doubleState s out input))
    (E : Env program.Γ) (s : GlobalState) (out completedFinal completed projective temporary : Pointer)
    (hel : LoopRegisters E completed projective temporary)
    (hef : FinalRegisters E out completedFinal projective)
    (hcounter : E.read (%27) = .value 0#32) (hlimit : E.read (%14) = .value 2#32)
    (hwf : s.WF) (ho : SmallRange s.mem out 160) (hf : SmallRange s.mem completedFinal 160)
    (hc : SmallRange s.mem completed 160) (hp : SmallRange s.mem projective 120)
    (ht : SmallRange s.mem temporary 120) (hne : projective.id ≠ temporary.id) :
    (program p).runFrom E 3 s = .value (.nil, finalState
      (loopState (loopState s completed projective temporary) completed projective temporary)
        out completedFinal projective) := by
  let F1 := E[%28 := .value 1#32]
  let E1 := F1[%29 := .value 0#1, %27 := .value 1#32]
  let F2 := E1[%28 := .value 2#32]
  let E2 := F2[%29 := .value 1#1]
  let s1 := loopState s completed projective temporary
  let s2 := loopState s1 completed projective temporary
  have hpre0 : List.foldlM Instr.run E (CofactorPhases.loopPrefix p) s = .value (F1, s1) :=
    loopPrefix_run p hfield E s completed projective temporary 0 (by decide) hel hcounter hwf hc hp ht hne
      (hdouble completed projective s hwf hc hp)
  have hfirst := CofactorPhases.first_loop_edge p E F1 s s1 hpre0
    (by simp (disch := decide) [F1, mlir_env])
    (by simp (disch := decide) [F1, mlir_env, hlimit])
  have hel1 : LoopRegisters E1 completed projective temporary := by
    rcases hel with ⟨h0, h5, h7, h8, h9, h16, h17, h18, h19, h20⟩
    constructor <;> simp (disch := decide) [E1, F1, mlir_env, *]
  have hs1 : s1.WF := loopState_wf s _ _ _ hwf
  have hc1 : SmallRange s1.mem completed 160 := loopState_range hc _ _ _
  have hp1 : SmallRange s1.mem projective 120 := loopState_range hp _ _ _
  have ht1 : SmallRange s1.mem temporary 120 := loopState_range ht _ _ _
  have hpre1 : List.foldlM Instr.run E1 (CofactorPhases.loopPrefix p) s1 = .value (F2, s2) :=
    loopPrefix_run p hfield E1 s1 completed projective temporary 1 (by decide) hel1
      (by simp (disch := decide) [E1, mlir_env]) hs1 hc1 hp1 ht1 hne
      (hdouble completed projective s1 hs1 hc1 hp1)
  have hsecond := CofactorPhases.second_loop_edge p E1 F2 s1 s2 hpre1
    (by simp (disch := decide) [F2, mlir_env])
    (by simp (disch := decide) [F2, E1, F1, mlir_env, hlimit])
  have hef2 : FinalRegisters E2 out completedFinal projective := by
    rcases hef with ⟨hout, h6, h8⟩
    constructor <;> simp (disch := decide) [E2, F2, E1, F1, mlir_env, *]
    exact hout
  rw [hfirst, hsecond]
  exact finalBlock_run p hfield E2 s2 out completedFinal projective hef2
    (loopState_wf s1 _ _ _ hs1) (loopState_range (loopState_range hf _ _ _) _ _ _)
    (loopState_range (loopState_range ho _ _ _) _ _ _)
    (hdouble completedFinal projective s2 (loopState_wf s1 _ _ _ hs1)
      (loopState_range (loopState_range hf _ _ _) _ _ _)
      (loopState_range hp1 _ _ _))

end Agave.Ed25519.SmallOrder.Execution
