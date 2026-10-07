import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline956Safety
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderInlinePrefixOperations

/-! The exact final sqrt-ratio inline tail. The only incoming facts concern
registers, live memory and the two candidate limb arrays at pc956. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
open LeanMLIR.RIR SerialFieldMul SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open Decode.InlinePrefix (vector_two carry_operation carry_vector_operation fold_operation)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem computeSafe761 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v759 r t b x y))) (.value ((v754 r t b x y))) = .value (v761 r t b x y) := safe761 r t b x y

theorem computeSafe762 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v760 r t b x y))) (.value ((v756 r t b x y))) = .value (v762 r t b x y) := safe762 r t b x y

theorem computeSafe782 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.mul {nsw := true, nuw := true}) (.value ((v779 r t b x y))) (.value (19#64)) = .value (v782 r t b x y) := safe782 r t b x y

theorem computeSafe783 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v781 r t b x y))) (.value ((v778 r t b x y))) = .value (v783 r t b x y) := safe783 r t b x y

theorem computeSafe790 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.mul {nsw := true, nuw := true}) (.value ((v786 r t b x y))) (.value (19#64)) = .value (v790 r t b x y) := safe790 r t b x y

theorem computeSafe791 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v782 r t b x y))) (.value ((v758 r t b x y))) = .value (v791 r t b x y) := safe791 r t b x y

theorem computeSafe792 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v780 r t b x y))) (.value ((v757 r t b x y))) = .value (v792 r t b x y) := safe792 r t b x y

theorem computeSafe793 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v791 r t b x y))) (.value (19#64)) = .value (v793 r t b x y) := safe793 r t b x y

theorem computeSafe795 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v761 r t b x y))) (.value ((v794 r t b x y))) = .value (v795 r t b x y) := safe795 r t b x y

theorem computeSafe797 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v762 r t b x y))) (.value ((v796 r t b x y))) = .value (v797 r t b x y) := safe797 r t b x y

theorem computeSafe799 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v792 r t b x y))) (.value ((v798 r t b x y))) = .value (v799 r t b x y) := safe799 r t b x y

theorem computeSafe801 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v783 r t b x y))) (.value ((v800 r t b x y))) = .value (v801 r t b x y) := safe801 r t b x y

theorem computeSafe803 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v802 r t b x y))) (.value ((v791 r t b x y))) = .value (v803 r t b x y) := safe803 r t b x y

theorem computeSafe808 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.add {nsw := true, nuw := true}) (.value ((v790 r t b x y))) (.value ((v767 r t b x y))) = .value (v808 r t b x y) := safe808 r t b x y

theorem computeSafe735 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.sub {nsw := true}) (.value 0#64) (.value (v734 r t b x y)) = .value (v735 r t b x y) := mask_safe b

theorem computeSafe811 (r t : Pointer) (b : BitVec 8) (x y : Words) : BinOp.compute (BinOp.sub {nsw := true}) (.value 0#64) (.value (v810 r t b x y)) = .value (v811 r t b x y) := mask_safe (v806 r t b x y)

def env957 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  E[%734 := .value (v734 r t b x y)]

theorem segment956 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 956 1
      E s = .value (env957 E r t b x y, s) := by
  have e733 : E.read (%733) = .value (b) := by
    simpa (disch := decide) only [mlir_env] using he.e733
  change List.foldlM Instr.run E
    (((program.entry sqrtRatioPrimitives g).body.drop 956).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e733, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env957, v734, throwUBIf, e733, mask_safe]

def env958 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env957 E r t b x y)[%735 := .value (v735 r t b x y)]

theorem segment957 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 957 1
      (env957 E r t b x y) s = .value (env958 E r t b x y, s) := by
  have e50 : (env957 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, mlir_env] using he.e50
  have e734 : (env957 E r t b x y).read (%734) = .value (v734 r t b x y) := rfl
  change List.foldlM Instr.run (env957 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 957).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e50, e734, computeSafe735, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env958, v735, throwUBIf, e50, e734, computeSafe735, mask_safe]

def env962 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env958 E r t b x y)[%736 := .value (v736 r t b x y),
    %737 := .value (v737 r t b x y),
    %738 := .value (v738 r t b x y),
    %739 := .value (v739 r t b x y)]

theorem segment958 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 958 4
      (env958 E r t b x y) s = .value (env962 E r t b x y, s) := by
  have e3 : (env958 E r t b x y).read (%3) = .value (8#64) := by
    simpa (disch := decide) only [env957, env958, mlir_env] using he.e3
  have e5 : (env958 E r t b x y).read (%5) = .value (24#64) := by
    simpa (disch := decide) only [env957, env958, mlir_env] using he.e5
  have e71 : (env958 E r t b x y).read (%71) = .value (t) := by
    simpa (disch := decide) only [env957, env958, mlir_env] using he.e71
  have e79 : (env958 E r t b x y).read (%79) = .value (r) := by
    simpa (disch := decide) only [env957, env958, mlir_env] using he.e79
  have gr8 := hr.gep (k := 8) (by decide)
  have gr24 := hr.gep (k := 24) (by decide)
  have gt8 := ht.gep (k := 8) (by decide)
  have gt24 := ht.gep (k := 24) (by decide)
  norm_num only [Nat.cast_ofNat] at gr8 gr24 gt8 gt24
  change List.foldlM Instr.run (env958 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 958).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e3, e5, e71, e79, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env962, v736, v737, v738, v739, throwUBIf, Operation.gepInboundsIndex, GepIndex.inboundsOffset, Operation.GepSignedRange, gr8, gr24, gt8, gt24, e3, e5, e71, e79, mask_safe]

def env966 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env962 E r t b x y)[%740 := Ty.wrap (v740 r t b x y),
    %741 := Ty.wrap (v741 r t b x y),
    %742 := Ty.wrap (v742 r t b x y),
    %743 := Ty.wrap (v743 r t b x y)]

theorem segment962 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 962 4
      (env962 E r t b x y) s = .value (env966 E r t b x y, s) := by
  have e71 : (env962 E r t b x y).read (%71) = .value (t) := by
    simpa (disch := decide) only [env957, env958, env962, mlir_env] using he.e71
  have e79 : (env962 E r t b x y).read (%79) = .value (r) := by
    simpa (disch := decide) only [env957, env958, env962, mlir_env] using he.e79
  have e736 : (env962 E r t b x y).read (%736) = .value (v736 r t b x y) := rfl
  have e737 : (env962 E r t b x y).read (%737) = .value (v737 r t b x y) := rfl
  have f79 := hr.fits_add (k := 0) (count := 16) (by decide)
  have l79 := Verifier.Execution.Dalek.smallRange_add hr (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at f79 l79
  have hx0 : s.mem.readAt (r.add 0#64) 64 = x 0 := by
    simpa [readLimbs] using congrFun hx 0
  have hx1 : s.mem.readAt (r.add 8#64) 64 = x 1 := by
    simpa [readLimbs] using congrFun hx 1
  have f71 := ht.fits_add (k := 0) (count := 16) (by decide)
  have l71 := Verifier.Execution.Dalek.smallRange_add ht (k := 0) (count := 16) (by decide)
  simp only [Pointer.add_zero] at f71 l71
  have hy0 : s.mem.readAt (t.add 0#64) 64 = y 0 := by
    simpa [readLimbs] using congrFun hy 0
  have hy1 : s.mem.readAt (t.add 8#64) 64 = y 1 := by
    simpa [readLimbs] using congrFun hy 1
  have f736 := hr.fits_add (k := 8) (count := 16) (by decide)
  have l736 := Verifier.Execution.Dalek.smallRange_add hr (k := 8) (count := 16) (by decide)
  have hx1 : s.mem.readAt (r.add 8#64) 64 = x 1 := by
    simpa [readLimbs] using congrFun hx 1
  have hx2 : s.mem.readAt (r.add 16#64) 64 = x 2 := by
    simpa [readLimbs] using congrFun hx 2
  have f737 := ht.fits_add (k := 8) (count := 16) (by decide)
  have l737 := Verifier.Execution.Dalek.smallRange_add ht (k := 8) (count := 16) (by decide)
  have hy1 : s.mem.readAt (t.add 8#64) 64 = y 1 := by
    simpa [readLimbs] using congrFun hy 1
  have hy2 : s.mem.readAt (t.add 16#64) 64 = y 2 := by
    simpa [readLimbs] using congrFun hy 2
  simp only [Pointer.add_zero] at hx0
  simp only [Pointer.add_zero] at hy0
  change List.foldlM Instr.run (env962 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 962).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e71, e79, e736, e737, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env966, v740, v741, v742, v743, throwUBIf, Operation.load, Operation.store, load_two_words, Pointer.add_add, Pointer.add_zero, f79, l79, hx0, hx1, f71, l71, hy0, hy1, f736, l736, hx1, hx2, f737, l737, hy1, hy2, v736, v737, v738, v739, e71, e79, e736, e737, mask_safe]

def env970 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env966 E r t b x y)[%744 := Ty.wrap (v744 r t b x y),
    %745 := Ty.wrap (v745 r t b x y),
    %746 := v746 r t b x y,
    %747 := Ty.wrap (v747 r t b x y)]

theorem segment966 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 966 4
      (env966 E r t b x y) s = .value (env970 E r t b x y, s) := by
  have e50 : (env966 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, mlir_env] using he.e50
  have e53 : (env966 E r t b x y).read (%53) = Ty.poisoned (.vec 2 64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, mlir_env] using he.e53
  have e735 : (env966 E r t b x y).read (%735) = .value (v735 r t b x y) := rfl
  have e740 : (env966 E r t b x y).read (%740) = Ty.wrap (v740 r t b x y) := rfl
  have e741 : (env966 E r t b x y).read (%741) = Ty.wrap (v741 r t b x y) := rfl
  have e742 : (env966 E r t b x y).read (%742) = Ty.wrap (v742 r t b x y) := rfl
  have e743 : (env966 E r t b x y).read (%743) = Ty.wrap (v743 r t b x y) := rfl
  change List.foldlM Instr.run (env966 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 966).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e50, e53, e735, e740, e741, e742, e743, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env970, v744, v745, v746, v747, throwUBIf, e50, e53, e735, e740, e741, e742, e743, mask_safe]

def env974 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env970 E r t b x y)[%748 := Ty.wrap (v748 r t b x y),
    %749 := Ty.wrap (v749 r t b x y),
    %750 := Ty.wrap (v750 r t b x y),
    %751 := .value (v751 r t b x y)]

theorem segment970 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 970 4
      (env970 E r t b x y) s = .value (env974 E r t b x y, s) := by
  have e50 : (env970 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, mlir_env] using he.e50
  have e740 : (env970 E r t b x y).read (%740) = Ty.wrap (v740 r t b x y) := rfl
  have e744 : (env970 E r t b x y).read (%744) = Ty.wrap (v744 r t b x y) := rfl
  have e745 : (env970 E r t b x y).read (%745) = Ty.wrap (v745 r t b x y) := rfl
  have e747 : (env970 E r t b x y).read (%747) = Ty.wrap (v747 r t b x y) := rfl
  change List.foldlM Instr.run (env970 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 970).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e50, e740, e744, e745, e747, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env974, v748, v749, v750, v751, throwUBIf, e50, e740, e744, e745, e747, mask_safe]

def env978 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env974 E r t b x y)[%752 := Ty.wrap (v752 r t b x y),
    %753 := .value (v753 r t b x y),
    %754 := .value (v754 r t b x y),
    %755 := .value (v755 r t b x y)]

theorem segment974 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 974 4
      (env974 E r t b x y) s = .value (env978 E r t b x y, s) := by
  have e7 : (env974 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, mlir_env] using he.e7
  have e10 : (env974 E r t b x y).read (%10) = .value (1#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, mlir_env] using he.e10
  have e50 : (env974 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, mlir_env] using he.e50
  have e742 : (env974 E r t b x y).read (%742) = Ty.wrap (v742 r t b x y) := rfl
  have e749 : (env974 E r t b x y).read (%749) = Ty.wrap (v749 r t b x y) := rfl
  have e751 : (env974 E r t b x y).read (%751) = .value (v751 r t b x y) := rfl
  change List.foldlM Instr.run (env974 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 974).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e10, e50, e742, e749, e751, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env978, v752, v753, v754, v755, throwUBIf, e7, e10, e50, e742, e749, e751, mask_safe]

def env982 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env978 E r t b x y)[%756 := .value (v756 r t b x y),
    %757 := .value (v757 r t b x y),
    %758 := .value (v758 r t b x y),
    %759 := .value (v759 r t b x y)]

theorem segment978 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 978 4
      (env978 E r t b x y) s = .value (env982 E r t b x y, s) := by
  have e7 : (env978 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, mlir_env] using he.e7
  have e8 : (env978 E r t b x y).read (%8) = .value (2251799813685247#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, mlir_env] using he.e8
  have e751 : (env978 E r t b x y).read (%751) = .value (v751 r t b x y) := rfl
  have e753 : (env978 E r t b x y).read (%753) = .value (v753 r t b x y) := rfl
  have e755 : (env978 E r t b x y).read (%755) = .value (v755 r t b x y) := rfl
  change List.foldlM Instr.run (env978 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 978).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e8, e751, e753, e755, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env982, v756, v757, v758, v759, throwUBIf, e7, e8, e751, e753, e755, mask_safe]

def env983 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env982 E r t b x y)[%760 := .value (v760 r t b x y)]

theorem segment982 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 982 1
      (env982 E r t b x y) s = .value (env983 E r t b x y, s) := by
  have e8 : (env982 E r t b x y).read (%8) = .value (2251799813685247#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, mlir_env] using he.e8
  have e753 : (env982 E r t b x y).read (%753) = .value (v753 r t b x y) := rfl
  change List.foldlM Instr.run (env982 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 982).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e8, e753, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env983, v760, throwUBIf, e8, e753, mask_safe]

def env984 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env983 E r t b x y)[%761 := .value (v761 r t b x y)]

theorem segment983 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 983 1
      (env983 E r t b x y) s = .value (env984 E r t b x y, s) := by
  have e754 : (env983 E r t b x y).read (%754) = .value (v754 r t b x y) := rfl
  have e759 : (env983 E r t b x y).read (%759) = .value (v759 r t b x y) := rfl
  change List.foldlM Instr.run (env983 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 983).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e754, e759, computeSafe761, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env984, v761, throwUBIf, e754, e759, computeSafe761, mask_safe]

def env985 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env984 E r t b x y)[%762 := .value (v762 r t b x y)]

theorem segment984 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 984 1
      (env984 E r t b x y) s = .value (env985 E r t b x y, s) := by
  have e756 : (env984 E r t b x y).read (%756) = .value (v756 r t b x y) := rfl
  have e760 : (env984 E r t b x y).read (%760) = .value (v760 r t b x y) := rfl
  change List.foldlM Instr.run (env984 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 984).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e756, e760, computeSafe762, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env985, v762, throwUBIf, e756, e760, computeSafe762, mask_safe]

def env986 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env985 E r t b x y)[%763 := .value (v763 r t b x y)]

theorem segment985 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 985 1
      (env985 E r t b x y) s = .value (env986 E r t b x y, s) := by
  have e54 : (env985 E r t b x y).read (%54) = .value (2251799813684944#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, mlir_env] using he.e54
  have e751 : (env985 E r t b x y).read (%751) = .value (v751 r t b x y) := rfl
  change List.foldlM Instr.run (env985 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 985).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e54, e751, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env986, v763, throwUBIf, e54, e751, mask_safe]

def env990 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env986 E r t b x y)[%764 := Ty.wrap (v764 r t b x y),
    %765 := Ty.wrap (v765 r t b x y),
    %766 := Ty.wrap (v766 r t b x y),
    %767 := .value (v767 r t b x y)]

theorem segment986 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 986 4
      (env986 E r t b x y) s = .value (env990 E r t b x y, s) := by
  have e8 : (env986 E r t b x y).read (%8) = .value (2251799813685247#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, mlir_env] using he.e8
  have e55 : (env986 E r t b x y).read (%55) = Ty.wrap (#v[36028797018963664#64, 36028797018963952#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, mlir_env] using he.e55
  have e56 : (env986 E r t b x y).read (%56) = Ty.wrap (#v[2251799813685232#64, 2251799813685232#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, mlir_env] using he.e56
  have e57 : (env986 E r t b x y).read (%57) = Ty.wrap (#v[51#64, 51#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, mlir_env] using he.e57
  have e750 : (env986 E r t b x y).read (%750) = Ty.wrap (v750 r t b x y) := rfl
  have e752 : (env986 E r t b x y).read (%752) = Ty.wrap (v752 r t b x y) := rfl
  have e763 : (env986 E r t b x y).read (%763) = .value (v763 r t b x y) := rfl
  change List.foldlM Instr.run (env986 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 986).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e8, e55, e56, e57, e750, e752, e763, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env990, v764, v765, v766, v767, throwUBIf, e8, e55, e56, e57, e750, e752, e763, mask_safe]

def env991 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env990 E r t b x y)[%768 := Ty.wrap (v768 r t b x y)]

theorem segment990 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 990 1
      (env990 E r t b x y) s = .value (env991 E r t b x y, s) := by
  have e58 : (env990 E r t b x y).read (%58) = Ty.wrap (#v[2251799813685247#64, 2251799813685247#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, mlir_env] using he.e58
  have e765 : (env990 E r t b x y).read (%765) = Ty.wrap (v765 r t b x y) := rfl
  change List.foldlM Instr.run (env990 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 990).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e58, e765, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env991, v768, throwUBIf, e58, e765, mask_safe]

def env992 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env991 E r t b x y)[%769 := Ty.wrap (v769 r t b x y)]

theorem segment991 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 991 1
      (env991 E r t b x y) s = .value (env992 E r t b x y, s) := by
  have e766 : (env991 E r t b x y).read (%766) = Ty.wrap (v766 r t b x y) := rfl
  have e768 : (env991 E r t b x y).read (%768) = Ty.wrap (v768 r t b x y) := rfl
  change List.foldlM Instr.run (env991 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 991).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e766, e768, safe769, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env992, v769, throwUBIf, e766, e768, safe769, mask_safe]

def env995 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env992 E r t b x y)[%770 := Ty.wrap (v770 r t b x y),
    %771 := Ty.wrap (v771 r t b x y),
    %772 := Ty.wrap (v772 r t b x y)]

theorem segment992 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 992 3
      (env992 E r t b x y) s = .value (env995 E r t b x y, s) := by
  have e738 : (env992 E r t b x y).read (%738) = .value (v738 r t b x y) := rfl
  have e739 : (env992 E r t b x y).read (%739) = .value (v739 r t b x y) := rfl
  have e752 : (env992 E r t b x y).read (%752) = Ty.wrap (v752 r t b x y) := rfl
  have e769 : (env992 E r t b x y).read (%769) = Ty.wrap (v769 r t b x y) := rfl
  have f738 := hr.fits_add (k := 24) (count := 16) (by decide)
  have l738 := Verifier.Execution.Dalek.smallRange_add hr (k := 24) (count := 16) (by decide)
  have hx3 : s.mem.readAt (r.add 24#64) 64 = x 3 := by
    simpa [readLimbs] using congrFun hx 3
  have hx4 : s.mem.readAt (r.add 32#64) 64 = x 4 := by
    simpa [readLimbs] using congrFun hx 4
  have f739 := ht.fits_add (k := 24) (count := 16) (by decide)
  have l739 := Verifier.Execution.Dalek.smallRange_add ht (k := 24) (count := 16) (by decide)
  have hy3 : s.mem.readAt (t.add 24#64) 64 = y 3 := by
    simpa [readLimbs] using congrFun hy 3
  have hy4 : s.mem.readAt (t.add 32#64) 64 = y 4 := by
    simpa [readLimbs] using congrFun hy 4
  change List.foldlM Instr.run (env992 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 992).take 3) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e738, e739, e752, e769, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env995, v770, v771, v772, throwUBIf, Operation.load, Operation.store, load_two_words, Pointer.add_add, Pointer.add_zero, f738, l738, hx3, hx4, f739, l739, hy3, hy4, v736, v737, v738, v739, e738, e739, e752, e769, mask_safe]

def env999 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env995 E r t b x y)[%773 := Ty.wrap (v773 r t b x y),
    %774 := Ty.wrap (v774 r t b x y),
    %775 := Ty.wrap (v775 r t b x y),
    %776 := .value (v776 r t b x y)]

theorem segment995 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 995 4
      (env995 E r t b x y) s = .value (env999 E r t b x y, s) := by
  have e10 : (env995 E r t b x y).read (%10) = .value (1#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, mlir_env] using he.e10
  have e747 : (env995 E r t b x y).read (%747) = Ty.wrap (v747 r t b x y) := rfl
  have e771 : (env995 E r t b x y).read (%771) = Ty.wrap (v771 r t b x y) := rfl
  have e772 : (env995 E r t b x y).read (%772) = Ty.wrap (v772 r t b x y) := rfl
  change List.foldlM Instr.run (env995 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 995).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e10, e747, e771, e772, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env999, v773, v774, v775, v776, throwUBIf, e10, e747, e771, e772, mask_safe]

def env1003 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env999 E r t b x y)[%777 := .value (v777 r t b x y),
    %778 := .value (v778 r t b x y),
    %779 := .value (v779 r t b x y),
    %780 := .value (v780 r t b x y)]

theorem segment999 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 999 4
      (env999 E r t b x y) s = .value (env1003 E r t b x y, s) := by
  have e7 : (env999 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, mlir_env] using he.e7
  have e8 : (env999 E r t b x y).read (%8) = .value (2251799813685247#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, mlir_env] using he.e8
  have e50 : (env999 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, mlir_env] using he.e50
  have e775 : (env999 E r t b x y).read (%775) = Ty.wrap (v775 r t b x y) := rfl
  have e776 : (env999 E r t b x y).read (%776) = .value (v776 r t b x y) := rfl
  change List.foldlM Instr.run (env999 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 999).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e8, e50, e775, e776, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1003, v777, v778, v779, v780, throwUBIf, e7, e8, e50, e775, e776, mask_safe]

def env1004 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1003 E r t b x y)[%781 := .value (v781 r t b x y)]

theorem segment1003 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1003 1
      (env1003 E r t b x y) s = .value (env1004 E r t b x y, s) := by
  have e8 : (env1003 E r t b x y).read (%8) = .value (2251799813685247#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, mlir_env] using he.e8
  have e776 : (env1003 E r t b x y).read (%776) = .value (v776 r t b x y) := rfl
  change List.foldlM Instr.run (env1003 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1003).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e8, e776, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1004, v781, throwUBIf, e8, e776, mask_safe]

def env1005 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1004 E r t b x y)[%782 := .value (v782 r t b x y)]

theorem segment1004 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1004 1
      (env1004 E r t b x y) s = .value (env1005 E r t b x y, s) := by
  have e9 : (env1004 E r t b x y).read (%9) = .value (19#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, mlir_env] using he.e9
  have e779 : (env1004 E r t b x y).read (%779) = .value (v779 r t b x y) := rfl
  change List.foldlM Instr.run (env1004 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1004).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e9, e779, computeSafe782, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1005, v782, throwUBIf, e9, e779, computeSafe782, mask_safe]

def env1006 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1005 E r t b x y)[%783 := .value (v783 r t b x y)]

theorem segment1005 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1005 1
      (env1005 E r t b x y) s = .value (env1006 E r t b x y, s) := by
  have e778 : (env1005 E r t b x y).read (%778) = .value (v778 r t b x y) := rfl
  have e781 : (env1005 E r t b x y).read (%781) = .value (v781 r t b x y) := rfl
  change List.foldlM Instr.run (env1005 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1005).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e778, e781, computeSafe783, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1006, v783, throwUBIf, e778, e781, computeSafe783, mask_safe]

def env1007 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1006 E r t b x y)[%784 := .value (v784 r t b x y)]

theorem segment1006 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1006 1
      (env1006 E r t b x y) s = .value (env1007 E r t b x y, s) := by
  have e59 : (env1006 E r t b x y).read (%59) = .value (36028797018963952#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, mlir_env] using he.e59
  have e776 : (env1006 E r t b x y).read (%776) = .value (v776 r t b x y) := rfl
  change List.foldlM Instr.run (env1006 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1006).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e59, e776, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1007, v784, throwUBIf, e59, e776, mask_safe]

def env1011 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1007 E r t b x y)[%785 := Ty.wrap (v785 r t b x y),
    %786 := .value (v786 r t b x y),
    %787 := Ty.wrap (v787 r t b x y),
    %788 := Ty.wrap (v788 r t b x y)]

theorem segment1007 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1007 4
      (env1007 E r t b x y) s = .value (env1011 E r t b x y, s) := by
  have e7 : (env1007 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, mlir_env] using he.e7
  have e56 : (env1007 E r t b x y).read (%56) = Ty.wrap (#v[2251799813685232#64, 2251799813685232#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, mlir_env] using he.e56
  have e60 : (env1007 E r t b x y).read (%60) = Ty.wrap (#v[36028797018963952#64, 36028797018963952#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, mlir_env] using he.e60
  have e752 : (env1007 E r t b x y).read (%752) = Ty.wrap (v752 r t b x y) := rfl
  have e775 : (env1007 E r t b x y).read (%775) = Ty.wrap (v775 r t b x y) := rfl
  have e784 : (env1007 E r t b x y).read (%784) = .value (v784 r t b x y) := rfl
  change List.foldlM Instr.run (env1007 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1007).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e56, e60, e752, e775, e784, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1011, v785, v786, v787, v788, throwUBIf, e7, e56, e60, e752, e775, e784, mask_safe]

def env1012 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1011 E r t b x y)[%789 := Ty.wrap (v789 r t b x y)]

theorem segment1011 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1011 1
      (env1011 E r t b x y) s = .value (env1012 E r t b x y, s) := by
  have e58 : (env1011 E r t b x y).read (%58) = Ty.wrap (#v[2251799813685247#64, 2251799813685247#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, mlir_env] using he.e58
  have e785 : (env1011 E r t b x y).read (%785) = Ty.wrap (v785 r t b x y) := rfl
  change List.foldlM Instr.run (env1011 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1011).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e58, e785, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1012, v789, throwUBIf, e58, e785, mask_safe]

def env1013 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1012 E r t b x y)[%790 := .value (v790 r t b x y)]

theorem segment1012 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1012 1
      (env1012 E r t b x y) s = .value (env1013 E r t b x y, s) := by
  have e9 : (env1012 E r t b x y).read (%9) = .value (19#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, mlir_env] using he.e9
  have e786 : (env1012 E r t b x y).read (%786) = .value (v786 r t b x y) := rfl
  change List.foldlM Instr.run (env1012 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1012).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e9, e786, computeSafe790, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1013, v790, throwUBIf, e9, e786, computeSafe790, mask_safe]

def env1014 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1013 E r t b x y)[%791 := .value (v791 r t b x y)]

theorem segment1013 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1013 1
      (env1013 E r t b x y) s = .value (env1014 E r t b x y, s) := by
  have e758 : (env1013 E r t b x y).read (%758) = .value (v758 r t b x y) := rfl
  have e782 : (env1013 E r t b x y).read (%782) = .value (v782 r t b x y) := rfl
  change List.foldlM Instr.run (env1013 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1013).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e758, e782, computeSafe791, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1014, v791, throwUBIf, e758, e782, computeSafe791, mask_safe]

def env1015 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1014 E r t b x y)[%792 := .value (v792 r t b x y)]

theorem segment1014 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1014 1
      (env1014 E r t b x y) s = .value (env1015 E r t b x y, s) := by
  have e757 : (env1014 E r t b x y).read (%757) = .value (v757 r t b x y) := rfl
  have e780 : (env1014 E r t b x y).read (%780) = .value (v780 r t b x y) := rfl
  change List.foldlM Instr.run (env1014 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1014).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e757, e780, computeSafe792, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1015, v792, throwUBIf, e757, e780, computeSafe792, mask_safe]

def env1016 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1015 E r t b x y)[%793 := .value (v793 r t b x y)]

theorem segment1015 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1015 1
      (env1015 E r t b x y) s = .value (env1016 E r t b x y, s) := by
  have e9 : (env1015 E r t b x y).read (%9) = .value (19#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, mlir_env] using he.e9
  have e791 : (env1015 E r t b x y).read (%791) = .value (v791 r t b x y) := rfl
  change List.foldlM Instr.run (env1015 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1015).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e9, e791, computeSafe793, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1016, v793, throwUBIf, e9, e791, computeSafe793, mask_safe]

def env1017 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1016 E r t b x y)[%794 := .value (v794 r t b x y)]

theorem segment1016 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1016 1
      (env1016 E r t b x y) s = .value (env1017 E r t b x y, s) := by
  have e7 : (env1016 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, mlir_env] using he.e7
  have e793 : (env1016 E r t b x y).read (%793) = .value (v793 r t b x y) := rfl
  change List.foldlM Instr.run (env1016 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1016).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e793, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1017, v794, throwUBIf, e7, e793, mask_safe]

def env1018 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1017 E r t b x y)[%795 := .value (v795 r t b x y)]

theorem segment1017 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1017 1
      (env1017 E r t b x y) s = .value (env1018 E r t b x y, s) := by
  have e761 : (env1017 E r t b x y).read (%761) = .value (v761 r t b x y) := rfl
  have e794 : (env1017 E r t b x y).read (%794) = .value (v794 r t b x y) := rfl
  change List.foldlM Instr.run (env1017 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1017).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e761, e794, computeSafe795, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1018, v795, throwUBIf, e761, e794, computeSafe795, mask_safe]

def env1019 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1018 E r t b x y)[%796 := .value (v796 r t b x y)]

theorem segment1018 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1018 1
      (env1018 E r t b x y) s = .value (env1019 E r t b x y, s) := by
  have e7 : (env1018 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, mlir_env] using he.e7
  have e795 : (env1018 E r t b x y).read (%795) = .value (v795 r t b x y) := rfl
  change List.foldlM Instr.run (env1018 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1018).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e795, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1019, v796, throwUBIf, e7, e795, mask_safe]

def env1020 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1019 E r t b x y)[%797 := .value (v797 r t b x y)]

theorem segment1019 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1019 1
      (env1019 E r t b x y) s = .value (env1020 E r t b x y, s) := by
  have e762 : (env1019 E r t b x y).read (%762) = .value (v762 r t b x y) := rfl
  have e796 : (env1019 E r t b x y).read (%796) = .value (v796 r t b x y) := rfl
  change List.foldlM Instr.run (env1019 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1019).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e762, e796, computeSafe797, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1020, v797, throwUBIf, e762, e796, computeSafe797, mask_safe]

def env1021 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1020 E r t b x y)[%798 := .value (v798 r t b x y)]

theorem segment1020 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1020 1
      (env1020 E r t b x y) s = .value (env1021 E r t b x y, s) := by
  have e7 : (env1020 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, mlir_env] using he.e7
  have e797 : (env1020 E r t b x y).read (%797) = .value (v797 r t b x y) := rfl
  change List.foldlM Instr.run (env1020 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1020).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e797, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1021, v798, throwUBIf, e7, e797, mask_safe]

def env1022 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1021 E r t b x y)[%799 := .value (v799 r t b x y)]

theorem segment1021 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1021 1
      (env1021 E r t b x y) s = .value (env1022 E r t b x y, s) := by
  have e792 : (env1021 E r t b x y).read (%792) = .value (v792 r t b x y) := rfl
  have e798 : (env1021 E r t b x y).read (%798) = .value (v798 r t b x y) := rfl
  change List.foldlM Instr.run (env1021 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1021).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e792, e798, computeSafe799, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1022, v799, throwUBIf, e792, e798, computeSafe799, mask_safe]

def env1023 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1022 E r t b x y)[%800 := .value (v800 r t b x y)]

theorem segment1022 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1022 1
      (env1022 E r t b x y) s = .value (env1023 E r t b x y, s) := by
  have e7 : (env1022 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, mlir_env] using he.e7
  have e799 : (env1022 E r t b x y).read (%799) = .value (v799 r t b x y) := rfl
  change List.foldlM Instr.run (env1022 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1022).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e799, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1023, v800, throwUBIf, e7, e799, mask_safe]

def env1024 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1023 E r t b x y)[%801 := .value (v801 r t b x y)]

theorem segment1023 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1023 1
      (env1023 E r t b x y) s = .value (env1024 E r t b x y, s) := by
  have e783 : (env1023 E r t b x y).read (%783) = .value (v783 r t b x y) := rfl
  have e800 : (env1023 E r t b x y).read (%800) = .value (v800 r t b x y) := rfl
  change List.foldlM Instr.run (env1023 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1023).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e783, e800, computeSafe801, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1024, v801, throwUBIf, e783, e800, computeSafe801, mask_safe]

def env1025 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1024 E r t b x y)[%802 := .value (v802 r t b x y)]

theorem segment1024 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1024 1
      (env1024 E r t b x y) s = .value (env1025 E r t b x y, s) := by
  have e7 : (env1024 E r t b x y).read (%7) = .value (51#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, mlir_env] using he.e7
  have e801 : (env1024 E r t b x y).read (%801) = .value (v801 r t b x y) := rfl
  change List.foldlM Instr.run (env1024 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1024).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e7, e801, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1025, v802, throwUBIf, e7, e801, mask_safe]

def env1026 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1025 E r t b x y)[%803 := .value (v803 r t b x y)]

theorem segment1025 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1025 1
      (env1025 E r t b x y) s = .value (env1026 E r t b x y, s) := by
  have e791 : (env1025 E r t b x y).read (%791) = .value (v791 r t b x y) := rfl
  have e802 : (env1025 E r t b x y).read (%802) = .value (v802 r t b x y) := rfl
  change List.foldlM Instr.run (env1025 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1025).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e791, e802, computeSafe803, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1026, v803, throwUBIf, e791, e802, computeSafe803, mask_safe]

def env1028 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1026 E r t b x y)[%804 := .value (v804 r t b x y),
    %805 := .value (v805 r t b x y)]

theorem segment1026 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) (hr : SmallRange s.mem r 40) (ht : SmallRange s.mem t 40) (hx : readLimbs s r = x) (hy : readLimbs s t = y) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1026 2
      (env1026 E r t b x y) s = .value (env1028 E r t b x y, s) := by
  have e61 : (env1026 E r t b x y).read (%61) = .value (1#8) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, mlir_env] using he.e61
  have e803 : (env1026 E r t b x y).read (%803) = .value (v803 r t b x y) := rfl
  change List.foldlM Instr.run (env1026 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1026).take 2) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e61, e803, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1028, v804, v805, throwUBIf, e61, e803, mask_safe]

def env1029 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1028 E r t b x y)[%806 := .value (v806 r t b x y)]

theorem segment1028 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hwf : s.WF) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1028 1
      (env1028 E r t b x y) s = .value (env1029 E r t b x y, {s with alloc := (s.alloca 1).alloc}) := by
  have e805 : (env1028 E r t b x y).read (%805) = .value (v805 r t b x y) := rfl
  have hb := BlackBox.program_call (v805 r t b x y) s hwf
  dsimp only [BlackBox.program.args] at hb
  change List.foldlM Instr.run (env1028 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1028).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e805, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1029, v806, throwUBIf, sqrtRatioPrimitives, hb, Env.writeMany_cons, Env.writeMany_nil, v806, e805, mask_safe]

def env1030 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1029 E r t b x y)[%807 := Ty.wrap (v807 r t b x y)]

theorem segment1029 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1029 1
      (env1029 E r t b x y) s = .value (env1030 E r t b x y, s) := by
  have e57 : (env1029 E r t b x y).read (%57) = Ty.wrap (#v[51#64, 51#64]) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, mlir_env] using he.e57
  have e788 : (env1029 E r t b x y).read (%788) = Ty.wrap (v788 r t b x y) := rfl
  change List.foldlM Instr.run (env1029 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1029).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e57, e788, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1030, v807, throwUBIf, e57, e788, mask_safe]

def env1031 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1030 E r t b x y)[%808 := .value (v808 r t b x y)]

theorem segment1030 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1030 1
      (env1030 E r t b x y) s = .value (env1031 E r t b x y, s) := by
  have e767 : (env1030 E r t b x y).read (%767) = .value (v767 r t b x y) := rfl
  have e790 : (env1030 E r t b x y).read (%790) = .value (v790 r t b x y) := rfl
  change List.foldlM Instr.run (env1030 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1030).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e767, e790, computeSafe808, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1031, v808, throwUBIf, e767, e790, computeSafe808, mask_safe]

def env1032 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1031 E r t b x y)[%809 := Ty.wrap (v809 r t b x y)]

theorem segment1031 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1031 1
      (env1031 E r t b x y) s = .value (env1032 E r t b x y, s) := by
  have e789 : (env1031 E r t b x y).read (%789) = Ty.wrap (v789 r t b x y) := rfl
  have e807 : (env1031 E r t b x y).read (%807) = Ty.wrap (v807 r t b x y) := rfl
  change List.foldlM Instr.run (env1031 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1031).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e789, e807, safe809, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1032, v809, throwUBIf, e789, e807, safe809, mask_safe]

def env1033 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1032 E r t b x y)[%810 := .value (v810 r t b x y)]

theorem segment1032 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1032 1
      (env1032 E r t b x y) s = .value (env1033 E r t b x y, s) := by
  have e806 : (env1032 E r t b x y).read (%806) = .value (v806 r t b x y) := rfl
  change List.foldlM Instr.run (env1032 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1032).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e806, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1033, v810, throwUBIf, e806, mask_safe]

def env1034 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1033 E r t b x y)[%811 := .value (v811 r t b x y)]

theorem segment1033 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1033 1
      (env1033 E r t b x y) s = .value (env1034 E r t b x y, s) := by
  have e50 : (env1033 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, mlir_env] using he.e50
  have e810 : (env1033 E r t b x y).read (%810) = .value (v810 r t b x y) := rfl
  change List.foldlM Instr.run (env1033 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1033).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e50, e810, computeSafe811, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1034, v811, throwUBIf, e50, e810, computeSafe811, mask_safe]

def env1037 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1034 E r t b x y)[%812 := .value (v812 r t b x y),
    %813 := .value (v813 r t b x y),
    %814 := .value (v814 r t b x y)]

theorem segment1034 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1034 3
      (env1034 E r t b x y) s = .value (env1037 E r t b x y, s) := by
  have e751 : (env1034 E r t b x y).read (%751) = .value (v751 r t b x y) := rfl
  have e808 : (env1034 E r t b x y).read (%808) = .value (v808 r t b x y) := rfl
  have e811 : (env1034 E r t b x y).read (%811) = .value (v811 r t b x y) := rfl
  change List.foldlM Instr.run (env1034 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1034).take 3) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e751, e808, e811, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1037, v812, v813, v814, throwUBIf, e751, e808, e811, mask_safe]

def env1038 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1037 E r t b x y)

theorem segment1037 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hr : SmallRange s.mem r 40) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1037 1
      (env1037 E r t b x y) s = .value (env1038 E r t b x y, {s with mem := s.mem.storeAt (r) (v814 r t b x y)}) := by
  have e79 : (env1037 E r t b x y).read (%79) = .value (r) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, mlir_env] using he.e79
  have e814 : (env1037 E r t b x y).read (%814) = .value (v814 r t b x y) := rfl
  have hf := hr.fits_add (k := 0) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hf
  change List.foldlM Instr.run (env1037 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1037).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e79, e814, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1038, throwUBIf, Operation.load, Operation.store, load_two_words, Pointer.add_add, Pointer.add_zero, hf, v736, v738, e79, e814, mask_safe]

def env1042 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1038 E r t b x y)[%815 := v815 r t b x y,
    %816 := Ty.wrap (v816 r t b x y),
    %817 := Ty.wrap (v817 r t b x y),
    %818 := Ty.wrap (v818 r t b x y)]

theorem segment1038 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1038 4
      (env1038 E r t b x y) s = .value (env1042 E r t b x y, s) := by
  have e50 : (env1038 E r t b x y).read (%50) = .value (0#64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, mlir_env] using he.e50
  have e53 : (env1038 E r t b x y).read (%53) = Ty.poisoned (.vec 2 64) := by
    simpa (disch := decide) only [env957, env958, env962, env966, env970, env974, env978, env982, env983, env984, env985, env986, env990, env991, env992, env995, env999, env1003, env1004, env1005, env1006, env1007, env1011, env1012, env1013, env1014, env1015, env1016, env1017, env1018, env1019, env1020, env1021, env1022, env1023, env1024, env1025, env1026, env1028, env1029, env1030, env1031, env1032, env1033, env1034, env1037, env1038, mlir_env] using he.e53
  have e752 : (env1038 E r t b x y).read (%752) = Ty.wrap (v752 r t b x y) := rfl
  have e770 : (env1038 E r t b x y).read (%770) = Ty.wrap (v770 r t b x y) := rfl
  have e811 : (env1038 E r t b x y).read (%811) = .value (v811 r t b x y) := rfl
  change List.foldlM Instr.run (env1038 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1038).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e50, e53, e752, e770, e811, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1042, v815, v816, v817, v818, throwUBIf, e50, e53, e752, e770, e811, mask_safe]

def env1043 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1042 E r t b x y)

theorem segment1042 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hr : SmallRange s.mem r 40) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1042 1
      (env1042 E r t b x y) s = .value (env1043 E r t b x y, {s with mem := s.mem.storeAt ((v736 r t b x y)) (BitVec.packLanes (v818 r t b x y))}) := by
  have e736 : (env1042 E r t b x y).read (%736) = .value (v736 r t b x y) := rfl
  have e818 : (env1042 E r t b x y).read (%818) = Ty.wrap (v818 r t b x y) := rfl
  have hf := hr.fits_add (k := 8) (count := 16) (by decide)
  change List.foldlM Instr.run (env1042 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1042).take 1) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e736, e818, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1043, throwUBIf, Operation.load, Operation.store, load_two_words, Pointer.add_add, Pointer.add_zero, hf, v736, v738, e736, e818, mask_safe]

def env1047 (E : Env program.Γ) (r t : Pointer) (b : BitVec 8) (x y : Words) : Env program.Γ :=
  (env1043 E r t b x y)[%819 := Ty.wrap (v819 r t b x y),
    %820 := Ty.wrap (v820 r t b x y),
    %821 := Ty.wrap (v821 r t b x y)]

theorem segment1043 (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (r t : Pointer) (b : BitVec 8) (x y : Words)
    (he : Registers E r t b) (hr : SmallRange s.mem r 40) :
    Cutpoint.segment (program sqrtRatioPrimitives g) 0 1043 4
      (env1043 E r t b x y) s = .value (env1047 E r t b x y, {s with mem := s.mem.storeAt ((v738 r t b x y)) (BitVec.packLanes (v821 r t b x y))}) := by
  have e738 : (env1043 E r t b x y).read (%738) = .value (v738 r t b x y) := rfl
  have e775 : (env1043 E r t b x y).read (%775) = Ty.wrap (v775 r t b x y) := rfl
  have e809 : (env1043 E r t b x y).read (%809) = Ty.wrap (v809 r t b x y) := rfl
  have e816 : (env1043 E r t b x y).read (%816) = Ty.wrap (v816 r t b x y) := rfl
  have hf := hr.fits_add (k := 24) (count := 16) (by decide)
  change List.foldlM Instr.run (env1043 E r t b x y)
    (((program.entry sqrtRatioPrimitives g).body.drop 1043).take 4) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp only [List.foldlM_cons, List.foldlM_nil, Instr.run, mlir_env,
    e738, e775, e809, e816, mask_safe,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind]
  simp (disch := first | assumption | decide) [BinOp.compute, UnOp.compute, TernOp.compute, mlir_env, mlir_operation, mlir_effect, vector_two, env1047, v819, v820, v821, throwUBIf, Operation.load, Operation.store, load_two_words, Pointer.add_add, Pointer.add_zero, hf, v736, v738, e738, e775, e809, e816, mask_safe]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline956
