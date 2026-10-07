import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Inline
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Output

/-! Compose the actual normalization cut point, black_box/shift/or instructions,
and original output stores. No whole-compression contract is used. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxHeartbeats 8000000
set_option maxRecDepth 12000

def insertedEnv (E : Env program.Γ) (sign last : BitVec 8) : Env program.Γ :=
  E[%222 := .value sign, %223 := .value (sign <<< 7),
    %224 := .value ((sign <<< 7) ||| last)]

/-- Three original instructions. The supplied external premise is exactly
one invocation of the subtle byte identity helper. -/
theorem sign_slice_run (p : Primitives) (E : Env program.Γ)
    (sign last : BitVec 8) (s t : GlobalState)
    (hsign : E.read (%221) = .value sign)
    (hlast : E.read (%183) = .value last)
    (hseven : E.read (%44) = .value 7#8)
    (hdis : (sign <<< 7) &&& last = 0)
    (hblack : p.blackBoxByte (.cons (.value sign) .nil) s =
      .value (.cons (.value sign) .nil, t)) :
    runSlice p 240 3 E s = .value (insertedEnv E sign last, t) := by
  simp [runSlice, program.entry, insertedEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.shl, Operation.or,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    hsign, hlast, hseven, hdis, hblack]

/-- The tail Func used by `store_run` has exactly the original remaining
instruction semantics and original empty return. -/
theorem storeProgram_eq_finishFrom (p : Primitives) (E : Env program.Γ) (s : GlobalState) :
    (storeProgram p).runFrom E 0 s = finishFrom p 243 E s := by
  rw [Func.runFrom_eq]
  simp [storeProgram, BasicBlock.run, finishFrom, BasicBlock.runBodyFrom,
    program.entry, Exit.run, Regs.read_nil, EffectM.bind_eq, EffectM.pure_eq,
    Func.continue]

/-- Only writes already present in the post-canonicalizer environment are
introduced by storeEnv; the environment therefore remains unchanged. -/
theorem normalized_storeEnv (E : Env program.Γ) (initial : GlobalState)
    (input : Pointer) (x y : Field.Serial) :
    let F := insertedEnv (normalizedEnv (affineEnv E initial input) (scratch initial 5) x y)
      (inlineParity x) (inlineYBytes y 31)
    storeEnv F (inlineCompressedBytes x y) = F := by
  dsimp only
  unfold storeEnv
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]
  rw [Env.write_of_read _ _ (by
    simp [insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv,
      inlineCompressedBytes, inlineYBytes, inlineParity, mlir_env])]

/-- Execute all original instructions from black_box through byte 31. -/
theorem canonical_tail_run (p : Primitives) (E : Env program.Γ)
    (initial s t : GlobalState) (input out : Pointer) (x y : Field.Serial)
    (hout : E.read (%arg0) = .value out)
    (hr : SmallRange t.mem out 32)
    (hblack : p.blackBoxByte (.cons (.value (inlineParity x)) .nil) s =
      .value (.cons (.value (inlineParity x)) .nil, t)) :
    finishFrom p 240 (normalizedEnv (affineEnv E initial input) (scratch initial 5) x y) s =
      .value (.nil, {t with mem := storeBytes t.mem out (encodedBytes x y)}) := by
  let F := normalizedEnv (affineEnv E initial input) (scratch initial 5) x y
  have htop : (inlineYBytes y 31)[7] = false := by
    rw [inlineYBytes_canonical]
    have h := serialized_top_clear y
    simpa [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_extractLsb'] using h
  have hdis : (inlineParity x <<< 7) &&& inlineYBytes y 31 = 0 := by
    rw [inlineParity_canonical]
    exact insertSign_disjoint _ _ htop
  have hslice := sign_slice_run p F (inlineParity x) (inlineYBytes y 31) s t
    (by simp [F, normalizedEnv, inlineParity, mlir_env])
    (by simp [F, normalizedEnv, inlineYBytes, mlir_env])
    (by simp [F, normalizedEnv, affineEnv, allocatedEnv, constantEnv, mlir_env]) hdis hblack
  rw [finishFrom_of_slice p 240 3 F _ s t hslice]
  change finishFrom p 243 (insertedEnv F (inlineParity x) (inlineYBytes y 31)) t = _
  rw [← storeProgram_eq_finishFrom]
  have hfix := normalized_storeEnv E initial input x y
  change storeEnv (insertedEnv F (inlineParity x) (inlineYBytes y 31))
    (inlineCompressedBytes x y) = _ at hfix
  rw [← hfix]
  rw [store_run p _ out (inlineCompressedBytes x y) t hr
    (by simpa [F, insertedEnv, normalizedEnv, affineEnv, allocatedEnv, constantEnv, mlir_env] using hout)]
  rw [inlineCompressedBytes_eq]

/-- Actual affine loads, both inline canonicalizers, sign insertion and stores. -/
theorem affine_tail_run (p : Primitives) (E : Env program.Γ)
    (initial s t : GlobalState) (input out : Pointer)
    (htemp : SmallRange s.mem (scratch initial 5) 80)
    (hout : E.read (%arg0) = .value out) (hr : SmallRange t.mem out 32)
    (hsafe : NormalizationSafety (affineXWords s (scratch initial 5))
      (affineYWords s (scratch initial 5)))
    (hblack : p.blackBoxByte
      (.cons (.value (inlineParity (affineXWords s (scratch initial 5)))) .nil) s =
      .value (.cons (.value (inlineParity (affineXWords s (scratch initial 5)))) .nil, t)) :
    finishFrom p 81 (affineEnv E initial input) s =
      .value (.nil, {t with
        mem := storeBytes t.mem out
          (encodedBytes (affineXWords s (scratch initial 5)) (affineYWords s (scratch initial 5)))}) := by
  rw [finishFrom_of_slice p 81 159 _ _ s s (normalize_run p E initial s input htemp hsafe)]
  exact canonical_tail_run p E initial s t input out _ _ hout hr hblack

end Agave.Ed25519.Encoding.Compress.Execution
