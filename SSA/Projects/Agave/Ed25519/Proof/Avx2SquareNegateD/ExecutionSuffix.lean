import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionStores
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionStages
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions

import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Agave.Ed25519.Avx2SquareNegateD.Execution.Suffix

open LeanMLIR.RIR
open Reduce64.Execution
open Avx2FieldMul.Execution

attribute [local implicit_reducible] Ty.width
attribute [-mlir_operation] Operation.bitcast Operation.add Operation.mul

@[simp] def mask26 : ⟦Ty.vec 8 32⟧ :=
  #v[.value 67108863#32, .poison, .value 67108863#32, .poison,
    .value 67108863#32, .poison, .value 67108863#32, .poison]

@[simp] def mask25 : ⟦Ty.vec 8 32⟧ :=
  #v[.value 33554431#32, .poison, .value 33554431#32, .poison,
    .value 33554431#32, .poison, .value 33554431#32, .poison]

/-- Resume the exact imported entry block at instruction `%300`, including its
unchanged terminator and function continuation. -/
noncomputable def resume300 (E : Env program.Γ) :
    EffectM (Vals program.tRets) := do
  let E' ← program.entry.runBodyFrom E 300
  let (E'', exit) ← program.entry.exit.run program.blockParams E'
  Func.continue (func := program) E'' exit

set_option maxHeartbeats 8000000 in
/-- Exact reduction, packing, and stores from instruction 300. The ten
convolution columns and the live constants form a compact cutpoint interface. -/
theorem run (E : Env program.Γ) (S : GlobalState) (r : Pointer)
    (z : WordColumns)
    (hr : SmallRange S.mem r 160)
    (harg : E.read (%arg0) = .value r)
    (h41 : E.read (%41) = Ty.wrap (Vector.replicate 4 19#64))
    (h75 : E.read (%75) = Ty.wrap (Vector.replicate 4 26#64))
    (h76 : E.read (%76) = Ty.wrap (Vector.replicate 4 67108863#64))
    (h77 : E.read (%77) = Ty.wrap (Vector.replicate 4 25#64))
    (h78 : E.read (%78) = Ty.wrap (Vector.replicate 4 33554431#64))
    (h79 : E.read (%79) = Ty.wrap (Vector.replicate 4 51#64))
    (h97 : E.read (%97) = mask26)
    (h115 : E.read (%115) = mask25)
    (h281 : E.read (%281) = Ty.wrap (z 0))
    (h283 : E.read (%283) = Ty.wrap (z 1))
    (h285 : E.read (%285) = Ty.wrap (z 2))
    (h287 : E.read (%287) = Ty.wrap (z 3))
    (h289 : E.read (%289) = Ty.wrap (z 4))
    (h291 : E.read (%291) = Ty.wrap (z 5))
    (h293 : E.read (%293) = Ty.wrap (z 6))
    (h295 : E.read (%295) = Ty.wrap (z 7))
    (h297 : E.read (%297) = Ty.wrap (z 8))
    (h299 : E.read (%299) = Ty.wrap (z 9)) :
    resume300 E S =
      .value (.nil, {S with mem := storeBlocks S.mem r (reductionTrace z)}) := by
  unfold resume300
  simp only [EffectM.bind_eq]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp]
  step_pure [expandOfFn, avx2_execution_simp] named
  as_aux_lemma =>
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp] named
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp] named
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp] named
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp] named
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp] named
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp]
    step_pure [expandOfFn, avx2_execution_simp] named
    have hblocks : ![v336, v341, v345, v350, v355] = reductionTrace z := by
      clear hr harg h41 h75 h76 h77 h78 h79 h97 h115
        h281 h283 h285 h287 h289 h291 h293 h295 h297 h299 hE E E₀ S r
      subst_vars
      funext i
      fin_cases i
      all_goals simp [reductionTrace, expandOfFn,
        avx2_execution_simp, zipWith_eq_ofFn]
    have htail := stores_run E S r ![v336, v341, v345, v350, v355] hr
      (by
        env_reads
        simpa only [Env.read] using harg)
      (by env_reads) (by env_reads) (by env_reads) (by env_reads) (by env_reads)
    rw [htail]
    clear htail
    simp only [PoisonOr.value_bind, reduceBlockExit, Exit.run,
      Regs.read_nil, EffectM.pure_eq, reduceFuncContinue]
    rw [hblocks]

end Agave.Ed25519.Avx2SquareNegateD.Execution.Suffix
