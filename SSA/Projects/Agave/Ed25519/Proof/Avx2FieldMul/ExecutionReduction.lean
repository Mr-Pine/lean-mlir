import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionStages
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Packing
import Mathlib.Data.BitVec

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR

/- Abstract columns bound the size of each carry proof. The five independently
checked output vectors contain the exact physical A/B/even/odd/C/D lane order. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reductionTrace_eq_packedOutput_0 (z : WordColumns) :
    reductionTrace z 0 = Reduce64.Execution.packedOutput z 0 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [reductionTrace, Reduce64.Execution.packedOutput,
    Reduce64.Execution.reduceLanes, Reduce64.Execution.packPair, Reduce64.Execution.low32,
    Reduce64.Word.reduce, Reduce64.Word.t1, Reduce64.Word.t2, Reduce64.Word.t3,
    Reduce64.Word.t4, Reduce64.Word.t5, Reduce64.Word.t6, Reduce64.Word.t7,
    Reduce64.Word.t8, Reduce64.Word.t9, Reduce64.Word.u0, Reduce64.Word.u1,
    Reduce64.Word.u5, Reduce64.Word.carry, split32, BitVec.extractLsb'_and,
    ← BitVec.shiftRight_add]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reductionTrace_eq_packedOutput_1 (z : WordColumns) :
    reductionTrace z 1 = Reduce64.Execution.packedOutput z 1 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [reductionTrace, Reduce64.Execution.packedOutput,
    Reduce64.Execution.reduceLanes, Reduce64.Execution.packPair, Reduce64.Execution.low32,
    Reduce64.Word.reduce, Reduce64.Word.t1, Reduce64.Word.t2, Reduce64.Word.t3,
    Reduce64.Word.t4, Reduce64.Word.t5, Reduce64.Word.t6, Reduce64.Word.t7,
    Reduce64.Word.t8, Reduce64.Word.t9, Reduce64.Word.u0, Reduce64.Word.u1,
    Reduce64.Word.u5, Reduce64.Word.carry, split32, BitVec.extractLsb'_and,
    ← BitVec.shiftRight_add]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reductionTrace_eq_packedOutput_2 (z : WordColumns) :
    reductionTrace z 2 = Reduce64.Execution.packedOutput z 2 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [reductionTrace, Reduce64.Execution.packedOutput,
    Reduce64.Execution.reduceLanes, Reduce64.Execution.packPair, Reduce64.Execution.low32,
    Reduce64.Word.reduce, Reduce64.Word.t1, Reduce64.Word.t2, Reduce64.Word.t3,
    Reduce64.Word.t4, Reduce64.Word.t5, Reduce64.Word.t6, Reduce64.Word.t7,
    Reduce64.Word.t8, Reduce64.Word.t9, Reduce64.Word.u0, Reduce64.Word.u1,
    Reduce64.Word.u5, Reduce64.Word.carry, split32, BitVec.extractLsb'_and,
    ← BitVec.shiftRight_add]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reductionTrace_eq_packedOutput_3 (z : WordColumns) :
    reductionTrace z 3 = Reduce64.Execution.packedOutput z 3 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [reductionTrace, Reduce64.Execution.packedOutput,
    Reduce64.Execution.reduceLanes, Reduce64.Execution.packPair, Reduce64.Execution.low32,
    Reduce64.Word.reduce, Reduce64.Word.t1, Reduce64.Word.t2, Reduce64.Word.t3,
    Reduce64.Word.t4, Reduce64.Word.t5, Reduce64.Word.t6, Reduce64.Word.t7,
    Reduce64.Word.t8, Reduce64.Word.t9, Reduce64.Word.u0, Reduce64.Word.u1,
    Reduce64.Word.u5, Reduce64.Word.carry, split32, BitVec.extractLsb'_and,
    ← BitVec.shiftRight_add]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reductionTrace_eq_packedOutput_4 (z : WordColumns) :
    reductionTrace z 4 = Reduce64.Execution.packedOutput z 4 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [reductionTrace, Reduce64.Execution.packedOutput,
    Reduce64.Execution.reduceLanes, Reduce64.Execution.packPair, Reduce64.Execution.low32,
    Reduce64.Word.reduce, Reduce64.Word.t1, Reduce64.Word.t2, Reduce64.Word.t3,
    Reduce64.Word.t4, Reduce64.Word.t5, Reduce64.Word.t6, Reduce64.Word.t7,
    Reduce64.Word.t8, Reduce64.Word.t9, Reduce64.Word.u0, Reduce64.Word.u1,
    Reduce64.Word.u5, Reduce64.Word.carry, split32, BitVec.extractLsb'_and,
    ← BitVec.shiftRight_add]
  all_goals ac_rfl

/-- Assemble the five independently checked output registers. -/
theorem reductionTrace_eq_packedOutput (z : WordColumns) :
    reductionTrace z = Reduce64.Execution.packedOutput z := by
  funext i
  fin_cases i
  · exact reductionTrace_eq_packedOutput_0 z
  · exact reductionTrace_eq_packedOutput_1 z
  · exact reductionTrace_eq_packedOutput_2 z
  · exact reductionTrace_eq_packedOutput_3 z
  · exact reductionTrace_eq_packedOutput_4 z

end Agave.Ed25519.Avx2FieldMul.Execution
