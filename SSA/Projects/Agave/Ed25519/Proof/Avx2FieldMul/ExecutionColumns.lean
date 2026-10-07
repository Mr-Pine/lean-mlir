import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionStages
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionModel
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions
import Mathlib.Data.BitVec

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR
open Avx2SquareNegateD

/- Each declaration checks one output column, so convolution terms never pass
through the carry or packing schedule and the kernel checks stay separate. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_0 (a b : Blocks) :
    columnTrace a b 0 = rawColumns4 a b 0 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_1 (a b : Blocks) :
    columnTrace a b 1 = rawColumns4 a b 1 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_2 (a b : Blocks) :
    columnTrace a b 2 = rawColumns4 a b 2 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_3 (a b : Blocks) :
    columnTrace a b 3 = rawColumns4 a b 3 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_4 (a b : Blocks) :
    columnTrace a b 4 = rawColumns4 a b 4 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_5 (a b : Blocks) :
    columnTrace a b 5 = rawColumns4 a b 5 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_6 (a b : Blocks) :
    columnTrace a b 6 = rawColumns4 a b 6 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_7 (a b : Blocks) :
    columnTrace a b 7 = rawColumns4 a b 7 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_8 (a b : Blocks) :
    columnTrace a b 8 = rawColumns4 a b 8 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_9 (a b : Blocks) :
    columnTrace a b 9 = rawColumns4 a b 9 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, rawColumns4, unpackBlocks, rawColumn, rawTerm,
    sum10, rhsIndex, split32, join64, zero_append_eq_wide, mask32_eq_wide]
  all_goals ac_rfl

/-- The ten individually checked convolution columns. -/
theorem columnTrace_eq_columns (a b : Blocks) :
    columnTrace a b = rawColumns4 a b := by
  funext i
  fin_cases i
  · exact columnTrace_eq_columns_0 a b
  · exact columnTrace_eq_columns_1 a b
  · exact columnTrace_eq_columns_2 a b
  · exact columnTrace_eq_columns_3 a b
  · exact columnTrace_eq_columns_4 a b
  · exact columnTrace_eq_columns_5 a b
  · exact columnTrace_eq_columns_6 a b
  · exact columnTrace_eq_columns_7 a b
  · exact columnTrace_eq_columns_8 a b
  · exact columnTrace_eq_columns_9 a b

end Agave.Ed25519.Avx2FieldMul.Execution
