import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionStages
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionModel
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions
import Mathlib.Data.BitVec

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR

/- Each declaration checks one output column, so convolution terms never pass
through the carry or packing schedule and the kernel checks stay separate.
Use `ac_rfl` after simplification to keep the arithmetic proof terms compact. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_0 (a : Blocks) :
    columnTrace a 0 = signedColumns4 a 0 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_1 (a : Blocks) :
    columnTrace a 1 = signedColumns4 a 1 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_2 (a : Blocks) :
    columnTrace a 2 = signedColumns4 a 2 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_3 (a : Blocks) :
    columnTrace a 3 = signedColumns4 a 3 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_4 (a : Blocks) :
    columnTrace a 4 = signedColumns4 a 4 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_5 (a : Blocks) :
    columnTrace a 5 = signedColumns4 a 5 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_6 (a : Blocks) :
    columnTrace a 6 = signedColumns4 a 6 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_7 (a : Blocks) :
    columnTrace a 7 = signedColumns4 a 7 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_8 (a : Blocks) :
    columnTrace a 8 = signedColumns4 a 8 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem columnTrace_eq_columns_9 (a : Blocks) :
    columnTrace a 9 = signedColumns4 a 9 := by
  apply Vector.ext
  intro j hj
  interval_cases j
  all_goals simp [columnTrace, signedColumns4, Avx2FieldMul.Execution.unpackBlocks,
    machineSignedColumns, machineColumns, negateConstant, mul32, twice, times19,
    join64, zero_append_eq_wide, Avx2FieldMul.Execution.mask32_eq_wide]
  all_goals ac_rfl

/-- The ten individually checked convolution columns. -/
theorem columnTrace_eq_columns (a : Blocks) :
    columnTrace a = signedColumns4 a := by
  funext i
  fin_cases i
  · exact columnTrace_eq_columns_0 a
  · exact columnTrace_eq_columns_1 a
  · exact columnTrace_eq_columns_2 a
  · exact columnTrace_eq_columns_3 a
  · exact columnTrace_eq_columns_4 a
  · exact columnTrace_eq_columns_5 a
  · exact columnTrace_eq_columns_6 a
  · exact columnTrace_eq_columns_7 a
  · exact columnTrace_eq_columns_8 a
  · exact columnTrace_eq_columns_9 a

end Agave.Ed25519.Avx2SquareNegateD.Execution
