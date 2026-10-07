import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308ArithmeticRun

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def a358 (x : Words) : BitVec 8 := (a345 x).setWidth 8
def a359 (x : Words) : BitVec 64 := (a345 x) >>> (8)
def a360 (x : Words) : BitVec 8 := (a359 x).setWidth 8
def a361 (x : Words) : BitVec 64 := (a345 x) >>> (16)
def a362 (x : Words) : BitVec 8 := (a361 x).setWidth 8
def a363 (x : Words) : BitVec 64 := (a345 x) >>> (24)
def a364 (x : Words) : BitVec 8 := (a363 x).setWidth 8
def a365 (x : Words) : BitVec 64 := (a345 x) >>> (32)
def a366 (x : Words) : BitVec 8 := (a365 x).setWidth 8
def a367 (x : Words) : BitVec 64 := (a345 x) >>> (40)
def a368 (x : Words) : BitVec 8 := (a367 x).setWidth 8
def a369 (x : Words) : BitVec 64 := (a345 x) >>> (48)
def a370 (x : Words) : BitVec 64 := (a369 x) &&& (7#64)
def a371 (x : Words) : BitVec 64 := (a350 x) <<< (3)
def a372 (x : Words) : BitVec 64 := (a371 x) ||| (a370 x)
def a373 (x : Words) : BitVec 8 := (a372 x).setWidth 8
def a374 (x : Words) : BitVec 64 := (a347 x) >>> (5)
def a375 (x : Words) : BitVec 8 := (a374 x).setWidth 8
def a376 (x : Words) : BitVec 64 := (a347 x) >>> (13)
def a377 (x : Words) : BitVec 8 := (a376 x).setWidth 8
def a378 (x : Words) : BitVec 64 := (a347 x) >>> (21)
def a379 (x : Words) : BitVec 8 := (a378 x).setWidth 8
def a380 (x : Words) : BitVec 64 := (a347 x) >>> (29)
def a381 (x : Words) : BitVec 8 := (a380 x).setWidth 8
def a382 (x : Words) : BitVec 64 := (a347 x) >>> (37)
def a383 (x : Words) : BitVec 8 := (a382 x).setWidth 8
def a384 (x : Words) : BitVec 64 := (a350 x) >>> (45)
def a385 (x : Words) : BitVec 64 := (a353 x) <<< (6)
def a386 (x : Words) : BitVec 64 := (a385 x) ||| (a384 x)
def a387 (x : Words) : BitVec 8 := (a386 x).setWidth 8
def a388 (x : Words) : BitVec 64 := (a349 x) >>> (2)
def a389 (x : Words) : BitVec 8 := (a388 x).setWidth 8
def a390 (x : Words) : BitVec 64 := (a349 x) >>> (10)
def a391 (x : Words) : BitVec 8 := (a390 x).setWidth 8
def a392 (x : Words) : BitVec 64 := (a349 x) >>> (18)
def a393 (x : Words) : BitVec 8 := (a392 x).setWidth 8
def a394 (x : Words) : BitVec 64 := (a349 x) >>> (26)
def a395 (x : Words) : BitVec 8 := (a394 x).setWidth 8
def a396 (x : Words) : BitVec 64 := (a349 x) >>> (34)
def a397 (x : Words) : BitVec 8 := (a396 x).setWidth 8
def a398 (x : Words) : BitVec 64 := (a349 x) >>> (42)
def a399 (x : Words) : BitVec 8 := (a398 x).setWidth 8
def a400 (x : Words) : BitVec 64 := (a353 x) >>> (50)
def a401 (x : Words) : BitVec 64 := (a356 x) <<< (1)
def a402 (x : Words) : BitVec 64 := (a401 x) ||| (a400 x)
def a403 (x : Words) : BitVec 8 := (a402 x).setWidth 8
def a404 (x : Words) : BitVec 64 := (a352 x) >>> (7)
def a405 (x : Words) : BitVec 8 := (a404 x).setWidth 8
def a406 (x : Words) : BitVec 64 := (a352 x) >>> (15)
def a407 (x : Words) : BitVec 8 := (a406 x).setWidth 8
def a408 (x : Words) : BitVec 64 := (a352 x) >>> (23)
def a409 (x : Words) : BitVec 8 := (a408 x).setWidth 8
def a410 (x : Words) : BitVec 64 := (a352 x) >>> (31)
def a411 (x : Words) : BitVec 8 := (a410 x).setWidth 8
def a412 (x : Words) : BitVec 64 := (a352 x) >>> (39)
def a413 (x : Words) : BitVec 8 := (a412 x).setWidth 8
def a414 (x : Words) : BitVec 64 := (a356 x) >>> (47)
def a415 (x : Words) : BitVec 64 := (a357 x) <<< (4)
def a416 (x : Words) : BitVec 64 := (a415 x) ||| (a414 x)
def a417 (x : Words) : BitVec 8 := (a416 x).setWidth 8
def a418 (x : Words) : BitVec 64 := (a355 x) >>> (4)
def a419 (x : Words) : BitVec 8 := (a418 x).setWidth 8
def a420 (x : Words) : BitVec 64 := (a355 x) >>> (12)
def a421 (x : Words) : BitVec 8 := (a420 x).setWidth 8
def a422 (x : Words) : BitVec 64 := (a355 x) >>> (20)
def a423 (x : Words) : BitVec 8 := (a422 x).setWidth 8
def a424 (x : Words) : BitVec 64 := (a355 x) >>> (28)
def a425 (x : Words) : BitVec 8 := (a424 x).setWidth 8
def a426 (x : Words) : BitVec 64 := (a355 x) >>> (36)
def a427 (x : Words) : BitVec 8 := (a426 x).setWidth 8
def a428 (x : Words) : BitVec 64 := (a357 x) >>> (44)
def a429 (x : Words) : BitVec 8 := (a428 x).setWidth 8

theorem calc358 (x : Words) :
    Operation.trunc {} (.value (a345 x)) = .value (a358 x) := by
  simp (disch := decide) [a358, mlir_operation]

theorem calc359 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (8#64)) = .value (a359 x) := by
  simp (disch := decide) [a359, mlir_operation]

theorem calc360 (x : Words) :
    Operation.trunc {} (.value (a359 x)) = .value (a360 x) := by
  simp (disch := decide) [a360, mlir_operation]

theorem calc361 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (16#64)) = .value (a361 x) := by
  simp (disch := decide) [a361, mlir_operation]

theorem calc362 (x : Words) :
    Operation.trunc {} (.value (a361 x)) = .value (a362 x) := by
  simp (disch := decide) [a362, mlir_operation]

theorem calc363 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (24#64)) = .value (a363 x) := by
  simp (disch := decide) [a363, mlir_operation]

theorem calc364 (x : Words) :
    Operation.trunc {} (.value (a363 x)) = .value (a364 x) := by
  simp (disch := decide) [a364, mlir_operation]

theorem calc365 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (32#64)) = .value (a365 x) := by
  simp (disch := decide) [a365, mlir_operation]

theorem calc366 (x : Words) :
    Operation.trunc {} (.value (a365 x)) = .value (a366 x) := by
  simp (disch := decide) [a366, mlir_operation]

theorem calc367 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (40#64)) = .value (a367 x) := by
  simp (disch := decide) [a367, mlir_operation]

theorem calc368 (x : Words) :
    Operation.trunc {} (.value (a367 x)) = .value (a368 x) := by
  simp (disch := decide) [a368, mlir_operation]

theorem calc369 (x : Words) :
    Operation.lshr false (.value (a345 x)) (.value (48#64)) = .value (a369 x) := by
  simp (disch := decide) [a369, mlir_operation]

theorem calc370 (x : Words) :
    Operation.and (.value (a369 x)) (.value (7#64)) = .value (a370 x) := by
  simp (disch := decide) [a370, mlir_operation]

theorem calc371 (x : Words) :
    Operation.shl {nsw := true, nuw := true} (.value (a350 x)) (.value (3#64)) = .value (a371 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc372 (x : Words) :
    Operation.or true (.value (a371 x)) (.value (a370 x)) = .value (a372 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc373 (x : Words) :
    Operation.trunc {} (.value (a372 x)) = .value (a373 x) := by
  simp (disch := decide) [a373, mlir_operation]

theorem calc374 (x : Words) :
    Operation.lshr false (.value (a347 x)) (.value (5#64)) = .value (a374 x) := by
  simp (disch := decide) [a374, mlir_operation]

theorem calc375 (x : Words) :
    Operation.trunc {} (.value (a374 x)) = .value (a375 x) := by
  simp (disch := decide) [a375, mlir_operation]

theorem calc376 (x : Words) :
    Operation.lshr false (.value (a347 x)) (.value (13#64)) = .value (a376 x) := by
  simp (disch := decide) [a376, mlir_operation]

theorem calc377 (x : Words) :
    Operation.trunc {} (.value (a376 x)) = .value (a377 x) := by
  simp (disch := decide) [a377, mlir_operation]

theorem calc378 (x : Words) :
    Operation.lshr false (.value (a347 x)) (.value (21#64)) = .value (a378 x) := by
  simp (disch := decide) [a378, mlir_operation]

theorem calc379 (x : Words) :
    Operation.trunc {} (.value (a378 x)) = .value (a379 x) := by
  simp (disch := decide) [a379, mlir_operation]

theorem calc380 (x : Words) :
    Operation.lshr false (.value (a347 x)) (.value (29#64)) = .value (a380 x) := by
  simp (disch := decide) [a380, mlir_operation]

theorem calc381 (x : Words) :
    Operation.trunc {} (.value (a380 x)) = .value (a381 x) := by
  simp (disch := decide) [a381, mlir_operation]

theorem calc382 (x : Words) :
    Operation.lshr false (.value (a347 x)) (.value (37#64)) = .value (a382 x) := by
  simp (disch := decide) [a382, mlir_operation]

theorem calc383 (x : Words) :
    Operation.trunc {} (.value (a382 x)) = .value (a383 x) := by
  simp (disch := decide) [a383, mlir_operation]

theorem calc384 (x : Words) :
    Operation.lshr false (.value (a350 x)) (.value (45#64)) = .value (a384 x) := by
  simp (disch := decide) [a384, mlir_operation]

theorem calc385 (x : Words) :
    Operation.shl {nsw := true, nuw := true} (.value (a353 x)) (.value (6#64)) = .value (a385 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc386 (x : Words) :
    Operation.or true (.value (a385 x)) (.value (a384 x)) = .value (a386 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc387 (x : Words) :
    Operation.trunc {} (.value (a386 x)) = .value (a387 x) := by
  simp (disch := decide) [a387, mlir_operation]

theorem calc388 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (2#64)) = .value (a388 x) := by
  simp (disch := decide) [a388, mlir_operation]

theorem calc389 (x : Words) :
    Operation.trunc {} (.value (a388 x)) = .value (a389 x) := by
  simp (disch := decide) [a389, mlir_operation]

theorem calc390 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (10#64)) = .value (a390 x) := by
  simp (disch := decide) [a390, mlir_operation]

theorem calc391 (x : Words) :
    Operation.trunc {} (.value (a390 x)) = .value (a391 x) := by
  simp (disch := decide) [a391, mlir_operation]

theorem calc392 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (18#64)) = .value (a392 x) := by
  simp (disch := decide) [a392, mlir_operation]

theorem calc393 (x : Words) :
    Operation.trunc {} (.value (a392 x)) = .value (a393 x) := by
  simp (disch := decide) [a393, mlir_operation]

theorem calc394 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (26#64)) = .value (a394 x) := by
  simp (disch := decide) [a394, mlir_operation]

theorem calc395 (x : Words) :
    Operation.trunc {} (.value (a394 x)) = .value (a395 x) := by
  simp (disch := decide) [a395, mlir_operation]

theorem calc396 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (34#64)) = .value (a396 x) := by
  simp (disch := decide) [a396, mlir_operation]

theorem calc397 (x : Words) :
    Operation.trunc {} (.value (a396 x)) = .value (a397 x) := by
  simp (disch := decide) [a397, mlir_operation]

theorem calc398 (x : Words) :
    Operation.lshr false (.value (a349 x)) (.value (42#64)) = .value (a398 x) := by
  simp (disch := decide) [a398, mlir_operation]

theorem calc399 (x : Words) :
    Operation.trunc {} (.value (a398 x)) = .value (a399 x) := by
  simp (disch := decide) [a399, mlir_operation]

theorem calc400 (x : Words) :
    Operation.lshr false (.value (a353 x)) (.value (50#64)) = .value (a400 x) := by
  simp (disch := decide) [a400, mlir_operation]

theorem calc401 (x : Words) :
    Operation.shl {nsw := true, nuw := true} (.value (a356 x)) (.value (1#64)) = .value (a401 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc402 (x : Words) :
    Operation.or true (.value (a401 x)) (.value (a400 x)) = .value (a402 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc403 (x : Words) :
    Operation.trunc {} (.value (a402 x)) = .value (a403 x) := by
  simp (disch := decide) [a403, mlir_operation]

theorem calc404 (x : Words) :
    Operation.lshr false (.value (a352 x)) (.value (7#64)) = .value (a404 x) := by
  simp (disch := decide) [a404, mlir_operation]

theorem calc405 (x : Words) :
    Operation.trunc {} (.value (a404 x)) = .value (a405 x) := by
  simp (disch := decide) [a405, mlir_operation]

theorem calc406 (x : Words) :
    Operation.lshr false (.value (a352 x)) (.value (15#64)) = .value (a406 x) := by
  simp (disch := decide) [a406, mlir_operation]

theorem calc407 (x : Words) :
    Operation.trunc {} (.value (a406 x)) = .value (a407 x) := by
  simp (disch := decide) [a407, mlir_operation]

theorem calc408 (x : Words) :
    Operation.lshr false (.value (a352 x)) (.value (23#64)) = .value (a408 x) := by
  simp (disch := decide) [a408, mlir_operation]

theorem calc409 (x : Words) :
    Operation.trunc {} (.value (a408 x)) = .value (a409 x) := by
  simp (disch := decide) [a409, mlir_operation]

theorem calc410 (x : Words) :
    Operation.lshr false (.value (a352 x)) (.value (31#64)) = .value (a410 x) := by
  simp (disch := decide) [a410, mlir_operation]

theorem calc411 (x : Words) :
    Operation.trunc {} (.value (a410 x)) = .value (a411 x) := by
  simp (disch := decide) [a411, mlir_operation]

theorem calc412 (x : Words) :
    Operation.lshr false (.value (a352 x)) (.value (39#64)) = .value (a412 x) := by
  simp (disch := decide) [a412, mlir_operation]

theorem calc413 (x : Words) :
    Operation.trunc {} (.value (a412 x)) = .value (a413 x) := by
  simp (disch := decide) [a413, mlir_operation]

theorem calc414 (x : Words) :
    Operation.lshr false (.value (a356 x)) (.value (47#64)) = .value (a414 x) := by
  simp (disch := decide) [a414, mlir_operation]

theorem calc415 (x : Words) :
    Operation.shl {nsw := true, nuw := true} (.value (a357 x)) (.value (4#64)) = .value (a415 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc416 (x : Words) :
    Operation.or true (.value (a415 x)) (.value (a414 x)) = .value (a416 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

theorem calc417 (x : Words) :
    Operation.trunc {} (.value (a416 x)) = .value (a417 x) := by
  simp (disch := decide) [a417, mlir_operation]

theorem calc418 (x : Words) :
    Operation.lshr false (.value (a355 x)) (.value (4#64)) = .value (a418 x) := by
  simp (disch := decide) [a418, mlir_operation]

theorem calc419 (x : Words) :
    Operation.trunc {} (.value (a418 x)) = .value (a419 x) := by
  simp (disch := decide) [a419, mlir_operation]

theorem calc420 (x : Words) :
    Operation.lshr false (.value (a355 x)) (.value (12#64)) = .value (a420 x) := by
  simp (disch := decide) [a420, mlir_operation]

theorem calc421 (x : Words) :
    Operation.trunc {} (.value (a420 x)) = .value (a421 x) := by
  simp (disch := decide) [a421, mlir_operation]

theorem calc422 (x : Words) :
    Operation.lshr false (.value (a355 x)) (.value (20#64)) = .value (a422 x) := by
  simp (disch := decide) [a422, mlir_operation]

theorem calc423 (x : Words) :
    Operation.trunc {} (.value (a422 x)) = .value (a423 x) := by
  simp (disch := decide) [a423, mlir_operation]

theorem calc424 (x : Words) :
    Operation.lshr false (.value (a355 x)) (.value (28#64)) = .value (a424 x) := by
  simp (disch := decide) [a424, mlir_operation]

theorem calc425 (x : Words) :
    Operation.trunc {} (.value (a424 x)) = .value (a425 x) := by
  simp (disch := decide) [a425, mlir_operation]

theorem calc426 (x : Words) :
    Operation.lshr false (.value (a355 x)) (.value (36#64)) = .value (a426 x) := by
  simp (disch := decide) [a426, mlir_operation]

theorem calc427 (x : Words) :
    Operation.trunc {} (.value (a426 x)) = .value (a427 x) := by
  simp (disch := decide) [a427, mlir_operation]

theorem calc428 (x : Words) :
    Operation.lshr false (.value (a357 x)) (.value (44#64)) = .value (a428 x) := by
  simp (disch := decide) [a428, mlir_operation]

theorem calc429 (x : Words) :
    Operation.trunc {nsw := true, nuw := true} (.value (a428 x)) = .value (a429 x) := by
  simp (disch := decide) [a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, a350, a353, a356, a357, mlir_operation, ToBytes.masked_shift_1_signed, ToBytes.masked_shift_1_unsigned, ToBytes.masked_shift_3_signed, ToBytes.masked_shift_3_unsigned, ToBytes.masked_shift_4_signed, ToBytes.masked_shift_4_unsigned, ToBytes.masked_shift_6_signed, ToBytes.masked_shift_6_unsigned, ToBytes.boundary_disjoint_1, ToBytes.boundary_disjoint_3, ToBytes.boundary_disjoint_4, ToBytes.boundary_disjoint_6, ToBytes.last_byte_trunc_signed, ToBytes.last_byte_trunc_unsigned]

def outputBytes (x : Words) : Fin 32 → BitVec 8 :=
  ![a358 x, a360 x, a362 x, a364 x, a366 x, a368 x, a373 x, a375 x, a377 x, a379 x, a381 x, a383 x, a387 x, a389 x, a391 x, a393 x, a395 x, a397 x, a399 x, a403 x, a405 x, a407 x, a409 x, a411 x, a413 x, a417 x, a419 x, a421 x, a423 x, a425 x, a427 x, a429 x]

theorem outputBytes_machine (x : Words) : outputBytes x = ToBytes.machine x := by
  funext i
  fin_cases i <;> simp only [outputBytes, a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, a358, a359, a360, a361, a362, a363, a364, a365, a366, a367, a368, a369, a370, a371, a372, a373, a374, a375, a376, a377, a378, a379, a380, a381, a382, a383, a384, a385, a386, a387, a388, a389, a390, a391, a392, a393, a394, a395, a396, a397, a398, a399, a400, a401, a402, a403, a404, a405, a406, a407, a408, a409, a410, a411, a412, a413, a414, a415, a416, a417, a418, a419, a420, a421, a422, a423, a424, a425, a426, a427, a428, a429, ToBytes.machine, ToBytes.rawBytes, ToBytes.carryMachine, ToBytes.reverseCarry, ToBytes.quotientCarry, Agave.Ed25519.Encoding.weakWord] <;> rfl

def packingEnv0 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%358 := .value (a358 x),
    %359 := .value (a359 x),
    %360 := .value (a360 x)]

def packingState0 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right) (a358 x)).storeAt (right.add 1#64) (a360 x)}

theorem packing_frame0 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv0 E x) 358 := by
  unfold packingEnv0
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment0 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e3 : E.read (%3) = .value (8#64))
    (e64 : E.read (%64) = .value (right))
    (e269 : E.read (%269) = .value (right.add 1#64))
    (e345 : E.read (%345) = .value (a345 x))
    : Cutpoint.segment (program p g) 0 465 5 E s =
      .value (packingEnv0 E x, packingState0 s right x) := by
  have f0 := hr.fits_add (k := 0) (count := 1) (by decide)
  simp only [Pointer.add_zero] at f0
  have f1 := hr.fits_add (k := 1) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 465).take 5) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv0, packingState0,
    e3, e64, e269, e345, calc358 x, calc359 x, calc360 x, f0, f1]

def packingEnv1 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%361 := .value (a361 x),
    %362 := .value (a362 x),
    %363 := .value (a363 x),
    %364 := .value (a364 x)]

def packingState1 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 2#64) (a362 x)).storeAt (right.add 3#64) (a364 x)}

theorem packing_frame1 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv1 E x) 358 := by
  unfold packingEnv1
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment1 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e4 : E.read (%4) = .value (16#64))
    (e5 : E.read (%5) = .value (24#64))
    (e270 : E.read (%270) = .value (right.add 2#64))
    (e271 : E.read (%271) = .value (right.add 3#64))
    (e345 : E.read (%345) = .value (a345 x))
    : Cutpoint.segment (program p g) 0 470 6 E s =
      .value (packingEnv1 E x, packingState1 s right x) := by
  have f2 := hr.fits_add (k := 2) (count := 1) (by decide)
  have f3 := hr.fits_add (k := 3) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 470).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv1, packingState1,
    e4, e5, e270, e271, e345, calc361 x, calc362 x, calc363 x, calc364 x, f2, f3]

def packingEnv2 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%365 := .value (a365 x),
    %366 := .value (a366 x),
    %367 := .value (a367 x),
    %368 := .value (a368 x)]

def packingState2 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 4#64) (a366 x)).storeAt (right.add 5#64) (a368 x)}

theorem packing_frame2 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv2 E x) 358 := by
  unfold packingEnv2
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment2 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e1 : E.read (%1) = .value (40#64))
    (e6 : E.read (%6) = .value (32#64))
    (e272 : E.read (%272) = .value (right.add 4#64))
    (e273 : E.read (%273) = .value (right.add 5#64))
    (e345 : E.read (%345) = .value (a345 x))
    : Cutpoint.segment (program p g) 0 476 6 E s =
      .value (packingEnv2 E x, packingState2 s right x) := by
  have f4 := hr.fits_add (k := 4) (count := 1) (by decide)
  have f5 := hr.fits_add (k := 5) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 476).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv2, packingState2,
    e1, e6, e272, e273, e345, calc365 x, calc366 x, calc367 x, calc368 x, f4, f5]

def packingEnv3 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%369 := .value (a369 x),
    %370 := .value (a370 x),
    %371 := .value (a371 x),
    %372 := .value (a372 x),
    %373 := .value (a373 x),
    %374 := .value (a374 x),
    %375 := .value (a375 x)]

def packingState3 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 6#64) (a373 x)).storeAt (right.add 7#64) (a375 x)}

theorem packing_frame3 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv3 E x) 358 := by
  unfold packingEnv3
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment3 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e12 : E.read (%12) = .value (3#64))
    (e14 : E.read (%14) = .value (5#64))
    (e15 : E.read (%15) = .value (48#64))
    (e16 : E.read (%16) = .value (7#64))
    (e274 : E.read (%274) = .value (right.add 6#64))
    (e275 : E.read (%275) = .value (right.add 7#64))
    (e345 : E.read (%345) = .value (a345 x))
    (e347 : E.read (%347) = .value (a347 x))
    (e350 : E.read (%350) = .value (a350 x))
    : Cutpoint.segment (program p g) 0 482 9 E s =
      .value (packingEnv3 E x, packingState3 s right x) := by
  have f6 := hr.fits_add (k := 6) (count := 1) (by decide)
  have f7 := hr.fits_add (k := 7) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 482).take 9) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv3, packingState3,
    e12, e14, e15, e16, e274, e275, e345, e347, e350, calc369 x, calc370 x, calc371 x, calc372 x, calc373 x, calc374 x, calc375 x, f6, f7]

def packingEnv4 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%376 := .value (a376 x),
    %377 := .value (a377 x),
    %378 := .value (a378 x),
    %379 := .value (a379 x)]

def packingState4 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 8#64) (a377 x)).storeAt (right.add 9#64) (a379 x)}

theorem packing_frame4 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv4 E x) 358 := by
  unfold packingEnv4
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment4 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e18 : E.read (%18) = .value (13#64))
    (e19 : E.read (%19) = .value (21#64))
    (e276 : E.read (%276) = .value (right.add 8#64))
    (e277 : E.read (%277) = .value (right.add 9#64))
    (e347 : E.read (%347) = .value (a347 x))
    : Cutpoint.segment (program p g) 0 491 6 E s =
      .value (packingEnv4 E x, packingState4 s right x) := by
  have f8 := hr.fits_add (k := 8) (count := 1) (by decide)
  have f9 := hr.fits_add (k := 9) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 491).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv4, packingState4,
    e18, e19, e276, e277, e347, calc376 x, calc377 x, calc378 x, calc379 x, f8, f9]

def packingEnv5 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%380 := .value (a380 x),
    %381 := .value (a381 x),
    %382 := .value (a382 x),
    %383 := .value (a383 x)]

def packingState5 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 10#64) (a381 x)).storeAt (right.add 11#64) (a383 x)}

theorem packing_frame5 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv5 E x) 358 := by
  unfold packingEnv5
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment5 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e21 : E.read (%21) = .value (29#64))
    (e23 : E.read (%23) = .value (37#64))
    (e278 : E.read (%278) = .value (right.add 10#64))
    (e279 : E.read (%279) = .value (right.add 11#64))
    (e347 : E.read (%347) = .value (a347 x))
    : Cutpoint.segment (program p g) 0 497 6 E s =
      .value (packingEnv5 E x, packingState5 s right x) := by
  have f10 := hr.fits_add (k := 10) (count := 1) (by decide)
  have f11 := hr.fits_add (k := 11) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 497).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv5, packingState5,
    e21, e23, e278, e279, e347, calc380 x, calc381 x, calc382 x, calc383 x, f10, f11]

def packingEnv6 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%384 := .value (a384 x),
    %385 := .value (a385 x),
    %386 := .value (a386 x),
    %387 := .value (a387 x),
    %388 := .value (a388 x),
    %389 := .value (a389 x)]

def packingState6 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 12#64) (a387 x)).storeAt (right.add 13#64) (a389 x)}

theorem packing_frame6 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv6 E x) 358 := by
  unfold packingEnv6
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment6 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e11 : E.read (%11) = .value (2#64))
    (e17 : E.read (%17) = .value (6#64))
    (e25 : E.read (%25) = .value (45#64))
    (e280 : E.read (%280) = .value (right.add 12#64))
    (e281 : E.read (%281) = .value (right.add 13#64))
    (e349 : E.read (%349) = .value (a349 x))
    (e350 : E.read (%350) = .value (a350 x))
    (e353 : E.read (%353) = .value (a353 x))
    : Cutpoint.segment (program p g) 0 503 8 E s =
      .value (packingEnv6 E x, packingState6 s right x) := by
  have f12 := hr.fits_add (k := 12) (count := 1) (by decide)
  have f13 := hr.fits_add (k := 13) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 503).take 8) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv6, packingState6,
    e11, e17, e25, e280, e281, e349, e350, e353, calc384 x, calc385 x, calc386 x, calc387 x, calc388 x, calc389 x, f12, f13]

def packingEnv7 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%390 := .value (a390 x),
    %391 := .value (a391 x),
    %392 := .value (a392 x),
    %393 := .value (a393 x)]

def packingState7 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 14#64) (a391 x)).storeAt (right.add 15#64) (a393 x)}

theorem packing_frame7 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv7 E x) 358 := by
  unfold packingEnv7
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment7 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e22 : E.read (%22) = .value (10#64))
    (e28 : E.read (%28) = .value (18#64))
    (e282 : E.read (%282) = .value (right.add 14#64))
    (e283 : E.read (%283) = .value (right.add 15#64))
    (e349 : E.read (%349) = .value (a349 x))
    : Cutpoint.segment (program p g) 0 511 6 E s =
      .value (packingEnv7 E x, packingState7 s right x) := by
  have f14 := hr.fits_add (k := 14) (count := 1) (by decide)
  have f15 := hr.fits_add (k := 15) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 511).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv7, packingState7,
    e22, e28, e282, e283, e349, calc390 x, calc391 x, calc392 x, calc393 x, f14, f15]

def packingEnv8 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%394 := .value (a394 x),
    %395 := .value (a395 x),
    %396 := .value (a396 x),
    %397 := .value (a397 x)]

def packingState8 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 16#64) (a395 x)).storeAt (right.add 17#64) (a397 x)}

theorem packing_frame8 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv8 E x) 358 := by
  unfold packingEnv8
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment8 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e30 : E.read (%30) = .value (26#64))
    (e31 : E.read (%31) = .value (34#64))
    (e284 : E.read (%284) = .value (right.add 16#64))
    (e285 : E.read (%285) = .value (right.add 17#64))
    (e349 : E.read (%349) = .value (a349 x))
    : Cutpoint.segment (program p g) 0 517 6 E s =
      .value (packingEnv8 E x, packingState8 s right x) := by
  have f16 := hr.fits_add (k := 16) (count := 1) (by decide)
  have f17 := hr.fits_add (k := 17) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 517).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv8, packingState8,
    e30, e31, e284, e285, e349, calc394 x, calc395 x, calc396 x, calc397 x, f16, f17]

def packingEnv9 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%398 := .value (a398 x),
    %399 := .value (a399 x),
    %400 := .value (a400 x),
    %401 := .value (a401 x),
    %402 := .value (a402 x),
    %403 := .value (a403 x)]

def packingState9 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 18#64) (a399 x)).storeAt (right.add 19#64) (a403 x)}

theorem packing_frame9 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv9 E x) 358 := by
  unfold packingEnv9
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment9 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e10 : E.read (%10) = .value (1#64))
    (e33 : E.read (%33) = .value (42#64))
    (e34 : E.read (%34) = .value (50#64))
    (e286 : E.read (%286) = .value (right.add 18#64))
    (e287 : E.read (%287) = .value (right.add 19#64))
    (e349 : E.read (%349) = .value (a349 x))
    (e353 : E.read (%353) = .value (a353 x))
    (e356 : E.read (%356) = .value (a356 x))
    : Cutpoint.segment (program p g) 0 523 8 E s =
      .value (packingEnv9 E x, packingState9 s right x) := by
  have f18 := hr.fits_add (k := 18) (count := 1) (by decide)
  have f19 := hr.fits_add (k := 19) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 523).take 8) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv9, packingState9,
    e10, e33, e34, e286, e287, e349, e353, e356, calc398 x, calc399 x, calc400 x, calc401 x, calc402 x, calc403 x, f18, f19]

def packingEnv10 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%404 := .value (a404 x),
    %405 := .value (a405 x),
    %406 := .value (a406 x),
    %407 := .value (a407 x)]

def packingState10 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 20#64) (a405 x)).storeAt (right.add 21#64) (a407 x)}

theorem packing_frame10 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv10 E x) 358 := by
  unfold packingEnv10
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment10 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e16 : E.read (%16) = .value (7#64))
    (e29 : E.read (%29) = .value (15#64))
    (e288 : E.read (%288) = .value (right.add 20#64))
    (e289 : E.read (%289) = .value (right.add 21#64))
    (e352 : E.read (%352) = .value (a352 x))
    : Cutpoint.segment (program p g) 0 531 6 E s =
      .value (packingEnv10 E x, packingState10 s right x) := by
  have f20 := hr.fits_add (k := 20) (count := 1) (by decide)
  have f21 := hr.fits_add (k := 21) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 531).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv10, packingState10,
    e16, e29, e288, e289, e352, calc404 x, calc405 x, calc406 x, calc407 x, f20, f21]

def packingEnv11 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%408 := .value (a408 x),
    %409 := .value (a409 x),
    %410 := .value (a410 x),
    %411 := .value (a411 x)]

def packingState11 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 22#64) (a409 x)).storeAt (right.add 23#64) (a411 x)}

theorem packing_frame11 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv11 E x) 358 := by
  unfold packingEnv11
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment11 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e36 : E.read (%36) = .value (23#64))
    (e38 : E.read (%38) = .value (31#64))
    (e290 : E.read (%290) = .value (right.add 22#64))
    (e291 : E.read (%291) = .value (right.add 23#64))
    (e352 : E.read (%352) = .value (a352 x))
    : Cutpoint.segment (program p g) 0 537 6 E s =
      .value (packingEnv11 E x, packingState11 s right x) := by
  have f22 := hr.fits_add (k := 22) (count := 1) (by decide)
  have f23 := hr.fits_add (k := 23) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 537).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv11, packingState11,
    e36, e38, e290, e291, e352, calc408 x, calc409 x, calc410 x, calc411 x, f22, f23]

def packingEnv12 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%412 := .value (a412 x),
    %413 := .value (a413 x),
    %414 := .value (a414 x),
    %415 := .value (a415 x),
    %416 := .value (a416 x),
    %417 := .value (a417 x)]

def packingState12 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 24#64) (a413 x)).storeAt (right.add 25#64) (a417 x)}

theorem packing_frame12 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv12 E x) 358 := by
  unfold packingEnv12
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment12 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e13 : E.read (%13) = .value (4#64))
    (e39 : E.read (%39) = .value (39#64))
    (e40 : E.read (%40) = .value (47#64))
    (e292 : E.read (%292) = .value (right.add 24#64))
    (e293 : E.read (%293) = .value (right.add 25#64))
    (e352 : E.read (%352) = .value (a352 x))
    (e356 : E.read (%356) = .value (a356 x))
    (e357 : E.read (%357) = .value (a357 x))
    : Cutpoint.segment (program p g) 0 543 8 E s =
      .value (packingEnv12 E x, packingState12 s right x) := by
  have f24 := hr.fits_add (k := 24) (count := 1) (by decide)
  have f25 := hr.fits_add (k := 25) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 543).take 8) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv12, packingState12,
    e13, e39, e40, e292, e293, e352, e356, e357, calc412 x, calc413 x, calc414 x, calc415 x, calc416 x, calc417 x, f24, f25]

def packingEnv13 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%418 := .value (a418 x),
    %419 := .value (a419 x),
    %420 := .value (a420 x),
    %421 := .value (a421 x)]

def packingState13 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 26#64) (a419 x)).storeAt (right.add 27#64) (a421 x)}

theorem packing_frame13 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv13 E x) 358 := by
  unfold packingEnv13
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment13 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e13 : E.read (%13) = .value (4#64))
    (e26 : E.read (%26) = .value (12#64))
    (e294 : E.read (%294) = .value (right.add 26#64))
    (e295 : E.read (%295) = .value (right.add 27#64))
    (e355 : E.read (%355) = .value (a355 x))
    : Cutpoint.segment (program p g) 0 551 6 E s =
      .value (packingEnv13 E x, packingState13 s right x) := by
  have f26 := hr.fits_add (k := 26) (count := 1) (by decide)
  have f27 := hr.fits_add (k := 27) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 551).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv13, packingState13,
    e13, e26, e294, e295, e355, calc418 x, calc419 x, calc420 x, calc421 x, f26, f27]

def packingEnv14 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%422 := .value (a422 x),
    %423 := .value (a423 x),
    %424 := .value (a424 x),
    %425 := .value (a425 x)]

def packingState14 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 28#64) (a423 x)).storeAt (right.add 29#64) (a425 x)}

theorem packing_frame14 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv14 E x) 358 := by
  unfold packingEnv14
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment14 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e35 : E.read (%35) = .value (20#64))
    (e43 : E.read (%43) = .value (28#64))
    (e296 : E.read (%296) = .value (right.add 28#64))
    (e297 : E.read (%297) = .value (right.add 29#64))
    (e355 : E.read (%355) = .value (a355 x))
    : Cutpoint.segment (program p g) 0 557 6 E s =
      .value (packingEnv14 E x, packingState14 s right x) := by
  have f28 := hr.fits_add (k := 28) (count := 1) (by decide)
  have f29 := hr.fits_add (k := 29) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 557).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv14, packingState14,
    e35, e43, e296, e297, e355, calc422 x, calc423 x, calc424 x, calc425 x, f28, f29]

def packingEnv15 (E : Env program.Γ) (x : Words) : Env program.Γ :=
  E[%426 := .value (a426 x),
    %427 := .value (a427 x),
    %428 := .value (a428 x),
    %429 := .value (a429 x)]

def packingState15 (s : GlobalState) (right : Pointer) (x : Words) : GlobalState :=
  {s with mem := ((s.mem).storeAt (right.add 30#64) (a427 x)).storeAt (right.add 31#64) (a429 x)}

theorem packing_frame15 (E : Env program.Γ) (x : Words) :
    Frame E (packingEnv15 E x) 358 := by
  unfold packingEnv15
  repeat apply frame_write _ _ _ _ _ _ (by decide)
  exact frame_refl E _

theorem packing_segment15 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (right : Pointer) (x : Words)
    (hr : SmallRange s.mem right 32)
    (e44 : E.read (%44) = .value (36#64))
    (e46 : E.read (%46) = .value (44#64))
    (e298 : E.read (%298) = .value (right.add 30#64))
    (e299 : E.read (%299) = .value (right.add 31#64))
    (e355 : E.read (%355) = .value (a355 x))
    (e357 : E.read (%357) = .value (a357 x))
    : Cutpoint.segment (program p g) 0 563 6 E s =
      .value (packingEnv15 E x, packingState15 s right x) := by
  have f30 := hr.fits_add (k := 30) (count := 1) (by decide)
  have f31 := hr.fits_add (k := 31) (count := 1) (by decide)
  change List.foldlM Instr.run E (((program.entry p g).body.drop 563).take 6) s = _
  dsimp only [program.entry, List.drop, List.take]
  simp (disch := first | assumption | decide) [List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
    mlir_env, mlir_effect, Operation.store, throwUBIf, packingEnv15, packingState15,
    e44, e46, e298, e299, e355, e357, calc426 x, calc427 x, calc428 x, calc429 x, f30, f31]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
