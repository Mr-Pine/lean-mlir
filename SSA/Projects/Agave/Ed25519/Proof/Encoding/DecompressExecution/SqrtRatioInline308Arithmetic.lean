import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.SqrtRatioInline308Negative

namespace Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
open LeanMLIR.RIR SerialFieldMul
open Agave.Ed25519.Encoding.RIR
set_option maxRecDepth 32000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def a314 (x : Words) : BitVec 64 := (x 0) >>> (51)
def a315 (x : Words) : BitVec 64 := x 1
def a316 (x : Words) : BitVec 64 := (a315 x) >>> (51)
def a317 (x : Words) : BitVec 64 := x 2
def a318 (x : Words) : BitVec 64 := (a317 x) >>> (51)
def a319 (x : Words) : BitVec 64 := x 3
def a320 (x : Words) : BitVec 64 := (a319 x) >>> (51)
def a321 (x : Words) : BitVec 64 := x 4
def a322 (x : Words) : BitVec 64 := (a321 x) >>> (51)
def a323 (x : Words) : BitVec 64 := (x 0) &&& (2251799813685247#64)
def a324 (x : Words) : BitVec 64 := (a315 x) &&& (2251799813685247#64)
def a325 (x : Words) : BitVec 64 := (a317 x) &&& (2251799813685247#64)
def a326 (x : Words) : BitVec 64 := (a319 x) &&& (2251799813685247#64)
def a327 (x : Words) : BitVec 64 := (a321 x) &&& (2251799813685247#64)
def a328 (x : Words) : BitVec 64 := (a322 x) * (19#64)
def a329 (x : Words) : BitVec 64 := (a328 x) + (a323 x)
def a330 (x : Words) : BitVec 64 := (a324 x) + (a314 x)
def a331 (x : Words) : BitVec 64 := (a325 x) + (a316 x)
def a332 (x : Words) : BitVec 64 := (a326 x) + (a318 x)
def a333 (x : Words) : BitVec 64 := (a327 x) + (a320 x)
def a334 (x : Words) : BitVec 64 := (a329 x) + (19#64)
def a335 (x : Words) : BitVec 64 := (a334 x) >>> (51)
def a336 (x : Words) : BitVec 64 := (a335 x) + (a330 x)
def a337 (x : Words) : BitVec 64 := (a336 x) >>> (51)
def a338 (x : Words) : BitVec 64 := (a337 x) + (a331 x)
def a339 (x : Words) : BitVec 64 := (a338 x) >>> (51)
def a340 (x : Words) : BitVec 64 := (a339 x) + (a332 x)
def a341 (x : Words) : BitVec 64 := (a340 x) >>> (51)
def a342 (x : Words) : BitVec 64 := (a341 x) + (a333 x)
def a343 (x : Words) : BitVec 64 := (a342 x) >>> (51)
def a344 (x : Words) : BitVec 64 := (a343 x) * (19#64)
def a345 (x : Words) : BitVec 64 := (a344 x) + (a329 x)
def a346 (x : Words) : BitVec 64 := (a345 x) >>> (51)
def a347 (x : Words) : BitVec 64 := (a346 x) + (a330 x)
def a348 (x : Words) : BitVec 64 := (a347 x) >>> (51)
def a349 (x : Words) : BitVec 64 := (a348 x) + (a331 x)
def a350 (x : Words) : BitVec 64 := (a347 x) &&& (2251799813685247#64)
def a351 (x : Words) : BitVec 64 := (a349 x) >>> (51)
def a352 (x : Words) : BitVec 64 := (a351 x) + (a332 x)
def a353 (x : Words) : BitVec 64 := (a349 x) &&& (2251799813685247#64)
def a354 (x : Words) : BitVec 64 := (a352 x) >>> (51)
def a355 (x : Words) : BitVec 64 := (a354 x) + (a333 x)
def a356 (x : Words) : BitVec 64 := (a352 x) &&& (2251799813685247#64)
def a357 (x : Words) : BitVec 64 := (a355 x) &&& (2251799813685247#64)

theorem add_comm_operation (a b : BitVec 64) :
    Operation.add {nsw := true, nuw := true} (.value a) (.value b) =
      Operation.add {nsw := true, nuw := true} (.value b) (.value a) := by
  simp only [Operation.add, PoisonOr.value_bind, BitVec.saddOverflow,
    BitVec.uaddOverflow, Int.add_comm, Nat.add_comm, BitVec.add_comm]

theorem arithmetic_operations (x : Words) :
    Operation.mul {nsw := true, nuw := true} (.value (a322 x)) (.value (19#64)) = .value (a328 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a328 x)) (.value (a323 x)) = .value (a329 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a314 x)) (.value (a324 x)) = .value (a330 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a325 x)) (.value (a316 x)) = .value (a331 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a326 x)) (.value (a318 x)) = .value (a332 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a327 x)) (.value (a320 x)) = .value (a333 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a329 x)) (.value (19#64)) = .value (a334 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a335 x)) (.value (a330 x)) = .value (a336 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a337 x)) (.value (a331 x)) = .value (a338 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a339 x)) (.value (a332 x)) = .value (a340 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a341 x)) (.value (a333 x)) = .value (a342 x) ∧
    Operation.mul {nsw := true, nuw := true} (.value (a343 x)) (.value (19#64)) = .value (a344 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a344 x)) (.value (a329 x)) = .value (a345 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a346 x)) (.value (a330 x)) = .value (a347 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a348 x)) (.value (a331 x)) = .value (a349 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a351 x)) (.value (a332 x)) = .value (a352 x) ∧
    Operation.add {nsw := true, nuw := true} (.value (a354 x)) (.value (a333 x)) = .value (a355 x) := by
  have hs := toBytesSafe3 (x 0) (x 1) (x 2) (x 3) (x 4)
  dsimp only at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.mul, PoisonOr.value_bind, h0, h1, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h2, h3, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · rw [add_comm_operation]
    simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h4, h5, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h6, h7, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h8, h9, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h10, h11, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h12, h13, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h14, h15, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h16, h17, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h18, h19, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h20, h21, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.mul, PoisonOr.value_bind, h22, h23, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h24, h25, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h26, h27, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h28, h29, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  constructor
  · simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h30, h31, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]
  simp only [a314, a315, a316, a317, a318, a319, a320, a321, a322, a323, a324, a325, a326, a327, a328, a329, a330, a331, a332, a333, a334, a335, a336, a337, a338, a339, a340, a341, a342, a343, a344, a345, a346, a347, a348, a349, a350, a351, a352, a353, a354, a355, a356, a357, Operation.add, PoisonOr.value_bind, h32, h33, Bool.false_eq_true, and_false, ite_false, PoisonOr.pure_def]

end Agave.Ed25519.Encoding.Decompress.Execution.SqrtRatio.Inline308
