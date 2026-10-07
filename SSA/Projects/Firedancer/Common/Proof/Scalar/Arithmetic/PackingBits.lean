import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceEvaluator
import Mathlib.Tactic.IntervalCases

/-! The final four word stores as a pure bit layout. This theorem is
independent of signed arithmetic: it proves exactly which bits the masks,
shifts, and disjunctions select, for arbitrary twelve source words. -/

namespace Firedancer.Common.ScalarArithmetic

/-- Bare bit operations from `%447` through `%483`, with `%426`'s low mask. -/
def packingWords (x : Fin 12 → BitVec 64) : Fin 4 → BitVec 64 := ![
  (((x 1 <<< (21 : Nat)) &&& 4398044413952#64) ||| (x 0 &&& 2097151#64) |||
    ((x 2 <<< (42 : Nat)) &&& 9223367638808264704#64)) ||| (x 3 <<< (63 : Nat)),
  (((x 4 <<< (20 : Nat)) &&& 2199022206976#64) ||| ((x 3 >>> (1 : Nat)) &&& 1048575#64) |||
    ((x 5 <<< (41 : Nat)) &&& 4611683819404132352#64)) ||| (x 6 <<< (62 : Nat)),
  (((x 7 <<< (19 : Nat)) &&& 1099511103488#64) ||| ((x 6 >>> (2 : Nat)) &&& 524287#64) |||
    ((x 8 <<< (40 : Nat)) &&& 2305841909702066176#64)) ||| (x 9 <<< (61 : Nat)),
  (((x 9 >>> (3 : Nat)) &&& 262143#64) ||| ((x 10 <<< (18 : Nat)) &&& 549755551744#64)) |||
    (x 11 <<< (39 : Nat))]

/-- The top limb contributes 25 bits; each other limb contributes 21. -/
def packingBits (x : Fin 12 → BitVec 64) : BitVec 256 :=
  (x 11).extractLsb' 0 25 ++
  (x 10).extractLsb' 0 21 ++ (x 9).extractLsb' 0 21 ++ (x 8).extractLsb' 0 21 ++
  (x 7).extractLsb' 0 21 ++ (x 6).extractLsb' 0 21 ++ (x 5).extractLsb' 0 21 ++
  (x 4).extractLsb' 0 21 ++ (x 3).extractLsb' 0 21 ++ (x 2).extractLsb' 0 21 ++
  (x 1).extractLsb' 0 21 ++ (x 0).extractLsb' 0 21

set_option maxHeartbeats 8000000 in
theorem packingWords_bits (x : Fin 12 → BitVec 64) :
    packWords (packingWords x) = packingBits x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem]
  interval_cases i <;>
    norm_num [packWords, packingWords, packingBits,
      BitVec.getLsbD_append, BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      ← BitVec.getLsbD_eq_getElem]

end Firedancer.Common.ScalarArithmetic
