module

namespace MLIR.Memory

public def spliceBits {n w} (bytes : BitVec n) (off : Nat) (x : BitVec w) : BitVec n :=
  let mask := ((BitVec.allOnes w).setWidth n) <<< off
  (bytes &&& ~~~mask) ||| ((x.setWidth n) <<< off)

public section

/-- Bit `i` of a splice: from `x` inside the spliced range, else from `bytes`. -/
theorem getLsbD_spliceBits {n w : Nat} (bytes : BitVec n) (off : Nat) (x : BitVec w) (i : Nat) :
    (spliceBits bytes off x).getLsbD i =
      if off ≤ i ∧ i < off + w ∧ i < n then x.getLsbD (i - off) else bytes.getLsbD i := by
  simp only [spliceBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  grind

theorem extractLsb'_spliceBits_of_subrange {n w w' : Nat} (bytes : BitVec n) (off off' : Nat)
    (x : BitVec w) (hoff : off ≤ off') (hw : (off' - off) + w' ≤ w) (hn : off + w ≤ n) :
    (spliceBits bytes off x).extractLsb' off' w' = x.extractLsb' (off' - off) w' := by
  apply BitVec.eq_of_getLsbD_eq
  grind [getLsbD_spliceBits]

/-- Read back a spliced value exactly -/
theorem extractLsb'_spliceBits_self {n w : Nat} (bytes : BitVec n) (off : Nat) (x : BitVec w)
    (h : off + w ≤ n) : (spliceBits bytes off x).extractLsb' off w = x := by
  grind [extractLsb'_spliceBits_of_subrange]

/-- After a splice, reading from a disjoint region returns the original bits -/
theorem extractLsb'_spliceBits_of_disjoint {n w w' : Nat} (bytes : BitVec n) (off off' : Nat)
    (x : BitVec w) (h : off' + w' ≤ off ∨ off + w ≤ off') :
    (spliceBits bytes off x).extractLsb' off' w' = bytes.extractLsb' off' w' := by
  apply BitVec.eq_of_getLsbD_eq
  grind [getLsbD_spliceBits]

/-- An overwriting splice determines the returned value -/
theorem spliceBits_spliceBits_self {n w : Nat} (bytes : BitVec n) (off : Nat) (x y : BitVec w) :
    spliceBits (spliceBits bytes off x) off y = spliceBits bytes off y := by
  apply BitVec.eq_of_getLsbD_eq
  grind [getLsbD_spliceBits]

/-- If two splices are disjoint, they are commutative -/
theorem spliceBits_comm_of_disjoint {n w w' : Nat} (bytes : BitVec n) (off off' : Nat)
    (x : BitVec w) (y : BitVec w') (h : off' + w' ≤ off ∨ off + w ≤ off') :
    spliceBits (spliceBits bytes off x) off' y = spliceBits (spliceBits bytes off' y) off x := by
  apply BitVec.eq_of_getLsbD_eq
  grind [getLsbD_spliceBits]

/-- Bits `s … s + w` of all ones: all ones. -/
theorem _root_.BitVec.extractLsb'_allOnes {n s w : Nat} (h : s + w ≤ n) :
    (BitVec.allOnes n).extractLsb' s w = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes]
  simp only [hi, decide_true, Bool.true_and, decide_eq_true_eq]
  omega

/-- A slice of a slice. -/
theorem _root_.BitVec.extractLsb'_extractLsb'_add {x : BitVec n} (h : s' + w' ≤ w) :
    (x.extractLsb' s w).extractLsb' s' w' = x.extractLsb' (s + s') w' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, show s' + i < w by omega]
  congr 1
  omega

end

end MLIR.Memory
