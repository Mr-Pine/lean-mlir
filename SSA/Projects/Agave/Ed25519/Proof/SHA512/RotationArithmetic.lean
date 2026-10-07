import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec

/-! The scalar LLVM funnel shifts used for SHA-512 rotations. Each identity
is proved once for arbitrary input words and reused at all round cut points.
The left side is RIR's precise `fshl` bitvector expression after definedness
and the constant shift modulus have been reduced. -/

namespace Agave.Ed25519.SHA512.Spec

theorem rotateRight_fshl (x : Word) (r : Nat) (hr : 0 < r) (hr64 : r < 64) :
    ((x ++ x) <<< (64 - r)).extractLsb' 64 64 = x.rotateRight r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.getLsbD_rotateRight]
  simp only [Nat.mod_eq_of_lt hr64, hi, decide_true, Bool.true_and]
  simp only [show 64 + i < 128 by omega, show ¬(64 + i < 64 - r) by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  split_ifs <;> first | omega | (congr 1; omega)

theorem rotateRight1_fshl (x : Word) :
    ((x ++ x) <<< 63).extractLsb' 64 64 = x.rotateRight 1 :=
  rotateRight_fshl x 1 (by decide) (by decide)
theorem rotateRight8_fshl (x : Word) :
    ((x ++ x) <<< 56).extractLsb' 64 64 = x.rotateRight 8 :=
  rotateRight_fshl x 8 (by decide) (by decide)
theorem rotateRight14_fshl (x : Word) :
    ((x ++ x) <<< 50).extractLsb' 64 64 = x.rotateRight 14 :=
  rotateRight_fshl x 14 (by decide) (by decide)
theorem rotateRight18_fshl (x : Word) :
    ((x ++ x) <<< 46).extractLsb' 64 64 = x.rotateRight 18 :=
  rotateRight_fshl x 18 (by decide) (by decide)
theorem rotateRight19_fshl (x : Word) :
    ((x ++ x) <<< 45).extractLsb' 64 64 = x.rotateRight 19 :=
  rotateRight_fshl x 19 (by decide) (by decide)
theorem rotateRight28_fshl (x : Word) :
    ((x ++ x) <<< 36).extractLsb' 64 64 = x.rotateRight 28 :=
  rotateRight_fshl x 28 (by decide) (by decide)
theorem rotateRight34_fshl (x : Word) :
    ((x ++ x) <<< 30).extractLsb' 64 64 = x.rotateRight 34 :=
  rotateRight_fshl x 34 (by decide) (by decide)
theorem rotateRight39_fshl (x : Word) :
    ((x ++ x) <<< 25).extractLsb' 64 64 = x.rotateRight 39 :=
  rotateRight_fshl x 39 (by decide) (by decide)
theorem rotateRight41_fshl (x : Word) :
    ((x ++ x) <<< 23).extractLsb' 64 64 = x.rotateRight 41 :=
  rotateRight_fshl x 41 (by decide) (by decide)
theorem rotateRight61_fshl (x : Word) :
    ((x ++ x) <<< 3).extractLsb' 64 64 = x.rotateRight 61 :=
  rotateRight_fshl x 61 (by decide) (by decide)

end Agave.Ed25519.SHA512.Spec
