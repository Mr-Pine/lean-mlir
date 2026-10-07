import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec

/-! Reusable scalar identities for the vector message-schedule network in
sha2 0.11.0 `sha512/x86_avx2.rs::fn_sha512_update_x`. Every SIMD lane uses
these same shifts. These are arithmetic identities, not execution contracts.
-/

namespace Agave.Ed25519.SHA512.Spec

/-- Exact assignment order of the AVX schedule's first sigma network. -/
def avxSmallSigma0 (x : Word) : Word :=
  let t2 := x >>> 1
  let t3 := x >>> 7
  let t1 := x <<< 56
  let t0 := t3 ^^^ t2
  let t2 := t2 >>> 7
  let t0 := t0 ^^^ t1
  let t1 := t1 <<< 7
  let t0 := t0 ^^^ t2
  t0 ^^^ t1

/-- Exact assignment order of the AVX schedule's second sigma network. -/
def avxSmallSigma1 (x : Word) : Word :=
  let t3 := x >>> 6
  let t2 := x <<< 3
  let t1 := x >>> 19
  let t3 := t3 ^^^ t2
  let t2 := t2 <<< 42
  let t3 := t3 ^^^ t1
  let t1 := t1 >>> 42
  let t3 := t3 ^^^ t2
  t3 ^^^ t1

/-- Rotate halves occupy disjoint bit ranges, so their OR equals XOR. -/
theorem rotateRight_xor (x : Word) (r : Nat) (hr : r < 64) :
    x.rotateRight r = (x >>> r) ^^^ (x <<< (64 - r)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr, hi, decide_true, Bool.true_and]
  by_cases hl : i < 64 - r
  · simp only [hl, ite_true, decide_true, Bool.not_true, Bool.false_and, Bool.xor_false]
  · have hz : x.getLsbD (r + i) = false := BitVec.getLsbD_of_ge x (r + i) (by omega)
    simp only [hl, ite_false, decide_false, Bool.not_false, Bool.true_and, hz, Bool.false_xor]

private theorem xor_left_comm (a b c : Word) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem avxSmallSigma0_eq (x : Word) : avxSmallSigma0 x = smallSigma0 x := by
  dsimp only [avxSmallSigma0, smallSigma0]
  rw [rotateRight_xor x 1 (by decide), rotateRight_xor x 8 (by decide)]
  rw [← BitVec.shiftRight_add, ← BitVec.shiftLeft_add]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

theorem avxSmallSigma1_eq (x : Word) : avxSmallSigma1 x = smallSigma1 x := by
  dsimp only [avxSmallSigma1, smallSigma1]
  rw [rotateRight_xor x 19 (by decide), rotateRight_xor x 61 (by decide)]
  rw [← BitVec.shiftRight_add, ← BitVec.shiftLeft_add]
  simp only [Nat.reduceAdd, Nat.reduceSub, BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm]

/-- One lane of the emitted network computes the FIPS schedule recurrence.
All four source words are arbitrary; no message correlation is required. -/
theorem avxScheduleWord_eq (w16 w15 w7 w2 : Word) :
    w16 + w7 + avxSmallSigma0 w15 + avxSmallSigma1 w2 =
      smallSigma1 w2 + w7 + smallSigma0 w15 + w16 := by
  rw [avxSmallSigma0_eq, avxSmallSigma1_eq]
  ac_rfl

end Agave.Ed25519.SHA512.Spec
