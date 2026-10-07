import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionScheduleVectors

/-! Four-lane semantics of the arbitrary-count path. Each pair of lanes is
an independent SHA-512 schedule. No relation between the two messages is required. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

def bulkVec (a b c d : Word) : Ty.denote (.vec 4 64) := Ty.wrap #v[a,b,c,d]

def bulkPairVec (a b : Word × Word) : Ty.denote (.vec 4 64) :=
  bulkVec a.1 a.2 b.1 b.2

theorem bulkVec_add (a b c d e f g h : Word) :
    (BinOp.vector (BinOp.add {})).compute (bulkVec a b c d) (bulkVec e f g h) =
      bulkVec (a+e) (b+f) (c+g) (d+h) := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, Ty.wrap_vec, Operation.add]

theorem bulkVec_xor (a b c d e f g h : Word) :
    (BinOp.vector BinOp.xor).compute (bulkVec a b c d) (bulkVec e f g h) =
      bulkVec (a^^^e) (b^^^f) (c^^^g) (d^^^h) := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, Ty.wrap_vec, Operation.xor]

theorem bulkVec_shl (a b c d : Word) (n : Nat) (hn : n < 64) :
    (BinOp.vector (BinOp.shl {})).compute (bulkVec a b c d)
      (bulkVec (BitVec.ofNat 64 n) (BitVec.ofNat 64 n)
        (BitVec.ofNat 64 n) (BitVec.ofNat 64 n)) =
      bulkVec (a <<< n) (b <<< n) (c <<< n) (d <<< n) := by
  have hm : n < 18446744073709551616 := by omega
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, Ty.wrap_vec, Operation.shl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, hn]

theorem bulkVec_lshr (a b c d : Word) (n : Nat) (hn : n < 64) :
    (BinOp.vector (BinOp.lshr false)).compute (bulkVec a b c d)
      (bulkVec (BitVec.ofNat 64 n) (BitVec.ofNat 64 n)
        (BitVec.ofNat 64 n) (BitVec.ofNat 64 n)) =
      bulkVec (a >>> n) (b >>> n) (c >>> n) (d >>> n) := by
  have hm : n < 18446744073709551616 := by omega
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, Ty.wrap_vec, Operation.lshr,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, hn]

theorem bulkVec_shuffle (a b c d e f g h : Word) :
    (BinOp.shufflevector #v[some 1, some 4, some 3, some 6]).compute
      (bulkVec a b c d) (bulkVec e f g h) = bulkVec b e d g := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, Ty.wrap_vec]

/-- Unselected operands may be poison: both selected lanes come from x. -/
theorem bulkVec_lo (a b c d : Word) (poison : Ty.denote (.vec 4 64)) :
    (BinOp.shufflevector #v[some 0, some 1]).compute (bulkVec a b c d) poison =
      pairVec a b := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, pairVec, Ty.wrap_vec]

theorem bulkVec_hi (a b c d : Word) (poison : Ty.denote (.vec 4 64)) :
    (BinOp.shufflevector #v[some 2, some 3]).compute (bulkVec a b c d) poison =
      pairVec c d := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, pairVec, Ty.wrap_vec]

theorem bulkVec_broadcast (a b : Word) (poison : Ty.denote (.vec 2 64)) :
    (BinOp.shufflevector #v[some 0, some 1, some 0, some 1]).compute
      (pairVec a b) poison = bulkVec a b a b := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, pairVec, Ty.wrap_vec]

theorem bulkVec_concat (a b c d : Word) :
    (BinOp.shufflevector #v[some 0, some 1, some 2, some 3]).compute
      (pairVec a b) (pairVec c d) = bulkVec a b c d := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, bulkVec, pairVec, Ty.wrap_vec]

/-- bb12 uses a different XOR association from the two-lane schedule. -/
def bulkPairSigma0 (x : Word) : Word :=
  (x >>> 1) ^^^ (x >>> 7) ^^^ (x <<< 56) ^^^ (x >>> 8) ^^^ (x <<< 63)

def bulkPairSigma1 (x : Word) : Word :=
  (x <<< 3) ^^^ (x >>> 6) ^^^ (x >>> 19) ^^^ (x <<< 45) ^^^ (x >>> 61)

theorem bulkPairSigma0_eq (x : Word) : bulkPairSigma0 x = avxSmallSigma0 x := by
  rw [← pairSigma0_eq]
  unfold bulkPairSigma0 pairSigma0
  have hx (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
    rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]
  simp only [BitVec.xor_assoc, hx, BitVec.xor_comm]

theorem bulkPairSigma1_eq (x : Word) : bulkPairSigma1 x = avxSmallSigma1 x := by
  rw [← pairSigma1_eq]
  unfold bulkPairSigma1 pairSigma1
  have hx (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
    rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]
  simp only [BitVec.xor_assoc, hx, BitVec.xor_comm]

end Agave.Ed25519.SHA512.Execution.Avx2
