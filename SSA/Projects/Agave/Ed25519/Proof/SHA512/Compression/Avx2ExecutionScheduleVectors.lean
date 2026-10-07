import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionScheduleState

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

def pairVec (a b : Word) : Ty.denote (.vec 2 64) := Ty.wrap #v[a,b]

theorem pairVec_add (a b c d : Word) :
    (BinOp.vector (BinOp.add {})).compute (pairVec a b) (pairVec c d) =
      pairVec (a+c) (b+d) := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, pairVec, Ty.wrap_vec, Operation.add]

theorem pairVec_xor (a b c d : Word) :
    (BinOp.vector BinOp.xor).compute (pairVec a b) (pairVec c d) =
      pairVec (a^^^c) (b^^^d) := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, pairVec, Ty.wrap_vec, Operation.xor]

theorem pairVec_shl (a b : Word) (n : Nat) (hn : n < 64) :
    (BinOp.vector (BinOp.shl {})).compute (pairVec a b)
      (pairVec (BitVec.ofNat 64 n) (BitVec.ofNat 64 n)) =
      pairVec (a <<< n) (b <<< n) := by
  have hm : n < 18446744073709551616 := by omega
  ext i hi
  interval_cases i <;> simp [BinOp.compute, pairVec, Ty.wrap_vec, Operation.shl,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, hn]

theorem pairVec_lshr (a b : Word) (n : Nat) (hn : n < 64) :
    (BinOp.vector (BinOp.lshr false)).compute (pairVec a b)
      (pairVec (BitVec.ofNat 64 n) (BitVec.ofNat 64 n)) =
      pairVec (a >>> n) (b >>> n) := by
  have hm : n < 18446744073709551616 := by omega
  ext i hi
  interval_cases i <;> simp [BinOp.compute, pairVec, Ty.wrap_vec, Operation.lshr,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, hn]

theorem pairVec_shuffle (a b c d : Word) :
    (BinOp.shufflevector #v[some 1, some 2]).compute (pairVec a b) (pairVec c d) =
      pairVec b c := by
  ext i hi
  interval_cases i <;> simp [BinOp.compute, pairVec, Ty.wrap_vec]

theorem pairVec_flatten (a b : Word) :
    Ty.flatten (.vec 2 64) (pairVec a b) = .value (b ++ a) := by
  simp [pairVec, Ty.flatten_wrap_vec, BitVec.packLanes]
  rw [BitVec.zero_width_append]
  rfl

theorem pairVec_unflatten (a b : Word) :
    Ty.unflatten (.vec 2 64) (b ++ a) = pairVec a b :=
  Ty.unflatten_flatten (pairVec_flatten a b)

/-- The optimized imported sigma networks, in emitted assignment order. -/
def pairSigma0 (x : Word) : Word :=
  (x >>> 1) ^^^ (x <<< 56) ^^^ (x >>> 8) ^^^ (x <<< 63) ^^^ (x >>> 7)

def pairSigma1 (x : Word) : Word :=
  (x <<< 3) ^^^ (x >>> 19) ^^^ (x <<< 45) ^^^ (x >>> 61) ^^^ (x >>> 6)

theorem pairSigma0_eq (x : Word) : pairSigma0 x = avxSmallSigma0 x := by
  dsimp only [pairSigma0, avxSmallSigma0]
  rw [← BitVec.shiftRight_add, ← BitVec.shiftLeft_add]
  have hx (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
    rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]
  simp only [Nat.reduceAdd, BitVec.xor_comm, hx]

theorem pairSigma1_eq (x : Word) : pairSigma1 x = avxSmallSigma1 x := by
  dsimp only [pairSigma1, avxSmallSigma1]
  rw [← BitVec.shiftRight_add, ← BitVec.shiftLeft_add]
  have hx (a b c : Word) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
    rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]
  simp only [Nat.reduceAdd, BitVec.xor_comm, hx]

end Agave.Ed25519.SHA512.Execution.Avx2
