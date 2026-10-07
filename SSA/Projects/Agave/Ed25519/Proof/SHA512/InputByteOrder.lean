import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec

/-! Reusable input-decoding cut point. Address-order message bytes are
assembled as native little-endian words by a load, then reversed by the
compiler's bswap/shuffle network before the compression rounds.
-/

namespace Agave.Ed25519.SHA512.Spec

open Agave.Ed25519.Bridge.Challenge
open LeanMLIR.RIR

/-- Address-order bytes assembled as the native little-endian load value. -/
def readWordNative (block : Bytes) (i : Nat) : Word :=
  block.getD (8 * i + 7) 0 ++ block.getD (8 * i + 6) 0 ++
  block.getD (8 * i + 5) 0 ++ block.getD (8 * i + 4) 0 ++
  block.getD (8 * i + 3) 0 ++ block.getD (8 * i + 2) 0 ++
  block.getD (8 * i + 1) 0 ++ block.getD (8 * i) 0

set_option maxHeartbeats 2000000 in
/-- The independent shift-and-append decoder is exactly byte concatenation
in big-endian order. The theorem makes no memory or input-length assumption. -/
theorem readWordBE_concat (block : Bytes) (i : Nat) :
    readWordBE block i =
      block.getD (8 * i) 0 ++ block.getD (8 * i + 1) 0 ++
      block.getD (8 * i + 2) 0 ++ block.getD (8 * i + 3) 0 ++
      block.getD (8 * i + 4) 0 ++ block.getD (8 * i + 5) 0 ++
      block.getD (8 * i + 6) 0 ++ block.getD (8 * i + 7) 0 := by
  simp only [readWordBE, List.range_succ, List.range_zero, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.add_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;>
    (simp
     repeat' (rw [BitVec.getElem_append]; norm_num))

set_option maxHeartbeats 2000000 in
/-- Exact RIR scalar bswap semantics implements the independent input
decoder once the native load is identified with its address-order bytes. -/
theorem bswap_native_readWordBE (block : Bytes) (i : Nat) :
    Operation.bswap (.value (readWordNative block i)) = .value (readWordBE block i) := by
  rw [readWordBE_concat]
  simp only [Operation.bswap, PoisonOr.value_bind, PoisonOr.pure_def,
    List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
    readWordNative]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases j <;>
    (simp
     repeat' (rw [BitVec.getElem_append]; norm_num))

end Agave.Ed25519.SHA512.Spec
