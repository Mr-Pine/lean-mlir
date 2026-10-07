import SSA.Projects.Agave.Ed25519.Proof.Verifier.ValidPoint

/-! Exact byte agreement between the serial decoder's scalar fields and the
verifier's vector store layout. These equalities preserve arbitrary raw words. -/
namespace Agave.Ed25519.Encoding.Decompress.Valid
open LeanMLIR.RIR
open Verifier.Execution

private theorem pack_pair (a b : BitVec 64) : BitVec.packLanes #v[a, b] = b ++ a := by
  change (0#0 ++ b) ++ a = b ++ a
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

theorem coordinatePayload_eq (a : Key.Words) :
    Key.coordinatePayload a = a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Key.coordinatePayload, Memory.getLsbD_spliceBits,
    pack_pair,
    BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

theorem pointPayload_eq (P : Key.PointWords) :
    P.bytes = (P.T 4 ++ P.T 3 ++ P.T 2 ++ P.T 1 ++ P.T 0) ++
      (P.Z 4 ++ P.Z 3 ++ P.Z 2 ++ P.Z 1 ++ P.Z 0) ++
      (P.Y 4 ++ P.Y 3 ++ P.Y 2 ++ P.Y 1 ++ P.Y 0) ++
      (P.X 4 ++ P.X 3 ++ P.X 2 ++ P.X 1 ++ P.X 0) := by
  unfold Key.PointWords.bytes
  rw [coordinatePayload_eq, coordinatePayload_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Key.pointPayload, Memory.getLsbD_spliceBits,
    pack_pair, BitVec.getLsbD_append, BitVec.getLsbD_zero]
  grind only

end Agave.Ed25519.Encoding.Decompress.Valid
