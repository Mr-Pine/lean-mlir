import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionScheduleVectors
import SSA.Projects.Agave.Ed25519.Proof.SHA512.InputByteOrder

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec

def initialMask : Vector (Option (Fin 32)) 16 :=
  #v[some 7, some 6, some 5, some 4, some 3, some 2, some 1, some 0,
     some 15, some 14, some 13, some 12, some 11, some 10, some 9, some 8]

def initialShuffle (bits : BitVec 128) : Ty.denote (.vec 16 8) :=
  (BinOp.shufflevector initialMask).compute (Ty.unflatten (.vec 16 8) bits)
    (Ty.poisoned (.vec 16 8))

def initialPair (bits : BitVec 128) : Ty.denote (.vec 2 64) :=
  Operation.bitcast (t := .vec 16 8) (t' := .vec 2 64) rfl (initialShuffle bits)

theorem initialShuffle_any (bits : BitVec 128) (other : Ty.denote (.vec 16 8)) :
    (BinOp.shufflevector initialMask).compute (Ty.unflatten (.vec 16 8) bits) other =
      initialShuffle bits := by
  ext i hi
  interval_cases i <;> simp [initialShuffle, BinOp.compute, initialMask]

private theorem bitcast_wrap (xs : Vector (BitVec 8) 16) :
    Operation.bitcast (t := .vec 16 8) (t' := .vec 2 64) rfl (Ty.wrap xs) =
      Ty.unflatten (.vec 2 64) (show BitVec 128 from BitVec.packLanes xs) := by
  ext i hi
  simp [Operation.bitcast, Ty.wrap_vec, Ty.unflatten, Ty.extractVecElem, Function.comp_def]

set_option maxHeartbeats 4000000 in
theorem initialPair_native (block : Agave.Ed25519.Bridge.Challenge.Bytes) (i j : Nat) :
    initialPair (readWordNative block j ++ readWordNative block i) =
      pairVec (readWordBE block i) (readWordBE block j) := by
  have hs : initialShuffle (readWordNative block j ++ readWordNative block i) =
      Ty.wrap #v[block.getD (8*i+7) 0, block.getD (8*i+6) 0,
        block.getD (8*i+5) 0, block.getD (8*i+4) 0,
        block.getD (8*i+3) 0, block.getD (8*i+2) 0,
        block.getD (8*i+1) 0, block.getD (8*i) 0,
        block.getD (8*j+7) 0, block.getD (8*j+6) 0,
        block.getD (8*j+5) 0, block.getD (8*j+4) 0,
        block.getD (8*j+3) 0, block.getD (8*j+2) 0,
        block.getD (8*j+1) 0, block.getD (8*j) 0] := by
    ext k hk
    interval_cases k <;>
      simp [initialShuffle, initialMask, BinOp.compute, Ty.unflatten,
        Ty.extractVecElem, Ty.wrap_vec, readWordNative] <;>
      apply BitVec.eq_of_getLsbD_eq <;>
      intro n hn <;>
      interval_cases n <;>
      (simp
       repeat' (rw [BitVec.getElem_append]; norm_num))
  unfold initialPair
  rw [hs, bitcast_wrap, ← pairVec_unflatten]
  apply congrArg (Ty.unflatten (.vec 2 64))
  rw [readWordBE_concat, readWordBE_concat]
  simp [BitVec.packLanes]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  interval_cases k <;>
    (simp
     repeat' (rw [BitVec.getElem_append]; norm_num))

end Agave.Ed25519.SHA512.Execution.Avx2
