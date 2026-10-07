import SSA.Projects.Agave.Ed25519.Proof.SHA512.InputByteOrder
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairVectors

/-! Exact four-word byte reversal used by the original two-block load path.
Each half is tied to its own input block; the inputs need not be equal. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def bulkInitialMask : Vector (Option (Fin 64)) 32 :=
  #v[some 7, some 6, some 5, some 4, some 3, some 2, some 1, some 0, some 15, some 14, some 13, some 12, some 11, some 10, some 9, some 8, some 23, some 22, some 21, some 20, some 19, some 18, some 17, some 16, some 31, some 30, some 29, some 28, some 27, some 26, some 25, some 24]

def bulkInitialBytes (a b c d : Word) : Ty.denote (.vec 32 8) :=
  Operation.bitcast (t := .vec 4 64) (t' := .vec 32 8) rfl (bulkVec a b c d)

def bulkInitialShuffle (a b c d : Word) : Ty.denote (.vec 32 8) :=
  (BinOp.shufflevector bulkInitialMask).compute (bulkInitialBytes a b c d)
    (Ty.poisoned (.vec 32 8))

def bulkInitialWords (a b c d : Word) : Ty.denote (.vec 4 64) :=
  Operation.bitcast (t := .vec 32 8) (t' := .vec 4 64) rfl (bulkInitialShuffle a b c d)

theorem bulkInitialBytes_eq (a b c d : Word) :
    bulkInitialBytes a b c d = Ty.unflatten (.vec 32 8) (d ++ c ++ b ++ a) := by
  ext i hi
  simp [bulkInitialBytes, Operation.bitcast, bulkVec, Ty.wrap_vec, Ty.unflatten,
    Ty.extractVecElem, BitVec.packLanes, Function.comp_def]
  rw [BitVec.zero_width_append]
  rfl

theorem bulkInitialShuffle_any (a b c d : Word) (other : Ty.denote (.vec 32 8)) :
    (BinOp.shufflevector bulkInitialMask).compute (bulkInitialBytes a b c d) other =
      bulkInitialShuffle a b c d := by
  ext i hi
  interval_cases i <;> simp [bulkInitialShuffle, BinOp.compute, bulkInitialMask]

theorem bulkInitial_bitcast_wrap (xs : Vector (BitVec 8) 32) :
    Operation.bitcast (t := .vec 32 8) (t' := .vec 4 64) rfl (Ty.wrap xs) =
      Ty.unflatten (.vec 4 64) (show BitVec 256 from BitVec.packLanes xs) := by
  ext i hi
  simp [Operation.bitcast, Ty.wrap_vec, Ty.unflatten, Ty.extractVecElem, Function.comp_def]

theorem bulkVec_unflatten (a b c d : Word) :
    Ty.unflatten (.vec 4 64) (d ++ c ++ b ++ a) = bulkVec a b c d := by
  apply Ty.unflatten_flatten
  simp [bulkVec, Ty.flatten_wrap_vec, BitVec.packLanes]
  rw [BitVec.zero_width_append]
  rfl

theorem bulkInitialShuffle_native (first second : Bytes) (i j : Nat) :
    bulkInitialShuffle (readWordNative first i) (readWordNative first (i+1))
      (readWordNative second j) (readWordNative second (j+1)) =
      Ty.wrap #v[first.getD (8*(i)+7) 0,
        first.getD (8*(i)+6) 0,
        first.getD (8*(i)+5) 0,
        first.getD (8*(i)+4) 0,
        first.getD (8*(i)+3) 0,
        first.getD (8*(i)+2) 0,
        first.getD (8*(i)+1) 0,
        first.getD (8*(i)) 0,
        first.getD (8*(i+1)+7) 0,
        first.getD (8*(i+1)+6) 0,
        first.getD (8*(i+1)+5) 0,
        first.getD (8*(i+1)+4) 0,
        first.getD (8*(i+1)+3) 0,
        first.getD (8*(i+1)+2) 0,
        first.getD (8*(i+1)+1) 0,
        first.getD (8*(i+1)) 0,
        second.getD (8*(j)+7) 0,
        second.getD (8*(j)+6) 0,
        second.getD (8*(j)+5) 0,
        second.getD (8*(j)+4) 0,
        second.getD (8*(j)+3) 0,
        second.getD (8*(j)+2) 0,
        second.getD (8*(j)+1) 0,
        second.getD (8*(j)) 0,
        second.getD (8*(j+1)+7) 0,
        second.getD (8*(j+1)+6) 0,
        second.getD (8*(j+1)+5) 0,
        second.getD (8*(j+1)+4) 0,
        second.getD (8*(j+1)+3) 0,
        second.getD (8*(j+1)+2) 0,
        second.getD (8*(j+1)+1) 0,
        second.getD (8*(j+1)) 0] := by
  ext k hk
  interval_cases k <;>
    simp [bulkInitialShuffle, bulkInitialBytes_eq, bulkInitialMask, BinOp.compute,
      Ty.unflatten, Ty.extractVecElem, Ty.wrap_vec, readWordNative,
      BitVec.extractLsb'_append_eq_ite] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro n hn <;>
    interval_cases n <;>
    (simp
     repeat' (rw [BitVec.getElem_append]; norm_num))

end Agave.Ed25519.SHA512.Execution.Avx2
