/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOutput
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReduction
import SSA.Projects.Agave.LatticeHash.Compression
namespace AgaveLatticeHash.MLIR.BatchXofOutput
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchReduction BatchOutput

abbrev RowTy : SLLVM.Ty := .arith (.vector 8 (.bitvec 32))
def stateVars : Vector (Input8.Var RowTy) 16 :=
  #v[⟨15, rfl⟩, ⟨11, rfl⟩, ⟨7, rfl⟩, ⟨3, rfl⟩, ⟨0, rfl⟩, ⟨12, rfl⟩, ⟨8, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨1, rfl⟩, ⟨13, rfl⟩, ⟨9, rfl⟩, ⟨10, rfl⟩, ⟨6, rfl⟩, ⟨2, rfl⟩, ⟨14, rfl⟩]
def cvVars : Vector (Input8.Var RowTy) 8 :=
  #v[⟨25, rfl⟩, ⟨24, rfl⟩, ⟨23, rfl⟩, ⟨22, rfl⟩, ⟨21, rfl⟩, ⟨20, rfl⟩, ⟨19, rfl⟩, ⟨18, rfl⟩]

/-- Representation of the final compression state and retained root CV at
actual compiler block 24, before the feed-forward/reduction instructions. -/
structure Env (V : Input8.Valuation) (s : State Words8) (cv : CV Words8) : Prop where
  state : ∀ i : Fin 16, V stateVars[i] = (s i).map PoisonOr.value
  saved : ∀ i : Fin 8, V cvVars[i] = (cv i).map PoisonOr.value

def wordXor (a b : Words8) : Words8 := Vector.ofFn fun lane => a[lane] ^^^ b[lane]
def lowerColumns (s : State Words8) (cv : CV Words8) : Columns8 :=
  Vector.ofFn fun i => feedForward wordXor cv s (i.castAdd 8)
def upperColumns (s : State Words8) (cv : CV Words8) : Columns8 :=
  Vector.ofFn fun i => feedForward wordXor cv s ⟨i.val + 8, by omega⟩

theorem xor8_defined (a b : Words8) :
    xor8 (a.map PoisonOr.value) (b.map PoisonOr.value) =
      (wordXor a b).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [xor8, wordXor, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]
  rfl

theorem xor8_defined_comm (a b : Words8) :
    xor8 (a.map PoisonOr.value) (b.map PoisonOr.value) =
      (wordXor b a).map PoisonOr.value := by
  rw [xor8_defined]
  congr 1
  apply Vector.ext
  intro i hi
  simp [wordXor, BitVec.xor_comm]

/-- The emitted lower reduction is the sum of the first sixteen scalar
output half-words after standard BLAKE3 feed-forward. -/
theorem lower_defined (V : Input8.Valuation) (s : State Words8) (cv : CV Words8)
    (h : Env V s cv) :
    lower8 V = (columnSum (lowerColumns s cv)).map PoisonOr.value := by
  have hs0 : V ⟨15, rfl⟩ = (s 0).map PoisonOr.value := h.state 0
  have hs1 : V ⟨11, rfl⟩ = (s 1).map PoisonOr.value := h.state 1
  have hs2 : V ⟨7, rfl⟩ = (s 2).map PoisonOr.value := h.state 2
  have hs3 : V ⟨3, rfl⟩ = (s 3).map PoisonOr.value := h.state 3
  have hs4 : V ⟨0, rfl⟩ = (s 4).map PoisonOr.value := h.state 4
  have hs5 : V ⟨12, rfl⟩ = (s 5).map PoisonOr.value := h.state 5
  have hs6 : V ⟨8, rfl⟩ = (s 6).map PoisonOr.value := h.state 6
  have hs7 : V ⟨4, rfl⟩ = (s 7).map PoisonOr.value := h.state 7
  have hs8 : V ⟨5, rfl⟩ = (s 8).map PoisonOr.value := h.state 8
  have hs9 : V ⟨1, rfl⟩ = (s 9).map PoisonOr.value := h.state 9
  have hs10 : V ⟨13, rfl⟩ = (s 10).map PoisonOr.value := h.state 10
  have hs11 : V ⟨9, rfl⟩ = (s 11).map PoisonOr.value := h.state 11
  have hs12 : V ⟨10, rfl⟩ = (s 12).map PoisonOr.value := h.state 12
  have hs13 : V ⟨6, rfl⟩ = (s 13).map PoisonOr.value := h.state 13
  have hs14 : V ⟨2, rfl⟩ = (s 14).map PoisonOr.value := h.state 14
  have hs15 : V ⟨14, rfl⟩ = (s 15).map PoisonOr.value := h.state 15
  simp only [lower8, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15]
  rw [← reduce8_defined (lowerColumns s cv)]
  congr 1 <;> apply xor8_defined_comm

/-- The emitted upper reduction is the sum of the final sixteen scalar
output half-words, including the retained input-CV XOR. -/
theorem upper_defined (V : Input8.Valuation) (s : State Words8) (cv : CV Words8)
    (h : Env V s cv) :
    upper8 V = (columnSum (upperColumns s cv)).map PoisonOr.value := by
  have hs8 : V ⟨5, rfl⟩ = (s 8).map PoisonOr.value := h.state 8
  have hs9 : V ⟨1, rfl⟩ = (s 9).map PoisonOr.value := h.state 9
  have hs10 : V ⟨13, rfl⟩ = (s 10).map PoisonOr.value := h.state 10
  have hs11 : V ⟨9, rfl⟩ = (s 11).map PoisonOr.value := h.state 11
  have hs12 : V ⟨10, rfl⟩ = (s 12).map PoisonOr.value := h.state 12
  have hs13 : V ⟨6, rfl⟩ = (s 13).map PoisonOr.value := h.state 13
  have hs14 : V ⟨2, rfl⟩ = (s 14).map PoisonOr.value := h.state 14
  have hs15 : V ⟨14, rfl⟩ = (s 15).map PoisonOr.value := h.state 15
  have hc0 : V ⟨25, rfl⟩ = (cv 0).map PoisonOr.value := h.saved 0
  have hc1 : V ⟨24, rfl⟩ = (cv 1).map PoisonOr.value := h.saved 1
  have hc2 : V ⟨23, rfl⟩ = (cv 2).map PoisonOr.value := h.saved 2
  have hc3 : V ⟨22, rfl⟩ = (cv 3).map PoisonOr.value := h.saved 3
  have hc4 : V ⟨21, rfl⟩ = (cv 4).map PoisonOr.value := h.saved 4
  have hc5 : V ⟨20, rfl⟩ = (cv 5).map PoisonOr.value := h.saved 5
  have hc6 : V ⟨19, rfl⟩ = (cv 6).map PoisonOr.value := h.saved 6
  have hc7 : V ⟨18, rfl⟩ = (cv 7).map PoisonOr.value := h.saved 7
  simp only [upper8, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  rw [← reduce8_defined (upperColumns s cv)]
  congr 1 <;> apply xor8_defined
/-- Feed-forward of word vectors projects to the scalar BLAKE3 operation. -/
theorem feedForward_lane (s : State Words8) (cv : CV Words8)
    (word : Fin 16) (lane : Fin 8) :
    (feedForward wordXor cv s word)[lane] =
      feedForward (· ^^^ ·) (fun w => (cv w)[lane])
        (fun w => (s w)[lane]) word := by
  unfold feedForward
  split <;> simp [wordXor]

/-- Lower output half-words are independent scalar contributions, summed
modulo 2^16 across the eight messages. -/
theorem lower_scalar_sum (s : State Words8) (cv : CV Words8) (half : Fin 16) :
    (columnSum (lowerColumns s cv))[half] = sum8 (fun lane =>
      AgaveLattice.halfWord
        (feedForward (· ^^^ ·) (fun w => (cv w)[lane])
          (fun w => (s w)[lane]) ⟨half.val / 2, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  have hb : half.val / 2 < 8 := by omega
  simp [columnSum, lowerColumns, AgaveLattice.halfWord, sum8, feedForward, wordXor, hb]

/-- Upper output half-words have the same scalar interpretation at word
indices eight through fifteen. -/
theorem upper_scalar_sum (s : State Words8) (cv : CV Words8) (half : Fin 16) :
    (columnSum (upperColumns s cv))[half] = sum8 (fun lane =>
      AgaveLattice.halfWord
        (feedForward (· ^^^ ·) (fun w => (cv w)[lane])
          (fun w => (s w)[lane]) ⟨half.val / 2 + 8, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  have hb : ¬ half.val / 2 + 8 < 8 := by omega
  simp [columnSum, upperColumns, AgaveLattice.halfWord, sum8, feedForward, wordXor, hb]

end AgaveLatticeHash.MLIR.BatchXofOutput
