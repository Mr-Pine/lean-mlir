/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchOutput16Memory
import SSA.Projects.Agave.LatticeHash.MLIR.BatchReduction16
import SSA.Projects.Agave.LatticeHash.Compression
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace AgaveLatticeHash.MLIR.BatchXofOutput16
open LeanMLIR SLLVM Firedancer Blake3Compression
open InstCombine (LLVM)
open BatchReduction16 BatchOutput16

abbrev RowTy : SLLVM.Ty := .arith (.vector 16 (.bitvec 32))
def stateVars : Vector (Input11.Var RowTy) 16 :=
  #v[⟨15, rfl⟩, ⟨11, rfl⟩, ⟨7, rfl⟩, ⟨3, rfl⟩, ⟨0, rfl⟩, ⟨12, rfl⟩, ⟨8, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨1, rfl⟩, ⟨13, rfl⟩, ⟨9, rfl⟩, ⟨10, rfl⟩, ⟨6, rfl⟩, ⟨2, rfl⟩, ⟨14, rfl⟩]
def cvVars : Vector (Input11.Var RowTy) 8 :=
  #v[⟨19, rfl⟩, ⟨20, rfl⟩, ⟨21, rfl⟩, ⟨22, rfl⟩, ⟨23, rfl⟩, ⟨24, rfl⟩, ⟨25, rfl⟩, ⟨26, rfl⟩]

/-- Actual output block 11 holds the final compression state and retained root CV. -/
structure Env16 (V : Input11.Valuation) (s : State Words16) (cv : CV Words16) : Prop where
  state : ∀ i : Fin 16, V stateVars[i] = (s i).map PoisonOr.value
  saved : ∀ i : Fin 8, V cvVars[i] = (cv i).map PoisonOr.value

def wordXor (a b : Words16) : Words16 := Vector.ofFn fun lane => a[lane] ^^^ b[lane]
def columns (s : State Words16) (cv : CV Words16) : Columns16 :=
  Vector.ofFn fun i => feedForward wordXor cv s i

theorem xor16_defined_comm (a b : Words16) :
    xor16 (a.map PoisonOr.value) (b.map PoisonOr.value) =
      (wordXor b a).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp only [xor16, wordXor, Vector.getElem_ofFn, Fin.getElem_fin, Vector.getElem_map]
  change PoisonOr.value (a[i] ^^^ b[i]) = PoisonOr.value (b[i] ^^^ a[i])
  rw [BitVec.xor_comm]

/-- The actual emitted XOR/shuffle/bitcast/add network is the mathematical
column reduction, with all poison eliminated by the representation premise. -/
theorem delta16_defined (V : Input11.Valuation) (s : State Words16) (cv : CV Words16)
    (h : Env16 V s cv) :
    delta16 V = (columnSum (columns s cv)).map PoisonOr.value := by
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
  have hc0 : V ⟨19, rfl⟩ = (cv 0).map PoisonOr.value := h.saved 0
  have hc1 : V ⟨20, rfl⟩ = (cv 1).map PoisonOr.value := h.saved 1
  have hc2 : V ⟨21, rfl⟩ = (cv 2).map PoisonOr.value := h.saved 2
  have hc3 : V ⟨22, rfl⟩ = (cv 3).map PoisonOr.value := h.saved 3
  have hc4 : V ⟨23, rfl⟩ = (cv 4).map PoisonOr.value := h.saved 4
  have hc5 : V ⟨24, rfl⟩ = (cv 5).map PoisonOr.value := h.saved 5
  have hc6 : V ⟨25, rfl⟩ = (cv 6).map PoisonOr.value := h.saved 6
  have hc7 : V ⟨26, rfl⟩ = (cv 7).map PoisonOr.value := h.saved 7
  simp only [delta16, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  rw [← reduce16_defined (columns s cv)]
  rw [xor16_defined_comm (s 8) (s 0), xor16_defined_comm (s 9) (s 1), xor16_defined_comm (s 10) (s 2), xor16_defined_comm (s 11) (s 3), xor16_defined_comm (s 12) (s 4), xor16_defined_comm (s 13) (s 5), xor16_defined_comm (s 14) (s 6), xor16_defined_comm (s 15) (s 7), xor16_defined_comm (cv 0) (s 8), xor16_defined_comm (cv 1) (s 9), xor16_defined_comm (cv 2) (s 10), xor16_defined_comm (cv 3) (s 11), xor16_defined_comm (cv 4) (s 12), xor16_defined_comm (cv 5) (s 13), xor16_defined_comm (cv 6) (s 14), xor16_defined_comm (cv 7) (s 15)]
  simp only [columns, Vector.getElem_ofFn, feedForward]
  rfl

theorem feedForward_lane (s : State Words16) (cv : CV Words16)
    (word : Fin 16) (lane : Fin 16) :
    (feedForward wordXor cv s word)[lane] =
      feedForward (· ^^^ ·) (fun w => (cv w)[lane])
        (fun w => (s w)[lane]) word := by
  unfold feedForward
  split <;> simp [wordXor]

/-- Every output halfword is the wrapping sum of sixteen scalar feed-forward results. -/
theorem scalar_sum (s : State Words16) (cv : CV Words16) (half : Fin 32) :
    (columnSum (columns s cv))[half] = sum16 (fun lane =>
      AgaveLattice.halfWord
        (feedForward (· ^^^ ·) (fun w => (cv w)[lane])
          (fun w => (s w)[lane]) ⟨half.val / 2, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  rw [show (columnSum (columns s cv))[half] =
    sum16 (fun lane => ((columns s cv)[half.val / 2])[lane].extractLsb' (16 * (half.val % 2)) 16) by
      simp only [columnSum, Fin.getElem_fin, Vector.getElem_ofFn]]
  apply congrArg sum16
  funext lane
  simp only [columns, Fin.getElem_fin, Vector.getElem_ofFn]
  exact congrArg (fun x : BitVec 32 => x.extractLsb' (16 * (half.val % 2)) 16)
    (feedForward_lane s cv ⟨half.val / 2, by omega⟩ lane)

/-- A projection of the actual output delta, rather than only the mathematical columns. -/
theorem delta16_scalar_sum (V : Input11.Valuation) (s : State Words16) (cv : CV Words16)
    (h : Env16 V s cv) (half : Fin 32) :
    (delta16 V)[half] = PoisonOr.value (sum16 (fun lane =>
      AgaveLattice.halfWord
        (feedForward (· ^^^ ·) (fun w => (cv w)[lane])
          (fun w => (s w)[lane]) ⟨half.val / 2, by omega⟩)
        ⟨half.val % 2, by omega⟩)) := by
  rw [delta16_defined V s cv h]
  simp only [Fin.getElem_fin, Vector.getElem_map]
  exact congrArg PoisonOr.value (scalar_sum s cv half)

theorem scalar_laneSum (s : State Words16) (cv : CV Words16)
    (word : Fin 16) (half : Fin 2) :
    (columnSum (columns s cv))[2 * word.val + half.val]'(by omega) =
      AgaveLattice.halfWord (AgaveLattice.laneSum 16 (by omega) (fun lane =>
        feedForward (· ^^^ ·) (fun w => (cv w)[lane])
          (fun w => (s w)[lane]) word)) half := by
  rw [columnSum_laneSum]
  have h : (fun lane : Fin 16 => (columns s cv)[word][lane]) =
      (fun lane => feedForward (· ^^^ ·) (fun w => (cv w)[lane])
        (fun w => (s w)[lane]) word) := by
    funext lane
    simpa only [columns, Fin.getElem_fin, Vector.getElem_ofFn] using
      feedForward_lane s cv word lane
  rw [h]

/-- If each final-state lane is scalar root compression, the emitted delta
is exactly its sixteen-message scalar root-output halfword sum. -/
theorem root_scalar_sum (s : State Words16) (cv : CV Words16)
    (m : State Words16) (counter : Counter) (len flags : Words16)
    (hfinal : ∀ lane : Fin 16, (fun w => (s w)[lane]) =
      scalarCompressPre (fun w => (cv w)[lane]) (fun w => (m w)[lane])
        counter len[lane] (flags[lane] ||| 8)) (half : Fin 32) :
    (columnSum (columns s cv))[half] = sum16 (fun lane =>
      AgaveLattice.halfWord
        (scalarCompress (fun w => (cv w)[lane]) (fun w => (m w)[lane])
          counter len[lane] (flags[lane] ||| 8) ⟨half.val / 2, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  rw [scalar_sum]
  apply congrArg sum16
  funext lane
  rw [hfinal lane]
  rfl

/-- Discharges the accumulator-step reduction premise from the actual block's
state/CV representation; memory and scalar control hypotheses remain explicit. -/
theorem output16Spec_run_feedForward (V : Input11.Valuation) (mem : GlobalState)
    (s : State Words16) (cv : CV Words16) (env : Env16 V s cv)
    (counter : Nat) (hc : counter < 32) (ptr : Pointer)
    (old : Vector (BitVec 16) 32)
    (hcounter : V ⟨16, rfl⟩ = .value (BitVec.ofNat 64 counter))
    (hshift : V ⟨81, rfl⟩ = .value 6#64)
    (hone : V ⟨110, rfl⟩ = .value 1#64)
    (hend : V ⟨100, rfl⟩ = .value 32#64)
    (hptr : gep (V ⟨162, rfl⟩) 1 0 (.value (BitVec.ofNat 64 (64*counter))) = .value ptr)
    (fit : Fits mem.mem ptr 512)
    (read : readWord? ptr 512 mem.mem = some (packBits old)) :
    StateT.run (output16Spec V) mem = .value
      (.inr (if counter = 31 then ⟨12, rfl, .nil⟩
        else next11 V (.value (BitVec.ofNat 64 (counter+1)))),
        {mem with mem := mem.mem.splice ptr (packBits (sums32 old (columnSum (columns s cv))))}) :=
  output16Spec_run V mem counter hc ptr old (columnSum (columns s cv))
    hcounter hshift hone hend hptr (delta16_defined V s cv env) fit read

end AgaveLatticeHash.MLIR.BatchXofOutput16
