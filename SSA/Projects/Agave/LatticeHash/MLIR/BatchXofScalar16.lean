/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofMemoryCore16

namespace AgaveLatticeHash.MLIR.BatchXofLoop16
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound
open InstCombine (LLVM)
open BatchReduction16
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

private theorem counterHalves (counter : Nat) (hc : counter < 32) :
    (BitVec.ofNat 64 counter).extractLsb' 0 32 = BitVec.ofNat 32 counter ∧
    (BitVec.ofNat 64 counter).extractLsb' 32 32 = 0#32 := by
  interval_cases counter <;> decide +kernel

theorem rootInitial_lane (cv : CV Words16) (len flags : Words16) (counter : Nat)
    (hc : counter < 32) (lane : Fin 16) :
    (fun i => (rootInitial cv len flags counter i)[lane]) =
      scalarInit (fun i => (cv i)[lane]) (BitVec.ofNat 64 counter) len[lane] flags[lane] := by
  obtain ⟨hl, hh⟩ := counterHalves counter hc
  funext i
  fin_cases i <;> simp [rootInitial, initState, scalarInit, hl, hh]

theorem finalState_lane (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (counter : Nat) (hc : counter < 32) (lane : Fin 16) :
    (fun i => (finalState cv len flags m counter i)[lane]) =
      scalarCompressPre (fun i => (cv i)[lane]) (fun i => (m i)[lane])
        (BitVec.ofNat 64 counter) len[lane] flags[lane] := by
  unfold finalState sevenRounds
  rw [rounds_vectors_lane, rootInitial_lane cv len flags counter hc lane]
  rfl

/-- Each stored halfword delta is the sum of sixteen scalar compression results. -/
theorem delta_scalar (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (counter : Nat) (hc : counter < 32) (half : Fin 32) :
    (delta cv len flags m counter)[half] = sum16 (fun lane =>
      AgaveLattice.halfWord
        (scalarCompress (fun i => (cv i)[lane]) (fun i => (m i)[lane])
          (BitVec.ofNat 64 counter) len[lane] flags[lane] ⟨half.val / 2, by omega⟩)
        ⟨half.val % 2, by omega⟩) := by
  rw [delta, BatchXofOutput16.scalar_sum]
  apply congrArg sum16
  funext lane
  rw [finalState_lane cv len flags m counter hc lane]
  rfl

/-- Scalar BLAKE3 contribution of all sixteen messages to one output chunk.
`flags` contains the actual root flags supplied to emitted block 9. -/
def scalarDelta (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (counter : Nat) : Vector (BitVec 16) 32 := Vector.ofFn fun half =>
  sum16 (fun lane => AgaveLattice.halfWord
    (scalarCompress (fun i => (cv i)[lane]) (fun i => (m i)[lane])
      (BitVec.ofNat 64 counter) len[lane] flags[lane] ⟨half.val / 2, by omega⟩)
    ⟨half.val % 2, by omega⟩)

attribute [local irreducible] delta finalState

theorem delta_eq_scalarDelta (cv : CV Words16) (len flags : Words16) (m : State Words16)
    (counter : Nat) (hc : counter < 32) :
    delta cv len flags m counter = scalarDelta cv len flags m counter := by
  apply Vector.ext
  intro i hi
  simpa only [scalarDelta, Fin.getElem_fin, Vector.getElem_ofFn] using
    delta_scalar cv len flags m counter hc ⟨i, hi⟩

end AgaveLatticeHash.MLIR.BatchXofLoop16
