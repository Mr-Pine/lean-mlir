module

public import MLIR.Syntax.Elab
public import MLIR.Run.Tactic
import Std.Tactic.BVDecide

/-! # Vector lanes: literal reads and bitcasts -/

namespace MLIR.Tests.Syntax.Bitcast

@[expose] public section

-- a literal vector's lane read by a proof step: as a `dsimp` step, folded with `0#8 ++ 0#8`, the
-- kernel (in a module) rejects the proof
example (v : BitVec 8) : [#v[0#8, v][0] ++ 0#8, 1] = [0, 1] := by
  simp [mlir_operation]

-- a lane at `⟨k, _⟩` or `↑⟨k, _⟩` is the lane at `k`, as specs write it
example (x : Vector (BitVec 64) 8) :
    (Vector.ofFn fun i : Fin 8 => x[i] + x[i.1])[3] = x[3] + x[3] := by
  simp only [Vector.getElem_ofFn, reduceGetElemLit]

-- a lane at `k` with its bound proved otherwise: the same atom for `bv_decide`
example (x : Vector (BitVec 64) 8) (h : x[0]'(by omega) &&& 1 = 1) : x[0] &&& 1 = 1 := by
  simp only [reduceGetElemLit] at h ⊢
  bv_decide

-- between vectors, lane by lane: the poison tests decided, the bits sliced from their lanes
example (a : BitVec 64) :
    Operation.bitcast (t := .vec 2 64) (t' := .vec 4 32) rfl #v[.value a, .poison] =
      #v[.value (a.extractLsb' 0 32), .value (a.extractLsb' 32 32), .poison, .poison] := by
  simp [mlir_operation]

example (a b : BitVec 8) :
    Operation.bitcast (t := .vec 2 8) (t' := .vec 1 16) rfl #v[.value a, .value b] =
      #v[.value (b ++ a)] := by
  simp [mlir_operation]

/-- `fd_r43x6_unpack`'s bytes: `u` as bytes (lanes `4 … 6` poison), shuffled, back to lanes. -/
mlir_def unpack :=
{
  ^bb0(%arg0: vector<4xi64>):
    %0 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %2 = "llvm.mlir.poison"() : () -> vector<4xi64>
    %3 = "llvm.mlir.poison"() : () -> vector<64xi8>
    %4 = "llvm.shufflevector"(%arg0, %2) <{mask = array<i32: 0, 1, 2, 3, -1, -1, -1, -1>}> : (vector<4xi64>, vector<4xi64>) -> vector<8xi64>
    %5 = "llvm.insertelement"(%4, %1, %0) : (vector<8xi64>, i64, i64) -> vector<8xi64>
    %6 = "llvm.bitcast"(%5) : (vector<8xi64>) -> vector<64xi8>
    %7 = "llvm.shufflevector"(%6, %3) <{mask = array<i32: 0, 1, 2, 3, 4, 5, 63, 63, 5, 6, 7, 8, 9, 10, 63, 63, 10, 11, 12, 13, 14, 15, 16, 63, 16, 17, 18, 19, 20, 21, 63, 63, 21, 22, 23, 24, 25, 26, 63, 63, 26, 27, 28, 29, 30, 31, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63, 63>}> : (vector<64xi8>, vector<64xi8>) -> vector<64xi8>
    %8 = "llvm.bitcast"(%7) : (vector<64xi8>) -> vector<8xi64>
    "llvm.return"(%8) : (vector<8xi64>) -> ()
}

end

/-- Bytes `k … k + 5` of `u`'s lane `i`, zero-extended. -/
abbrev bytes6 (u : BitVec 64) (k : Nat) : BitVec 64 :=
  0#16 ++ u.extractLsb' (8 * k + 40) 8 ++ u.extractLsb' (8 * k + 32) 8 ++
      u.extractLsb' (8 * k + 24) 8 ++ u.extractLsb' (8 * k + 16) 8 ++ u.extractLsb' (8 * k + 8) 8 ++
    u.extractLsb' (8 * k) 8

-- the bitcasts' poison tests decide by `step_pure` alone, so the lanes are the bytes
example (u : Vector (BitVec 64) 4) (s : GlobalState) (hwf : s.WF) :
    unpack.call (unpack.args (Ty.wrap (t := .vec 4 64) u)) s =
      .value
        (.cons
          (Ty.wrap (t := .vec 8 64)
            #v[bytes6 u[0] 0,
              0#16 ++ u[1].extractLsb' 16 8 ++ u[1].extractLsb' 8 8 ++ u[1].extractLsb' 0 8 ++
                  u[0].extractLsb' 56 8 ++ u[0].extractLsb' 48 8 ++ u[0].extractLsb' 40 8,
              0#8 ++ u[2].extractLsb' 0 8 ++ u[1].extractLsb' 56 8 ++ u[1].extractLsb' 48 8 ++
                      u[1].extractLsb' 40 8 ++ u[1].extractLsb' 32 8 ++ u[1].extractLsb' 24 8 ++
                  u[1].extractLsb' 16 8,
              bytes6 u[2] 0,
              0#16 ++ u[3].extractLsb' 16 8 ++ u[3].extractLsb' 8 8 ++ u[3].extractLsb' 0 8 ++
                  u[2].extractLsb' 56 8 ++ u[2].extractLsb' 48 8 ++ u[2].extractLsb' 40 8,
              bytes6 u[3] 2, 0, 0])
          .nil,
        s) := by
  func_init
  block_init
  iterate 9 step_pure
  finish_block
  rw [hS]
  rfl

end MLIR.Tests.Syntax.Bitcast
