/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.bitcast`, `llvm.select` at vector types, and `llvm.intr.memcpy`

The three operations an AVX-512 `fd_r43x6_unpack`/`ge_decode2` needs beyond
what the scalar layer used: a reinterpretation of a vector's flat bits, a
lane-wise select, and a byte copy between two pointers.
-/

namespace LeanMLIR.SLLVM.Tests.Bitcast
open LeanMLIR

/-- Two 64-bit lanes, read as four 32-bit ones: little-endian, low lane
first. -/
def split : Com SLLVM (Ctxt.ofList [SLLVM.Ty.arith (.vector 2 (.bitvec (.concrete 64)))])
    .pure [SLLVM.Ty.arith (.vector 4 (.bitvec (.concrete 32)))] := [sllvm| {
  ^entry(%v : vector<2xi64>):
    %r = "llvm.bitcast"(%v) : (vector<2xi64>) -> vector<4xi32>
    "llvm.return"(%r) : (vector<4xi32>) -> ()
}]

example :
    (split.denote (Ctxt.Valuation.singleton
      (#v[.value 0x1122334455667788#64, .value 0x99aabbccddeeff00#64]))).head
      = #v[.value 0x55667788#32, .value 0x11223344#32,
           .value 0xddeeff00#32, .value 0x99aabbcc#32] := rfl

/-- A poison lane poisons the whole result: a 32-bit lane may straddle two
64-bit ones, so there is no finer answer. -/
example :
    (split.denote (Ctxt.Valuation.singleton (#v[.poison, .value 0#64]))).head
      = #v[.poison, .poison, .poison, .poison] := rfl

-- `Ctxt.ofList` takes the block arguments in reverse declaration order.
def pick : Com SLLVM (Ctxt.ofList [SLLVM.Ty.arith (.vector 2 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 2 (.bitvec (.concrete 64))),
    SLLVM.Ty.arith (.vector 2 (.bitvec (.concrete 1)))])
    .pure [SLLVM.Ty.arith (.vector 2 (.bitvec (.concrete 64)))] := [sllvm| {
  ^entry(%c : vector<2xi1>, %x : vector<2xi64>, %y : vector<2xi64>):
    %r = "llvm.select"(%c, %x, %y) : (vector<2xi1>, vector<2xi64>, vector<2xi64>)
      -> vector<2xi64>
    "llvm.return"(%r) : (vector<2xi64>) -> ()
}]

example :
    (pick.denote (Ctxt.Valuation.ofHVector
      [#v[(.value 7#64 : LLVM.IntW 64), .value 8#64],
        #v[(.value 5#64 : LLVM.IntW 64), .value 6#64],
        #v[(.value 1#1 : LLVM.IntW 1), .value 0#1]]ₕ)).head
      = #v[.value 5#64, .value 8#64] := rfl

end LeanMLIR.SLLVM.Tests.Bitcast
