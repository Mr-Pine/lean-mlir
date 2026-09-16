/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect

/-!
# `llvm.intr.bswap` and `llvm.intr.fshr`

`fd_ulong_bswap` is a byte reversal; `fd_ulong_rotate_right` is `fshr x x n`,
which at equal operands is a rotation.
-/

namespace LeanMLIR.SLLVM.Tests.Bswap

open LeanMLIR
open InstCombine (LLVM)

def rev : Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 64]) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm| {^entry(%x:i64):%r="llvm.intr.bswap"(%x):(i64)->i64"llvm.return"(%r):(i64)->()}]

example :
    (rev.denote (Ctxt.Valuation.singleton ((.value 0x0123456789abcdef#64 : LLVM.IntW 64)))).head =
      .value 0xefcdab8967452301#64 :=
  rfl

/-- Byte reversal is an involution. -/
example :
    (rev.denote (Ctxt.Valuation.singleton ((.value 0xefcdab8967452301#64 : LLVM.IntW 64)))).head =
      .value 0x0123456789abcdef#64 :=
  rfl

example : (rev.denote (Ctxt.Valuation.singleton ((.poison : LLVM.IntW 64)))).head = .poison :=
  rfl

def rotr :
    Com SLLVM (Ctxt.ofList [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64]) .pure [SLLVM.Ty.bitvec 64] :=
  [sllvm|
    {^entry(%x:i64,%n:i64):%r="llvm.intr.fshr"(%x, %x, %n):(i64, i64,
            i64)->i64"llvm.return"(%r):(i64)->()}]

/-- `fshr x x n` rotates right by `n`: the top nibble comes round to the bottom. -/
example :
    (rotr.denote
          (Ctxt.Valuation.ofHVector
            [(.value 4#64 : LLVM.IntW 64), .value 0x0123456789abcdef#64]ₕ)).head =
      .value 0xf0123456789abcde#64 :=
  rfl

/-- A zero rotation is the identity. -/
example :
    (rotr.denote
          (Ctxt.Valuation.ofHVector
            [(.value 0#64 : LLVM.IntW 64), .value 0x0123456789abcdef#64]ₕ)).head =
      .value 0x0123456789abcdef#64 :=
  rfl

end LeanMLIR.SLLVM.Tests.Bswap
