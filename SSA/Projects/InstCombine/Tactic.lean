/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanMLIR.Dialects.LLVM.Syntax
public import LeanMLIR.Dialects.LLVM.SimpSet
public import SSA.Projects.InstCombine.Refinement
public import LeanMLIR.Util.ForStd
public import LeanMLIR.ErasedContext
public import LeanMLIR.Tactic

@[expose] public section

namespace InstCombine
open MLIR AST

attribute [simp_denote]
  InstCombine.Op.denote
  HVector.getN HVector.get HVector.cons_get_zero
  beq_self_eq_true Option.isSome_some

-- Fold integers into their canonical form: the builtin `Int.reduceNeg{,Succ}`, which, not being
-- `meta`, a module can only add to a simp set through its own simproc.
set_option compiler.relaxedMetaCheck true in
dsimproc [simp_denote] reduceNeg ((- _ : Int)) := Int.reduceNeg

set_option compiler.relaxedMetaCheck true in
dsimproc [simp_denote] reduceNegSucc (Int.negSucc _) := Int.reduceNegSucc

@[deprecated "use `simp_peephole` instead" (since := "2025-05-16")]
macro "simp_alive_ssa" : tactic => `(tactic| simp_peephole)

@[deprecated "use `simp_peephole` instead" (since := "2025-05-16")]
macro "simp_alive_peephole" : tactic => `(tactic| simp_peephole)
