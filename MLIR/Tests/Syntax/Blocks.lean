module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func

/-! # `mlir_def` with many blocks: `20`, past the `16` where Lean's exhaustiveness check stops -/

namespace MLIR.Tests.Syntax.Blocks

@[expose] public section

mlir_def chain := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.br"(%arg0)[^bb1] : (i64) -> ()
  ^bb1(%1: i64):
    %2 = "llvm.add"(%1, %0) : (i64, i64) -> i64
    "llvm.br"(%2)[^bb2] : (i64) -> ()
  ^bb2(%3: i64):
    %4 = "llvm.add"(%3, %0) : (i64, i64) -> i64
    "llvm.br"(%4)[^bb3] : (i64) -> ()
  ^bb3(%5: i64):
    %6 = "llvm.add"(%5, %0) : (i64, i64) -> i64
    "llvm.br"(%6)[^bb4] : (i64) -> ()
  ^bb4(%7: i64):
    %8 = "llvm.add"(%7, %0) : (i64, i64) -> i64
    "llvm.br"(%8)[^bb5] : (i64) -> ()
  ^bb5(%9: i64):
    %10 = "llvm.add"(%9, %0) : (i64, i64) -> i64
    "llvm.br"(%10)[^bb6] : (i64) -> ()
  ^bb6(%11: i64):
    %12 = "llvm.add"(%11, %0) : (i64, i64) -> i64
    "llvm.br"(%12)[^bb7] : (i64) -> ()
  ^bb7(%13: i64):
    %14 = "llvm.add"(%13, %0) : (i64, i64) -> i64
    "llvm.br"(%14)[^bb8] : (i64) -> ()
  ^bb8(%15: i64):
    %16 = "llvm.add"(%15, %0) : (i64, i64) -> i64
    "llvm.br"(%16)[^bb9] : (i64) -> ()
  ^bb9(%17: i64):
    %18 = "llvm.add"(%17, %0) : (i64, i64) -> i64
    "llvm.br"(%18)[^bb10] : (i64) -> ()
  ^bb10(%19: i64):
    %20 = "llvm.add"(%19, %0) : (i64, i64) -> i64
    "llvm.br"(%20)[^bb11] : (i64) -> ()
  ^bb11(%21: i64):
    %22 = "llvm.add"(%21, %0) : (i64, i64) -> i64
    "llvm.br"(%22)[^bb12] : (i64) -> ()
  ^bb12(%23: i64):
    %24 = "llvm.add"(%23, %0) : (i64, i64) -> i64
    "llvm.br"(%24)[^bb13] : (i64) -> ()
  ^bb13(%25: i64):
    %26 = "llvm.add"(%25, %0) : (i64, i64) -> i64
    "llvm.br"(%26)[^bb14] : (i64) -> ()
  ^bb14(%27: i64):
    %28 = "llvm.add"(%27, %0) : (i64, i64) -> i64
    "llvm.br"(%28)[^bb15] : (i64) -> ()
  ^bb15(%29: i64):
    %30 = "llvm.add"(%29, %0) : (i64, i64) -> i64
    "llvm.br"(%30)[^bb16] : (i64) -> ()
  ^bb16(%31: i64):
    %32 = "llvm.add"(%31, %0) : (i64, i64) -> i64
    "llvm.br"(%32)[^bb17] : (i64) -> ()
  ^bb17(%33: i64):
    %34 = "llvm.add"(%33, %0) : (i64, i64) -> i64
    "llvm.br"(%34)[^bb18] : (i64) -> ()
  ^bb18(%35: i64):
    %36 = "llvm.add"(%35, %0) : (i64, i64) -> i64
    "llvm.br"(%36)[^bb19] : (i64) -> ()
  ^bb19(%37: i64):
    %38 = "llvm.add"(%37, %0) : (i64, i64) -> i64
    "llvm.return"(%38) : (i64) -> ()
}

end

/-- `chain` on `x`: `x + 19`, one per block after the entry; `none` for UB or no result. -/
private def run (x : BitVec 64) : Option (BitVec 64) :=
  match chain.eval 20 (chain.args (.value x)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons (.value v) .nil), _) => some v
  | _ => none

#guard run 5 == some 24
#guard run (-1) == some 18

end MLIR.Tests.Syntax.Blocks
