/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Util.fd_int_if

namespace Firedancer.Avx512
open LeanMLIR SLLVM

/-- `fd_int_if(c, t, -1)`. -/
def fdIntIf : LLVM.IntW 32 → LLVM.IntW 32 → LLVM.IntW 32
  | .poison, _ => .poison
  | .value c, t => if c = 0#32 then t else .value (-1#32)

abbrev fd_int_if_spec (c t : LLVM.IntW 32) (s : GlobalState) : Prop :=
  let invocation := runFunction
    ((fd_int_if.castPureToEff .impure).denote (Ctxt.Valuation.ofPair t c))
  let result := StateT.run invocation s

  ∃ s' : GlobalState,
    result = .value ([fdIntIf c t]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512
