import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Avx512.Spec.Quad

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Firedancer.Avx512 (vecBV flatten_vecBV)

/-- `peel_call h` runs the next call that returns a value, given the callee's
run equation `h` -- the form its conformance theorem is stated in. A callee
embedded by reference (`Cfg.ofCom` of a `Com` constant, or a `Cfg` constant)
is first folded back to that constant's own `denote`.

`h : StateT.run (runFunction (callee.denote V)) t = .value ([x]ₕ, t')` -/
macro "peel_call " h:term : tactic =>
  `(tactic| rw [BlockCom.run_bind_denote_call_of_value
      (by first
        | (rw [Cfg.denote_mk_ofCom]; exact $h)
        | (rw [Cfg.denote_mk_self]; exact $h)
        | exact $h)])

macro "simp_return" : tactic =>
  `(tactic| simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm, Ctxt.Valuation.singleton])

end Firedancer
