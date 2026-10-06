/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofPure
import SSA.Projects.Agave.LatticeHash.MLIR.agave_portable_compress_pre
import SSA.Projects.Agave.LatticeHash.MLIR.agave_portable_compress_xof
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace PortableXof
structure Split (Γ Ω : Ctxt SLLVM.Ty) (rs : List SLLVM.Ty)
    (ss : List (List SLLVM.Ty)) where
  middle : Ctxt SLLVM.Ty
  pre : BlockPrefix Γ middle
  tail : BlockCom middle Ω rs ss

open Lean Meta Elab Term in
elab "splitPrefix% " b:term " at " n:num : term => do
  let actual ← elabTerm b none
  let rec peel (fuel : Nat) (b : Lean.Expr) : TermElabM (Lean.Expr × Lean.Expr) := do
    let b ← whnf b
    match fuel with
    | 0 =>
      let bt ← whnf (← inferType b)
      return (mkApp (Lean.mkConst ``BlockPrefix.nil) bt.getAppArgs[0]!, b)
    | fuel+1 =>
      let args := b.getAppArgs
      unless b.isAppOf ``BlockCom.var do throwError "not a variable instruction"
      let (p, t) ← peel fuel args.back!
      let p ← mkAppM ``BlockPrefix.var #[args[args.size - 2]!, p]
      return (p, t)
  let (p, t) ← peel n.getNat actual
  let bt ← whnf (← inferType t)
  mkAppM ``Split.mk #[bt.getAppArgs[0]!, p, t]

def preInput := splitPrefix% agave_portable_compress_pre.cfgEntry at 75
def xofInput := splitPrefix% agave_portable_compress_xof.cfgEntry at 76
def preRound := splitPrefix% preInput.tail at 784
def xofRound := splitPrefix% xofInput.tail at 784

theorem pre_input_parts : preInput.pre.append preInput.tail =
    agave_portable_compress_pre.cfgEntry := by rfl

theorem xof_input_parts : xofInput.pre.append xofInput.tail =
    agave_portable_compress_xof.cfgEntry := by rfl

theorem pre_round_parts : preRound.pre.append preRound.tail = preInput.tail := by rfl

theorem xof_round_parts : xofRound.pre.append xofRound.tail = xofInput.tail := by rfl

theorem rounds_same : preRound.pre = xofRound.pre := by rfl

theorem rounds_pure : preRound.pre.Pure := by
  repeat first
  | apply BlockPrefix.Pure.var (by rfl)
  | exact BlockPrefix.Pure.nil

end PortableXof
end AgaveLatticeHash.MLIR
