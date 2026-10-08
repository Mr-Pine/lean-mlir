import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCore
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail
import SSA.Projects.Firedancer.Proof.Tactics

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Agave.Ed25519.SHA512.Spec
set_option maxHeartbeats 1000000

theorem first_shl (i : Nat) (hi : i < 16) :
    LLVM.shl (.value (BitVec.ofNat 64 i)) (.value 3#64) {nsw := true, nuw := true} =
      .value (BitVec.ofNat 64 (8*i)) := by
  interval_cases i <;> decide

theorem first_add (i : Nat) (hi : i < 16) :
    LLVM.add (.value (BitVec.ofNat 64 i)) (.value 1#64) {nsw := true, nuw := true} =
      .value (BitVec.ofNat 64 (i+1)) := by
  interval_cases i <;> decide

theorem first_bswap (x : Word) :
    bswapBV x = Agave.Ed25519.Verifier.Execution.SHA512Finalization.swapBytes x := by
  rfl

theorem first_fshl50 (x : Word) : fshlBV x x 50#64 = x.rotateRight 14 := by
  exact rotateRight14_fshl x

theorem first_fshl46 (x : Word) : fshlBV x x 46#64 = x.rotateRight 18 := by
  exact rotateRight18_fshl x

theorem first_fshl23 (x : Word) : fshlBV x x 23#64 = x.rotateRight 41 := by
  exact rotateRight41_fshl x

theorem first_fshl36 (x : Word) : fshlBV x x 36#64 = x.rotateRight 28 := by
  exact rotateRight28_fshl x

theorem first_fshl30 (x : Word) : fshlBV x x 30#64 = x.rotateRight 34 := by
  exact rotateRight34_fshl x

theorem first_fshl25 (x : Word) : fshlBV x x 25#64 = x.rotateRight 39 := by
  exact rotateRight39_fshl x

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
