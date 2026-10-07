import SSA.Projects.Agave.Ed25519.Bridge.FiredancerReachableReady
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInitContract

namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

namespace FiredancerSHAExecution.SLLVMSource

/-- The source initializer discharges the first reachable call for every
actual input block, preserving all bytes not written by the initializer. -/
theorem reachableInit (before : Option LiveBlock) (off : BitVec 64) :
    FiredancerReachableInit programs before (initBlock before off) off :=
  firedancerReachableInit_of_initBy programs initModel init_contract
    before (initBlock before off) off rfl

/-- Concrete initializer plus only the four remaining reachable source calls.
The three append premises each mention their exact predecessor block and
input. The finish premise is a local source execution/store theorem. -/
def reachableCalls (before : Option LiveBlock) (off : BitVec 64)
    (k : BitVec (80 * 64)) (r a : BitVec 256) (message : List (BitVec 8))
    (digest : BitVec 512) (afterR afterA afterMessage finished : Option LiveBlock)
    (hR : FiredancerReachableAppend programs k (initBlock before off) afterR off
      (bytesOf (n := 32) r))
    (hA : FiredancerReachableAppend programs k afterR afterA off (bytesOf (n := 32) a))
    (hM : FiredancerReachableAppend programs k afterA afterMessage off message)
    (hF : FiredancerReachableFinish programs k afterMessage finished off digest) :
    FiredancerReachableCalls programs k before off r a message digest where
  initialized := initBlock before off
  afterR := afterR
  afterA := afterA
  afterMessage := afterMessage
  finished := finished
  init := reachableInit before off
  appendR := hR
  appendA := hA
  appendMessage := hM
  finish := hF

end FiredancerSHAExecution.SLLVMSource
end Agave.Ed25519.Bridge
