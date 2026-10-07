import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def packBlock2 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 432).take 11}

def packEnv2 (E : Env program.Γ) (x2 : BitVec 64) : Env program.Γ :=
  let v378 : BitVec 8 := (x2).setWidth 8
  let v379 : BitVec 64 := x2 >>> 8
  let v380 : BitVec 8 := (v379).setWidth 8
  let v381 : BitVec 64 := x2 >>> 16
  let v382 : BitVec 8 := (v381).setWidth 8
  let v383 : BitVec 64 := x2 >>> 24
  let v384 : BitVec 8 := (v383).setWidth 8
  let v385 : BitVec 64 := x2 >>> 32
  let v386 : BitVec 8 := (v385).setWidth 8
  let v387 : BitVec 64 := x2 >>> 40
  let v388 : BitVec 8 := (v387).setWidth 8
  E[%378 := .value v378][%379 := .value v379][%380 := .value v380][%381 := .value v381][%382 := .value v382][%383 := .value v383][%384 := .value v384][%385 := .value v385][%386 := .value v386][%387 := .value v387][%388 := .value v388]

theorem pack_chunk2 (E : Env program.Γ) (x2 : BitVec 64) (s : GlobalState)
    (h341 : E.read (%341) = .value x2)
    (hk2 : E.read (%2) = .value 32#64)
    (hk4 : E.read (%4) = .value 40#64)
    (hk9 : E.read (%9) = .value 8#64)
    (hk13 : E.read (%13) = .value 16#64)
    (hk16 : E.read (%16) = .value 24#64)
    : packBlock2.runBodyFrom E 0 s = .value (packEnv2 E x2, s) := by
  suffices ∀ (E' : Env program.Γ), E' = E →
      packBlock2.runBodyFrom E' 0 s = .value (packEnv2 E x2, s) by
    exact this E rfl
  intro E' hE
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  step_pure [h341, hk2, hk4, hk9, hk13, hk16]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
