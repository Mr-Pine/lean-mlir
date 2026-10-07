import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def packBlock4 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 459).take 11}

def packEnv4 (E : Env program.Γ) (x4 : BitVec 64) : Env program.Γ :=
  let v405 : BitVec 8 := (x4).setWidth 8
  let v406 : BitVec 64 := x4 >>> 8
  let v407 : BitVec 8 := (v406).setWidth 8
  let v408 : BitVec 64 := x4 >>> 16
  let v409 : BitVec 8 := (v408).setWidth 8
  let v410 : BitVec 64 := x4 >>> 24
  let v411 : BitVec 8 := (v410).setWidth 8
  let v412 : BitVec 64 := x4 >>> 32
  let v413 : BitVec 8 := (v412).setWidth 8
  let v414 : BitVec 64 := x4 >>> 40
  let v415 : BitVec 8 := (v414).setWidth 8
  E[%405 := .value v405][%406 := .value v406][%407 := .value v407][%408 := .value v408][%409 := .value v409][%410 := .value v410][%411 := .value v411][%412 := .value v412][%413 := .value v413][%414 := .value v414][%415 := .value v415]

theorem pack_chunk4 (E : Env program.Γ) (x4 : BitVec 64) (s : GlobalState)
    (h349 : E.read (%349) = .value x4)
    (hk2 : E.read (%2) = .value 32#64)
    (hk4 : E.read (%4) = .value 40#64)
    (hk9 : E.read (%9) = .value 8#64)
    (hk13 : E.read (%13) = .value 16#64)
    (hk16 : E.read (%16) = .value 24#64)
    : packBlock4.runBodyFrom E 0 s = .value (packEnv4 E x4, s) := by
  suffices ∀ (E' : Env program.Γ), E' = E →
      packBlock4.runBodyFrom E' 0 s = .value (packEnv4 E x4, s) by
    exact this E rfl
  intro E' hE
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  step_pure [h349, hk2, hk4, hk9, hk13, hk16]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
