import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def packBlock0 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 405).take 11}

def packEnv0 (E : Env program.Γ) (x0 : BitVec 64) : Env program.Γ :=
  let v351 : BitVec 8 := (x0).setWidth 8
  let v352 : BitVec 64 := x0 >>> 8
  let v353 : BitVec 8 := (v352).setWidth 8
  let v354 : BitVec 64 := x0 >>> 16
  let v355 : BitVec 8 := (v354).setWidth 8
  let v356 : BitVec 64 := x0 >>> 24
  let v357 : BitVec 8 := (v356).setWidth 8
  let v358 : BitVec 64 := x0 >>> 32
  let v359 : BitVec 8 := (v358).setWidth 8
  let v360 : BitVec 64 := x0 >>> 40
  let v361 : BitVec 8 := (v360).setWidth 8
  E[%351 := .value v351][%352 := .value v352][%353 := .value v353][%354 := .value v354][%355 := .value v355][%356 := .value v356][%357 := .value v357][%358 := .value v358][%359 := .value v359][%360 := .value v360][%361 := .value v361]

theorem pack_chunk0 (E : Env program.Γ) (x0 : BitVec 64) (s : GlobalState)
    (h331 : E.read (%331) = .value x0)
    (hk2 : E.read (%2) = .value 32#64)
    (hk4 : E.read (%4) = .value 40#64)
    (hk9 : E.read (%9) = .value 8#64)
    (hk13 : E.read (%13) = .value 16#64)
    (hk16 : E.read (%16) = .value 24#64)
    : packBlock0.runBodyFrom E 0 s = .value (packEnv0 E x0, s) := by
  suffices ∀ (E' : Env program.Γ), E' = E →
      packBlock0.runBodyFrom E' 0 s = .value (packEnv0 E x0, s) by
    exact this E rfl
  intro E' hE
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  step_pure [h331, hk2, hk4, hk9, hk13, hk16]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
