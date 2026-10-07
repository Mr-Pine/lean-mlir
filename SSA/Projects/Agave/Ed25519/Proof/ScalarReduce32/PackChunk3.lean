import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def packBlock3 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 443).take 16}

def packEnv3 (E : Env program.Γ) (x2 x3 : BitVec 64) : Env program.Γ :=
  let v389 : BitVec 64 := (x2 &&& 4503599627370495#64) >>> 48
  let v390 : BitVec 64 := x3 <<< 4
  let v391 : BitVec 64 := v390 ||| v389
  let v392 : BitVec 8 := (v391).setWidth 8
  let v393 : BitVec 64 := x3 >>> 4
  let v394 : BitVec 8 := (v393).setWidth 8
  let v395 : BitVec 64 := x3 >>> 12
  let v396 : BitVec 8 := (v395).setWidth 8
  let v397 : BitVec 64 := x3 >>> 20
  let v398 : BitVec 8 := (v397).setWidth 8
  let v399 : BitVec 64 := x3 >>> 28
  let v400 : BitVec 8 := (v399).setWidth 8
  let v401 : BitVec 64 := x3 >>> 36
  let v402 : BitVec 8 := (v401).setWidth 8
  let v403 : BitVec 64 := x3 >>> 44
  let v404 : BitVec 8 := (v403).setWidth 8
  E[%389 := .value v389][%390 := .value v390][%391 := .value v391][%392 := .value v392][%393 := .value v393][%394 := .value v394][%395 := .value v395][%396 := .value v396][%397 := .value v397][%398 := .value v398][%399 := .value v399][%400 := .value v400][%401 := .value v401][%402 := .value v402][%403 := .value v403][%404 := .value v404]

attribute [-simp] BitVec.setWidth_or BitVec.setWidth_and BitVec.setWidth_shiftLeft_of_le in
theorem pack_chunk3 (E : Env program.Γ) (x2 x3 : BitVec 64) (s : GlobalState)
    (h342 : E.read (%342) = .value (x2 &&& 4503599627370495#64))
    (h344 : E.read (%344) = .value x3)
    (hk1 : E.read (%1) = .value 4#64)
    (hk6 : E.read (%6) = .value 48#64)
    (hk10 : E.read (%10) = .value 12#64)
    (hk17 : E.read (%17) = .value 20#64)
    (hk22 : E.read (%22) = .value 36#64)
    (hk45 : E.read (%45) = .value 28#64)
    (hk46 : E.read (%46) = .value 44#64)
    (hbound : x3.toNat < 2 ^ 53)
    : packBlock3.runBodyFrom E 0 s = .value (packEnv3 E x2 x3, s) := by
  suffices ∀ (E' : Env program.Γ), E' = E →
      packBlock3.runBodyFrom E' 0 s = .value (packEnv3 E x2 x3, s) by
    exact this E rfl
  intro E' hE
  have hsu := pack_shift_unsigned x3 hbound
  have hss := pack_shift_signed x3 hbound
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46, hsu, hss]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46, pack_boundary_disjoint]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h342, h344, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
