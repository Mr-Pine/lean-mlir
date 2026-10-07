import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackSafety

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def packBlock1 : BasicBlock program.Γ [] program.blockTys :=
  {program.entry with body := (program.entry.body.drop 416).take 16}

def packEnv1 (E : Env program.Γ) (x0 x1 : BitVec 64) : Env program.Γ :=
  let v362 : BitVec 64 := (x0 &&& 4503599627370495#64) >>> 48
  let v363 : BitVec 64 := (x1 &&& 4503599627370495#64) <<< 4
  let v364 : BitVec 64 := v363 ||| v362
  let v365 : BitVec 8 := (v364).setWidth 8
  let v366 : BitVec 64 := x1 >>> 4
  let v367 : BitVec 8 := (v366).setWidth 8
  let v368 : BitVec 64 := x1 >>> 12
  let v369 : BitVec 8 := (v368).setWidth 8
  let v370 : BitVec 64 := x1 >>> 20
  let v371 : BitVec 8 := (v370).setWidth 8
  let v372 : BitVec 64 := x1 >>> 28
  let v373 : BitVec 8 := (v372).setWidth 8
  let v374 : BitVec 64 := x1 >>> 36
  let v375 : BitVec 8 := (v374).setWidth 8
  let v376 : BitVec 64 := x1 >>> 44
  let v377 : BitVec 8 := (v376).setWidth 8
  E[%362 := .value v362][%363 := .value v363][%364 := .value v364][%365 := .value v365][%366 := .value v366][%367 := .value v367][%368 := .value v368][%369 := .value v369][%370 := .value v370][%371 := .value v371][%372 := .value v372][%373 := .value v373][%374 := .value v374][%375 := .value v375][%376 := .value v376][%377 := .value v377]

attribute [-simp] BitVec.setWidth_or BitVec.setWidth_and BitVec.setWidth_shiftLeft_of_le in
theorem pack_chunk1 (E : Env program.Γ) (x0 x1 : BitVec 64) (s : GlobalState)
    (h332 : E.read (%332) = .value (x0 &&& 4503599627370495#64))
    (h336 : E.read (%336) = .value x1)
    (h337 : E.read (%337) = .value (x1 &&& 4503599627370495#64))
    (hk1 : E.read (%1) = .value 4#64)
    (hk6 : E.read (%6) = .value 48#64)
    (hk10 : E.read (%10) = .value 12#64)
    (hk17 : E.read (%17) = .value 20#64)
    (hk22 : E.read (%22) = .value 36#64)
    (hk45 : E.read (%45) = .value 28#64)
    (hk46 : E.read (%46) = .value 44#64)
    : packBlock1.runBodyFrom E 0 s = .value (packEnv1 E x0 x1, s) := by
  suffices ∀ (E' : Env program.Γ), E' = E →
      packBlock1.runBodyFrom E' 0 s = .value (packEnv1 E x0 x1, s) by
    exact this E rfl
  intro E' hE
  have hsu := pack_shift_unsigned (x1 &&& 4503599627370495#64) (pack_mask_bound x1)
  have hss := pack_shift_signed (x1 &&& 4503599627370495#64) (pack_mask_bound x1)
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46, hsu, hss]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46, pack_boundary_disjoint]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  step_pure [h332, h336, h337, hk1, hk6, hk10, hk17, hk22, hk45, hk46]
  rw [BasicBlock.runBodyFrom_done (by decide)]
  subst_vars
  rfl

end Agave.Ed25519.ScalarReduce32.Execution
