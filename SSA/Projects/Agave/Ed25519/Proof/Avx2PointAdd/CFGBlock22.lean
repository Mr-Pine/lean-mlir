import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGPhases
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGRegisterFrame
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline

/-! Generated source candidate: complete execution of one unchanged imported
point-add/subtract block, composed only from its small exact instruction slices.
Kernel validation and the guarded audit are required before this is certified. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases
open DoubleBase.ExecutionAvx2 (RegisterFrame)

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

structure Input22 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P : Point) : Prop where
  constants : Constants E
  r3 : E.read (%3) = .value 32#64
  r20 : E.read (%20) = .value 64#64
  r21 : E.read (%21) = .value 96#64
  r22 : E.read (%22) = .value 128#64
  r153 : E.read (%153) = .value 160#64
  r250 : E.read (%250) = .value q.right
  r251 : E.read (%251) = .value q.left
  r252 : E.read (%252) = .value q.product
  r253 : E.read (%253) = .value q.prepared
  r254 : E.read (%254) = .value q.negative
  r261 : E.read (%261) = .value q.output
  r264 : E.read (%264) = .value table
  r355 : E.read (%355) = .value (q.negative.add 32#64)
  r356 : E.read (%356) = .value (q.negative.add 64#64)
  r357 : E.read (%357) = .value (q.negative.add 96#64)
  r358 : E.read (%358) = .value (q.negative.add 128#64)
  r359 : E.read (%359) = .value (q.prepared.add 32#64)
  r360 : E.read (%360) = .value (q.prepared.add 64#64)
  r361 : E.read (%361) = .value (q.prepared.add 96#64)
  r362 : E.read (%362) = .value (q.prepared.add 128#64)
  r363 : E.read (%363) = .value (q.left.add 32#64)
  r364 : E.read (%364) = .value (q.left.add 64#64)
  r365 : E.read (%365) = .value (q.left.add 96#64)
  r366 : E.read (%366) = .value (q.left.add 128#64)
  r367 : E.read (%367) = .value (q.right.add 32#64)
  r368 : E.read (%368) = .value (q.right.add 64#64)
  r369 : E.read (%369) = .value (q.right.add 96#64)
  r370 : E.read (%370) = .value (q.right.add 128#64)
  r371 : E.read (%371) = .value (q.output.add 32#64)
  r372 : E.read (%372) = .value (q.output.add 64#64)
  r373 : E.read (%373) = .value (q.output.add 96#64)
  r374 : E.read (%374) = .value (q.output.add 128#64)
  r517 : E.read (%517) = Ty.wrap (packPoint P 0)
  r518 : E.read (%518) = Ty.wrap (packPoint P 1)
  r519 : E.read (%519) = Ty.wrap (packPoint P 2)
  r520 : E.read (%520) = Ty.wrap (packPoint P 3)
  r521 : E.read (%521) = Ty.wrap (packPoint P 4)
  r527 : E.read (%527) = .value (BitVec.ofNat 64 index.val)

def body22Env1 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  row22Env (E) table index

def body22Env2 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  cached22Env (body22Env1 E q table index P C) (tableRow table index) (packPoint C)

def body22Env3 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  negate22Env (body22Env2 E q table index P C)

def body22Env4 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  prepare22Env (body22Env3 E q table index P C)

def body22Env5 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load22_product4Env (body22Env4 E q table index P C) (packPoint (productPoint true P C))

def body22Env6 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  abdc22Env (body22Env5 E q table index P C)

def body22Env7 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load22_product1Env (body22Env6 E q table index P C) (packPoint (productPoint true P C))

def body22Env8 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  difference22Env (body22Env7 E q table index P C)

def body22Env9 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  adda22Env (body22Env8 E q table index P C)

def body22Env10 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  cbcb22Env (body22Env9 E q table index P C)

def body22Env11 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load22_resultEnv (body22Env10 E q table index P C) (packPoint (resultPoint true P C))

theorem body22_output (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (body22Env11 E q table index P C).read (%619) = Ty.wrap (packPoint (resultPoint true P C) 0) ∧
    (body22Env11 E q table index P C).read (%620) = Ty.wrap (packPoint (resultPoint true P C) 1) ∧
    (body22Env11 E q table index P C).read (%621) = Ty.wrap (packPoint (resultPoint true P C) 2) ∧
    (body22Env11 E q table index P C).read (%622) = Ty.wrap (packPoint (resultPoint true P C) 3) ∧
    (body22Env11 E q table index P C).read (%623) = Ty.wrap (packPoint (resultPoint true P C) 4) := by
  exact load22_result_reads _ _

theorem body22_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (body22Env11 E q table index P C) := by
  have f1 := (row22_frame (E) table index).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f2 := (cached22_frame (body22Env1 E q table index P C) (tableRow table index) (packPoint C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f3 := (negate22_frame (body22Env2 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f4 := (prepare22_frame (body22Env3 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f5 := (load22_product4_frame (body22Env4 E q table index P C) (packPoint (productPoint true P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f6 := (abdc22_frame (body22Env5 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f7 := (load22_product1_frame (body22Env6 E q table index P C) (packPoint (productPoint true P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f8 := (difference22_frame (body22Env7 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f9 := (adda22_frame (body22Env8 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f10 := (cbcb22_frame (body22Env9 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f11 := (load22_result_frame (body22Env10 E q table index P C) (packPoint (resultPoint true P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  exact (((((((((((RegisterFrame.refl 427 avx2Kernel.Γ.n E).trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11

theorem body22_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input22 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb22 p).runBodyFrom E 0 s =
      .value (body22Env11 E q table index P C, pipelineState s q true P C 7) := by
  let e1 := body22Env1 E q table index P C
  let e2 := body22Env2 E q table index P C
  let e3 := body22Env3 E q table index P C
  let e4 := body22Env4 E q table index P C
  let e5 := body22Env5 E q table index P C
  let e6 := body22Env6 E q table index P C
  let e7 := body22Env7 E q table index P C
  let e8 := body22Env8 E q table index P C
  let e9 := body22Env9 E q table index P C
  let e10 := body22Env10 E q table index P C
  let e11 := body22Env11 E q table index P C
  have h0 : runSlice (avx2Kernel.bb22 p) E 0 1 (pipelineState s q true P C 0) =
      .value (e1, (pipelineState s q true P C 0)) := by
    exact row22_slice p E (pipelineState s q true P C 0) table index bytes htable hindex (hreg.r264) (hreg.r527)
  have f1 : RegisterFrame 529 530 E e1 :=
    row22_frame E table index
  have v529 : e1.read (%529) = .value (tableRow table index) := by
    simp [e1, body22Env1, row22Env, mlir_env]
  have r1_3 := (f1.read (%3) (by decide)).trans (hreg.r3)
  have r1_20 := (f1.read (%20) (by decide)).trans (hreg.r20)
  have r1_21 := (f1.read (%21) (by decide)).trans (hreg.r21)
  have r1_22 := (f1.read (%22) (by decide)).trans (hreg.r22)
  have h1 : runSlice (avx2Kernel.bb22 p) e1 1 9 (pipelineState s q true P C 0) =
      .value (e2, (pipelineState s q true P C 0)) := by
    exact cached22_slice p e1 (pipelineState s q true P C 0) (tableRow table index) (packPoint C) (hmem.live 6) hcache (v529) r1_3 r1_20 r1_21 r1_22
  have f2 : RegisterFrame 530 539 e1 e2 :=
    cached22_frame e1 (tableRow table index) (packPoint C)
  have v530 : e2.read (%530) = Ty.wrap (packPoint (C) 0) := by
    simp [e2, body22Env2, cached22Env, mlir_env]
  have v532 : e2.read (%532) = Ty.wrap (packPoint (C) 1) := by
    simp [e2, body22Env2, cached22Env, mlir_env]
  have v534 : e2.read (%534) = Ty.wrap (packPoint (C) 2) := by
    simp [e2, body22Env2, cached22Env, mlir_env]
  have v536 : e2.read (%536) = Ty.wrap (packPoint (C) 3) := by
    simp [e2, body22Env2, cached22Env, mlir_env]
  have v538 : e2.read (%538) = Ty.wrap (packPoint (C) 4) := by
    simp [e2, body22Env2, cached22Env, mlir_env]
  have h10 : runSlice (avx2Kernel.bb22 p) e2 10 1 (pipelineState s q true P C 0) =
      .value (e2, (pipelineState s q true P C 0)) := by
    exact lifetime22_10_slice p e2 (pipelineState s q true P C 0)
  have h11 : runSlice (avx2Kernel.bb22 p) e2 11 15 (pipelineState s q true P C 0) =
      .value (e3, (pipelineState s q true P C 0)) := by
    exact negate22_slice p e2 (pipelineState s q true P C 0)
  have f3 : RegisterFrame 539 554 e2 e3 :=
    negate22_frame e2
  have r1_26 := (f1.read (%26) (by decide)).trans (hreg.constants.poison)
  have r2_26 := (f2.read (%26) (by decide)).trans r1_26
  have r1_135 := (f1.read (%135) (by decide)).trans (hreg.constants.prepare0)
  have r2_135 := (f2.read (%135) (by decide)).trans r1_135
  have r1_152 := (f1.read (%152) (by decide)).trans (hreg.constants.prepareN)
  have r2_152 := (f2.read (%152) (by decide)).trans r1_152
  have r1_170 := (f1.read (%170) (by decide)).trans (hreg.constants.difference0)
  have r2_170 := (f2.read (%170) (by decide)).trans r1_170
  have r1_187 := (f1.read (%187) (by decide)).trans (hreg.constants.differenceN)
  have r2_187 := (f2.read (%187) (by decide)).trans r1_187
  have r1_204 := (f1.read (%204) (by decide)).trans (hreg.constants.negate0)
  have r2_204 := (f2.read (%204) (by decide)).trans r1_204
  have r1_221 := (f1.read (%221) (by decide)).trans (hreg.constants.negateN)
  have r2_221 := (f2.read (%221) (by decide)).trans r1_221
  have cnegate22 : Constants e2 := ⟨r2_26, r2_135, r2_152, r2_170, r2_187, r2_204, r2_221⟩
  have inegate22 : negate22Inputs e2 (packPoint C) := ⟨(v530), (v532), (v534), (v536), (v538)⟩
  have v549 := negate22_field e2 C hC cnegate22 inegate22 0
  have v550 := negate22_field e2 C hC cnegate22 inegate22 1
  have v551 := negate22_field e2 C hC cnegate22 inegate22 2
  have v552 := negate22_field e2 C hC cnegate22 inegate22 3
  have v553 := negate22_field e2 C hC cnegate22 inegate22 4
  have r1_254 := (f1.read (%254) (by decide)).trans (hreg.r254)
  have r2_254 := (f2.read (%254) (by decide)).trans r1_254
  have r3_254 := (f3.read (%254) (by decide)).trans r2_254
  have r1_355 := (f1.read (%355) (by decide)).trans (hreg.r355)
  have r2_355 := (f2.read (%355) (by decide)).trans r1_355
  have r3_355 := (f3.read (%355) (by decide)).trans r2_355
  have r1_356 := (f1.read (%356) (by decide)).trans (hreg.r356)
  have r2_356 := (f2.read (%356) (by decide)).trans r1_356
  have r3_356 := (f3.read (%356) (by decide)).trans r2_356
  have r1_357 := (f1.read (%357) (by decide)).trans (hreg.r357)
  have r2_357 := (f2.read (%357) (by decide)).trans r1_357
  have r3_357 := (f3.read (%357) (by decide)).trans r2_357
  have r1_358 := (f1.read (%358) (by decide)).trans (hreg.r358)
  have r2_358 := (f2.read (%358) (by decide)).trans r1_358
  have r3_358 := (f3.read (%358) (by decide)).trans r2_358
  have h26 : runSlice (avx2Kernel.bb22 p) e3 26 5 (pipelineState s q true P C 0) =
      .value (e3, (pipelineState s q true P C 1)) := by
    exact negate22_store_slice p e3 (pipelineState s q true P C 0) q.negative (packPoint (negate C)) (pipelineState_live s q true P C (hmem.live 5) 0) r3_254 (v549) r3_355 (v550) r3_356 (v551) r3_357 (v552) r3_358 (v553)
  have h31 : runSlice (avx2Kernel.bb22 p) e3 31 1 (pipelineState s q true P C 1) =
      .value (e3, (pipelineState s q true P C 1)) := by
    exact lifetime22_31_slice p e3 (pipelineState s q true P C 1)
  have h32 : runSlice (avx2Kernel.bb22 p) e3 32 25 (pipelineState s q true P C 1) =
      .value (e4, (pipelineState s q true P C 1)) := by
    exact prepare22_slice p e3 (pipelineState s q true P C 1)
  have f4 : RegisterFrame 554 579 e3 e4 :=
    prepare22_frame e3
  have r1_517 := (f1.read (%517) (by decide)).trans (hreg.r517)
  have r2_517 := (f2.read (%517) (by decide)).trans r1_517
  have r3_517 := (f3.read (%517) (by decide)).trans r2_517
  have r1_518 := (f1.read (%518) (by decide)).trans (hreg.r518)
  have r2_518 := (f2.read (%518) (by decide)).trans r1_518
  have r3_518 := (f3.read (%518) (by decide)).trans r2_518
  have r1_519 := (f1.read (%519) (by decide)).trans (hreg.r519)
  have r2_519 := (f2.read (%519) (by decide)).trans r1_519
  have r3_519 := (f3.read (%519) (by decide)).trans r2_519
  have r1_520 := (f1.read (%520) (by decide)).trans (hreg.r520)
  have r2_520 := (f2.read (%520) (by decide)).trans r1_520
  have r3_520 := (f3.read (%520) (by decide)).trans r2_520
  have r1_521 := (f1.read (%521) (by decide)).trans (hreg.r521)
  have r2_521 := (f2.read (%521) (by decide)).trans r1_521
  have r3_521 := (f3.read (%521) (by decide)).trans r2_521
  have r3_26 := (f3.read (%26) (by decide)).trans r2_26
  have r3_135 := (f3.read (%135) (by decide)).trans r2_135
  have r3_152 := (f3.read (%152) (by decide)).trans r2_152
  have r3_170 := (f3.read (%170) (by decide)).trans r2_170
  have r3_187 := (f3.read (%187) (by decide)).trans r2_187
  have r3_204 := (f3.read (%204) (by decide)).trans r2_204
  have r3_221 := (f3.read (%221) (by decide)).trans r2_221
  have cprepare22 : Constants e3 := ⟨r3_26, r3_135, r3_152, r3_170, r3_187, r3_204, r3_221⟩
  have iprepare22 : prepare22Inputs e3 (packPoint P) := ⟨r3_517, r3_518, r3_519, r3_520, r3_521⟩
  have v574 := prepare22_field e3 P hP cprepare22 iprepare22 0
  have v575 := prepare22_field e3 P hP cprepare22 iprepare22 1
  have v576 := prepare22_field e3 P hP cprepare22 iprepare22 2
  have v577 := prepare22_field e3 P hP cprepare22 iprepare22 3
  have v578 := prepare22_field e3 P hP cprepare22 iprepare22 4
  have r1_253 := (f1.read (%253) (by decide)).trans (hreg.r253)
  have r2_253 := (f2.read (%253) (by decide)).trans r1_253
  have r3_253 := (f3.read (%253) (by decide)).trans r2_253
  have r4_253 := (f4.read (%253) (by decide)).trans r3_253
  have r1_359 := (f1.read (%359) (by decide)).trans (hreg.r359)
  have r2_359 := (f2.read (%359) (by decide)).trans r1_359
  have r3_359 := (f3.read (%359) (by decide)).trans r2_359
  have r4_359 := (f4.read (%359) (by decide)).trans r3_359
  have r1_360 := (f1.read (%360) (by decide)).trans (hreg.r360)
  have r2_360 := (f2.read (%360) (by decide)).trans r1_360
  have r3_360 := (f3.read (%360) (by decide)).trans r2_360
  have r4_360 := (f4.read (%360) (by decide)).trans r3_360
  have r1_361 := (f1.read (%361) (by decide)).trans (hreg.r361)
  have r2_361 := (f2.read (%361) (by decide)).trans r1_361
  have r3_361 := (f3.read (%361) (by decide)).trans r2_361
  have r4_361 := (f4.read (%361) (by decide)).trans r3_361
  have r1_362 := (f1.read (%362) (by decide)).trans (hreg.r362)
  have r2_362 := (f2.read (%362) (by decide)).trans r1_362
  have r3_362 := (f3.read (%362) (by decide)).trans r2_362
  have r4_362 := (f4.read (%362) (by decide)).trans r3_362
  have h57 : runSlice (avx2Kernel.bb22 p) e4 57 5 (pipelineState s q true P C 1) =
      .value (e4, (pipelineState s q true P C 2)) := by
    exact prepare22_store_slice p e4 (pipelineState s q true P C 1) q.prepared (packPoint (prepare P)) (pipelineState_live s q true P C (hmem.live 1) 1) r4_253 (v574) r4_359 (v575) r4_360 (v576) r4_361 (v577) r4_362 (v578)
  have h62 : runSlice (avx2Kernel.bb22 p) e4 62 1 (pipelineState s q true P C 2) =
      .value (e4, (pipelineState s q true P C 2)) := by
    exact lifetime22_62_slice p e4 (pipelineState s q true P C 2)
  have r1_252 := (f1.read (%252) (by decide)).trans (hreg.r252)
  have r2_252 := (f2.read (%252) (by decide)).trans r1_252
  have r3_252 := (f3.read (%252) (by decide)).trans r2_252
  have r4_252 := (f4.read (%252) (by decide)).trans r3_252
  have r4_254 := (f4.read (%254) (by decide)).trans r3_254
  have h63 : runSlice (avx2Kernel.bb22 p) e4 63 1 (pipelineState s q true P C 2) =
      .value (e4, (pipelineState s q true P C 3)) := by
    exact multiply22_0_slice p e4 (pipelineState s q true P C 2) q.product q.prepared (cachePointer true q (tableRow table index)) (prepare P) (chosenCache true C) hmul (pipelineState_wf s q true P C hmem.wf 2) (pipelineState_live s q true P C (hmem.live 2) 2) (pipelineState_live s q true P C (hmem.live 1) 2) (pipelineState_live s q true P C (hmem.live 5) 2) (prepare_wide hP) (chosenCache_wide true hC) (prepared_read s q true P C (hmem.live 1)) (cache_read s q true (tableRow table index) P C hmem hcache) r4_252 r4_253 r4_254
  have r1_153 := (f1.read (%153) (by decide)).trans (hreg.r153)
  have r2_153 := (f2.read (%153) (by decide)).trans r1_153
  have r3_153 := (f3.read (%153) (by decide)).trans r2_153
  have r4_153 := (f4.read (%153) (by decide)).trans r3_153
  have h64 : runSlice (avx2Kernel.bb22 p) e4 64 1 (pipelineState s q true P C 3) =
      .value (e4, (pipelineState s q true P C 4)) := by
    exact copy22_slice p e4 (pipelineState s q true P C 3) q.prepared q.product (pipelineState_live s q true P C (hmem.live 1) 3) (pipelineState_live s q true P C (hmem.live 2) 3) (Or.inl (hmem.ne 1 2 (by decide))) r4_253 r4_252 r4_153
  have h65 : runSlice (avx2Kernel.bb22 p) e4 65 1 (pipelineState s q true P C 4) =
      .value (e4, (pipelineState s q true P C 4)) := by
    exact lifetime22_65_slice p e4 (pipelineState s q true P C 4)
  have h66 : runSlice (avx2Kernel.bb22 p) e4 66 4 (pipelineState s q true P C 4) =
      .value (e5, (pipelineState s q true P C 4)) := by
    exact load22_product4_slice p e4 (pipelineState s q true P C 4) q.prepared (packPoint (productPoint true P C)) (pipelineState_live s q true P C (hmem.live 1) 4) (copied_read s q true P C (hmem.live 1) (hmem.live 2)) r4_253 r4_359 r4_360 r4_361
  have f5 : RegisterFrame 579 583 e4 e5 :=
    load22_product4_frame e4 (packPoint (productPoint true P C))
  have v579 : e5.read (%579) = Ty.wrap (packPoint (productPoint true P C) 0) := by
    simp [e5, body22Env5, load22_product4Env, mlir_env]
  have v580 : e5.read (%580) = Ty.wrap (packPoint (productPoint true P C) 1) := by
    simp [e5, body22Env5, load22_product4Env, mlir_env]
  have v581 : e5.read (%581) = Ty.wrap (packPoint (productPoint true P C) 2) := by
    simp [e5, body22Env5, load22_product4Env, mlir_env]
  have v582 : e5.read (%582) = Ty.wrap (packPoint (productPoint true P C) 3) := by
    simp [e5, body22Env5, load22_product4Env, mlir_env]
  have h70 : runSlice (avx2Kernel.bb22 p) e5 70 4 (pipelineState s q true P C 4) =
      .value (e6, (pipelineState s q true P C 4)) := by
    exact abdc22_slice p e5 (pipelineState s q true P C 4)
  have f6 : RegisterFrame 583 587 e5 e6 :=
    abdc22_frame e5
  have r4_26 := (f4.read (%26) (by decide)).trans r3_26
  have r5_26 := (f5.read (%26) (by decide)).trans r4_26
  obtain ⟨v583, v584, v585, v586⟩ := abdc22_reads e5 (packPoint (productPoint true P C)) r5_26 (v579) (v580) (v581) (v582)
  have r5_362 := (f5.read (%362) (by decide)).trans r4_362
  have r6_362 := (f6.read (%362) (by decide)).trans r5_362
  have h74 : runSlice (avx2Kernel.bb22 p) e6 74 1 (pipelineState s q true P C 4) =
      .value (e7, (pipelineState s q true P C 4)) := by
    exact load22_product1_slice p e6 (pipelineState s q true P C 4) q.prepared (packPoint (productPoint true P C)) (pipelineState_live s q true P C (hmem.live 1) 4) (copied_read s q true P C (hmem.live 1) (hmem.live 2)) r6_362
  have f7 : RegisterFrame 587 588 e6 e7 :=
    load22_product1_frame e6 (packPoint (productPoint true P C))
  have v587 : e7.read (%587) = Ty.wrap (packPoint (productPoint true P C) 4) := by
    simp [e7, body22Env7, load22_product1Env, mlir_env]
  have h75 : runSlice (avx2Kernel.bb22 p) e7 75 21 (pipelineState s q true P C 4) =
      .value (e8, (pipelineState s q true P C 4)) := by
    exact difference22_slice p e7 (pipelineState s q true P C 4)
  have f8 : RegisterFrame 588 609 e7 e8 :=
    difference22_frame e7
  have r6_579 := (f6.read (%579) (by decide)).trans (v579)
  have r7_579 := (f7.read (%579) (by decide)).trans r6_579
  have r6_580 := (f6.read (%580) (by decide)).trans (v580)
  have r7_580 := (f7.read (%580) (by decide)).trans r6_580
  have r6_581 := (f6.read (%581) (by decide)).trans (v581)
  have r7_581 := (f7.read (%581) (by decide)).trans r6_581
  have r6_582 := (f6.read (%582) (by decide)).trans (v582)
  have r7_582 := (f7.read (%582) (by decide)).trans r6_582
  have r7_583 := (f7.read (%583) (by decide)).trans (v583)
  have r7_584 := (f7.read (%584) (by decide)).trans (v584)
  have r7_585 := (f7.read (%585) (by decide)).trans (v585)
  have r7_586 := (f7.read (%586) (by decide)).trans (v586)
  have r6_26 := (f6.read (%26) (by decide)).trans r5_26
  have r7_26 := (f7.read (%26) (by decide)).trans r6_26
  have r4_135 := (f4.read (%135) (by decide)).trans r3_135
  have r5_135 := (f5.read (%135) (by decide)).trans r4_135
  have r6_135 := (f6.read (%135) (by decide)).trans r5_135
  have r7_135 := (f7.read (%135) (by decide)).trans r6_135
  have r4_152 := (f4.read (%152) (by decide)).trans r3_152
  have r5_152 := (f5.read (%152) (by decide)).trans r4_152
  have r6_152 := (f6.read (%152) (by decide)).trans r5_152
  have r7_152 := (f7.read (%152) (by decide)).trans r6_152
  have r4_170 := (f4.read (%170) (by decide)).trans r3_170
  have r5_170 := (f5.read (%170) (by decide)).trans r4_170
  have r6_170 := (f6.read (%170) (by decide)).trans r5_170
  have r7_170 := (f7.read (%170) (by decide)).trans r6_170
  have r4_187 := (f4.read (%187) (by decide)).trans r3_187
  have r5_187 := (f5.read (%187) (by decide)).trans r4_187
  have r6_187 := (f6.read (%187) (by decide)).trans r5_187
  have r7_187 := (f7.read (%187) (by decide)).trans r6_187
  have r4_204 := (f4.read (%204) (by decide)).trans r3_204
  have r5_204 := (f5.read (%204) (by decide)).trans r4_204
  have r6_204 := (f6.read (%204) (by decide)).trans r5_204
  have r7_204 := (f7.read (%204) (by decide)).trans r6_204
  have r4_221 := (f4.read (%221) (by decide)).trans r3_221
  have r5_221 := (f5.read (%221) (by decide)).trans r4_221
  have r6_221 := (f6.read (%221) (by decide)).trans r5_221
  have r7_221 := (f7.read (%221) (by decide)).trans r6_221
  have cdifference22 : Constants e7 := ⟨r7_26, r7_135, r7_152, r7_170, r7_187, r7_204, r7_221⟩
  have idifference22 : difference22Inputs e7 (packPoint (productPoint true P C)) := ⟨r7_579, r7_580, r7_581, r7_582, (v587), r7_583, r7_584, r7_585, r7_586⟩
  have v604 := difference22_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference22 idifference22 0
  have v605 := difference22_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference22 idifference22 1
  have v606 := difference22_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference22 idifference22 2
  have v607 := difference22_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference22 idifference22 3
  have v608 := difference22_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference22 idifference22 4
  have h96 : runSlice (avx2Kernel.bb22 p) e8 96 1 (pipelineState s q true P C 4) =
      .value (e8, (pipelineState s q true P C 4)) := by
    exact lifetime22_96_slice p e8 (pipelineState s q true P C 4)
  have h97 : runSlice (avx2Kernel.bb22 p) e8 97 5 (pipelineState s q true P C 4) =
      .value (e9, (pipelineState s q true P C 4)) := by
    exact adda22_slice p e8 (pipelineState s q true P C 4)
  have f9 : RegisterFrame 609 614 e8 e9 :=
    adda22_frame e8
  have r8_26 := (f8.read (%26) (by decide)).trans r7_26
  have r8_135 := (f8.read (%135) (by decide)).trans r7_135
  have r8_152 := (f8.read (%152) (by decide)).trans r7_152
  have r8_170 := (f8.read (%170) (by decide)).trans r7_170
  have r8_187 := (f8.read (%187) (by decide)).trans r7_187
  have r8_204 := (f8.read (%204) (by decide)).trans r7_204
  have r8_221 := (f8.read (%221) (by decide)).trans r7_221
  have cadda22 : Constants e8 := ⟨r8_26, r8_135, r8_152, r8_170, r8_187, r8_204, r8_221⟩
  have iadda22 : adda22Inputs e8 (packPoint (differencePoint true P C)) := ⟨(v604), (v605), (v606), (v607), (v608)⟩
  have v609 := adda22_field e8 (differencePoint true P C) cadda22 iadda22 0
  have v610 := adda22_field e8 (differencePoint true P C) cadda22 iadda22 1
  have v611 := adda22_field e8 (differencePoint true P C) cadda22 iadda22 2
  have v612 := adda22_field e8 (differencePoint true P C) cadda22 iadda22 3
  have v613 := adda22_field e8 (differencePoint true P C) cadda22 iadda22 4
  have r1_251 := (f1.read (%251) (by decide)).trans (hreg.r251)
  have r2_251 := (f2.read (%251) (by decide)).trans r1_251
  have r3_251 := (f3.read (%251) (by decide)).trans r2_251
  have r4_251 := (f4.read (%251) (by decide)).trans r3_251
  have r5_251 := (f5.read (%251) (by decide)).trans r4_251
  have r6_251 := (f6.read (%251) (by decide)).trans r5_251
  have r7_251 := (f7.read (%251) (by decide)).trans r6_251
  have r8_251 := (f8.read (%251) (by decide)).trans r7_251
  have r9_251 := (f9.read (%251) (by decide)).trans r8_251
  have r1_363 := (f1.read (%363) (by decide)).trans (hreg.r363)
  have r2_363 := (f2.read (%363) (by decide)).trans r1_363
  have r3_363 := (f3.read (%363) (by decide)).trans r2_363
  have r4_363 := (f4.read (%363) (by decide)).trans r3_363
  have r5_363 := (f5.read (%363) (by decide)).trans r4_363
  have r6_363 := (f6.read (%363) (by decide)).trans r5_363
  have r7_363 := (f7.read (%363) (by decide)).trans r6_363
  have r8_363 := (f8.read (%363) (by decide)).trans r7_363
  have r9_363 := (f9.read (%363) (by decide)).trans r8_363
  have r1_364 := (f1.read (%364) (by decide)).trans (hreg.r364)
  have r2_364 := (f2.read (%364) (by decide)).trans r1_364
  have r3_364 := (f3.read (%364) (by decide)).trans r2_364
  have r4_364 := (f4.read (%364) (by decide)).trans r3_364
  have r5_364 := (f5.read (%364) (by decide)).trans r4_364
  have r6_364 := (f6.read (%364) (by decide)).trans r5_364
  have r7_364 := (f7.read (%364) (by decide)).trans r6_364
  have r8_364 := (f8.read (%364) (by decide)).trans r7_364
  have r9_364 := (f9.read (%364) (by decide)).trans r8_364
  have r1_365 := (f1.read (%365) (by decide)).trans (hreg.r365)
  have r2_365 := (f2.read (%365) (by decide)).trans r1_365
  have r3_365 := (f3.read (%365) (by decide)).trans r2_365
  have r4_365 := (f4.read (%365) (by decide)).trans r3_365
  have r5_365 := (f5.read (%365) (by decide)).trans r4_365
  have r6_365 := (f6.read (%365) (by decide)).trans r5_365
  have r7_365 := (f7.read (%365) (by decide)).trans r6_365
  have r8_365 := (f8.read (%365) (by decide)).trans r7_365
  have r9_365 := (f9.read (%365) (by decide)).trans r8_365
  have r1_366 := (f1.read (%366) (by decide)).trans (hreg.r366)
  have r2_366 := (f2.read (%366) (by decide)).trans r1_366
  have r3_366 := (f3.read (%366) (by decide)).trans r2_366
  have r4_366 := (f4.read (%366) (by decide)).trans r3_366
  have r5_366 := (f5.read (%366) (by decide)).trans r4_366
  have r6_366 := (f6.read (%366) (by decide)).trans r5_366
  have r7_366 := (f7.read (%366) (by decide)).trans r6_366
  have r8_366 := (f8.read (%366) (by decide)).trans r7_366
  have r9_366 := (f9.read (%366) (by decide)).trans r8_366
  have h102 : runSlice (avx2Kernel.bb22 p) e9 102 5 (pipelineState s q true P C 4) =
      .value (e9, (pipelineState s q true P C 5)) := by
    exact adda22_store_slice p e9 (pipelineState s q true P C 4) q.left (packPoint (leftPoint true P C)) (pipelineState_live s q true P C (hmem.live 3) 4) r9_251 (v609) r9_363 (v610) r9_364 (v611) r9_365 (v612) r9_366 (v613)
  have h107 : runSlice (avx2Kernel.bb22 p) e9 107 1 (pipelineState s q true P C 5) =
      .value (e9, (pipelineState s q true P C 5)) := by
    exact lifetime22_107_slice p e9 (pipelineState s q true P C 5)
  have h108 : runSlice (avx2Kernel.bb22 p) e9 108 5 (pipelineState s q true P C 5) =
      .value (e10, (pipelineState s q true P C 5)) := by
    exact cbcb22_slice p e9 (pipelineState s q true P C 5)
  have f10 : RegisterFrame 614 619 e9 e10 :=
    cbcb22_frame e9
  have r9_604 := (f9.read (%604) (by decide)).trans (v604)
  have r9_605 := (f9.read (%605) (by decide)).trans (v605)
  have r9_606 := (f9.read (%606) (by decide)).trans (v606)
  have r9_607 := (f9.read (%607) (by decide)).trans (v607)
  have r9_608 := (f9.read (%608) (by decide)).trans (v608)
  have r9_26 := (f9.read (%26) (by decide)).trans r8_26
  have r9_135 := (f9.read (%135) (by decide)).trans r8_135
  have r9_152 := (f9.read (%152) (by decide)).trans r8_152
  have r9_170 := (f9.read (%170) (by decide)).trans r8_170
  have r9_187 := (f9.read (%187) (by decide)).trans r8_187
  have r9_204 := (f9.read (%204) (by decide)).trans r8_204
  have r9_221 := (f9.read (%221) (by decide)).trans r8_221
  have ccbcb22 : Constants e9 := ⟨r9_26, r9_135, r9_152, r9_170, r9_187, r9_204, r9_221⟩
  have icbcb22 : cbcb22Inputs e9 (packPoint (differencePoint true P C)) := ⟨r9_604, r9_605, r9_606, r9_607, r9_608⟩
  have v614 := cbcb22_field e9 (differencePoint true P C) ccbcb22 icbcb22 0
  have v615 := cbcb22_field e9 (differencePoint true P C) ccbcb22 icbcb22 1
  have v616 := cbcb22_field e9 (differencePoint true P C) ccbcb22 icbcb22 2
  have v617 := cbcb22_field e9 (differencePoint true P C) ccbcb22 icbcb22 3
  have v618 := cbcb22_field e9 (differencePoint true P C) ccbcb22 icbcb22 4
  have r1_250 := (f1.read (%250) (by decide)).trans (hreg.r250)
  have r2_250 := (f2.read (%250) (by decide)).trans r1_250
  have r3_250 := (f3.read (%250) (by decide)).trans r2_250
  have r4_250 := (f4.read (%250) (by decide)).trans r3_250
  have r5_250 := (f5.read (%250) (by decide)).trans r4_250
  have r6_250 := (f6.read (%250) (by decide)).trans r5_250
  have r7_250 := (f7.read (%250) (by decide)).trans r6_250
  have r8_250 := (f8.read (%250) (by decide)).trans r7_250
  have r9_250 := (f9.read (%250) (by decide)).trans r8_250
  have r10_250 := (f10.read (%250) (by decide)).trans r9_250
  have r1_367 := (f1.read (%367) (by decide)).trans (hreg.r367)
  have r2_367 := (f2.read (%367) (by decide)).trans r1_367
  have r3_367 := (f3.read (%367) (by decide)).trans r2_367
  have r4_367 := (f4.read (%367) (by decide)).trans r3_367
  have r5_367 := (f5.read (%367) (by decide)).trans r4_367
  have r6_367 := (f6.read (%367) (by decide)).trans r5_367
  have r7_367 := (f7.read (%367) (by decide)).trans r6_367
  have r8_367 := (f8.read (%367) (by decide)).trans r7_367
  have r9_367 := (f9.read (%367) (by decide)).trans r8_367
  have r10_367 := (f10.read (%367) (by decide)).trans r9_367
  have r1_368 := (f1.read (%368) (by decide)).trans (hreg.r368)
  have r2_368 := (f2.read (%368) (by decide)).trans r1_368
  have r3_368 := (f3.read (%368) (by decide)).trans r2_368
  have r4_368 := (f4.read (%368) (by decide)).trans r3_368
  have r5_368 := (f5.read (%368) (by decide)).trans r4_368
  have r6_368 := (f6.read (%368) (by decide)).trans r5_368
  have r7_368 := (f7.read (%368) (by decide)).trans r6_368
  have r8_368 := (f8.read (%368) (by decide)).trans r7_368
  have r9_368 := (f9.read (%368) (by decide)).trans r8_368
  have r10_368 := (f10.read (%368) (by decide)).trans r9_368
  have r1_369 := (f1.read (%369) (by decide)).trans (hreg.r369)
  have r2_369 := (f2.read (%369) (by decide)).trans r1_369
  have r3_369 := (f3.read (%369) (by decide)).trans r2_369
  have r4_369 := (f4.read (%369) (by decide)).trans r3_369
  have r5_369 := (f5.read (%369) (by decide)).trans r4_369
  have r6_369 := (f6.read (%369) (by decide)).trans r5_369
  have r7_369 := (f7.read (%369) (by decide)).trans r6_369
  have r8_369 := (f8.read (%369) (by decide)).trans r7_369
  have r9_369 := (f9.read (%369) (by decide)).trans r8_369
  have r10_369 := (f10.read (%369) (by decide)).trans r9_369
  have r1_370 := (f1.read (%370) (by decide)).trans (hreg.r370)
  have r2_370 := (f2.read (%370) (by decide)).trans r1_370
  have r3_370 := (f3.read (%370) (by decide)).trans r2_370
  have r4_370 := (f4.read (%370) (by decide)).trans r3_370
  have r5_370 := (f5.read (%370) (by decide)).trans r4_370
  have r6_370 := (f6.read (%370) (by decide)).trans r5_370
  have r7_370 := (f7.read (%370) (by decide)).trans r6_370
  have r8_370 := (f8.read (%370) (by decide)).trans r7_370
  have r9_370 := (f9.read (%370) (by decide)).trans r8_370
  have r10_370 := (f10.read (%370) (by decide)).trans r9_370
  have h113 : runSlice (avx2Kernel.bb22 p) e10 113 5 (pipelineState s q true P C 5) =
      .value (e10, (pipelineState s q true P C 6)) := by
    exact cbcb22_store_slice p e10 (pipelineState s q true P C 5) q.right (packPoint (rightPoint true P C)) (pipelineState_live s q true P C (hmem.live 4) 5) r10_250 (v614) r10_367 (v615) r10_368 (v616) r10_369 (v617) r10_370 (v618)
  have r1_261 := (f1.read (%261) (by decide)).trans (hreg.r261)
  have r2_261 := (f2.read (%261) (by decide)).trans r1_261
  have r3_261 := (f3.read (%261) (by decide)).trans r2_261
  have r4_261 := (f4.read (%261) (by decide)).trans r3_261
  have r5_261 := (f5.read (%261) (by decide)).trans r4_261
  have r6_261 := (f6.read (%261) (by decide)).trans r5_261
  have r7_261 := (f7.read (%261) (by decide)).trans r6_261
  have r8_261 := (f8.read (%261) (by decide)).trans r7_261
  have r9_261 := (f9.read (%261) (by decide)).trans r8_261
  have r10_261 := (f10.read (%261) (by decide)).trans r9_261
  have r10_251 := (f10.read (%251) (by decide)).trans r9_251
  have h118 : runSlice (avx2Kernel.bb22 p) e10 118 1 (pipelineState s q true P C 6) =
      .value (e10, (pipelineState s q true P C 7)) := by
    exact multiply22_1_slice p e10 (pipelineState s q true P C 6) q.output q.left q.right (leftPoint true P C) (rightPoint true P C) hmul (pipelineState_wf s q true P C hmem.wf 6) (pipelineState_live s q true P C (hmem.live 0) 6) (pipelineState_live s q true P C (hmem.live 3) 6) (pipelineState_live s q true P C (hmem.live 4) 6) (leftPoint_wide true hP hC) (rightPoint_wide true hP hC) (factors_read s q true (tableRow table index) P C hmem).1 (factors_read s q true (tableRow table index) P C hmem).2 r10_261 r10_251 r10_250
  have h119 : runSlice (avx2Kernel.bb22 p) e10 119 4 (pipelineState s q true P C 7) =
      .value (e10, (pipelineState s q true P C 7)) := by
    exact lifetime22_119_slice p e10 (pipelineState s q true P C 7)
  have r1_371 := (f1.read (%371) (by decide)).trans (hreg.r371)
  have r2_371 := (f2.read (%371) (by decide)).trans r1_371
  have r3_371 := (f3.read (%371) (by decide)).trans r2_371
  have r4_371 := (f4.read (%371) (by decide)).trans r3_371
  have r5_371 := (f5.read (%371) (by decide)).trans r4_371
  have r6_371 := (f6.read (%371) (by decide)).trans r5_371
  have r7_371 := (f7.read (%371) (by decide)).trans r6_371
  have r8_371 := (f8.read (%371) (by decide)).trans r7_371
  have r9_371 := (f9.read (%371) (by decide)).trans r8_371
  have r10_371 := (f10.read (%371) (by decide)).trans r9_371
  have r1_372 := (f1.read (%372) (by decide)).trans (hreg.r372)
  have r2_372 := (f2.read (%372) (by decide)).trans r1_372
  have r3_372 := (f3.read (%372) (by decide)).trans r2_372
  have r4_372 := (f4.read (%372) (by decide)).trans r3_372
  have r5_372 := (f5.read (%372) (by decide)).trans r4_372
  have r6_372 := (f6.read (%372) (by decide)).trans r5_372
  have r7_372 := (f7.read (%372) (by decide)).trans r6_372
  have r8_372 := (f8.read (%372) (by decide)).trans r7_372
  have r9_372 := (f9.read (%372) (by decide)).trans r8_372
  have r10_372 := (f10.read (%372) (by decide)).trans r9_372
  have r1_373 := (f1.read (%373) (by decide)).trans (hreg.r373)
  have r2_373 := (f2.read (%373) (by decide)).trans r1_373
  have r3_373 := (f3.read (%373) (by decide)).trans r2_373
  have r4_373 := (f4.read (%373) (by decide)).trans r3_373
  have r5_373 := (f5.read (%373) (by decide)).trans r4_373
  have r6_373 := (f6.read (%373) (by decide)).trans r5_373
  have r7_373 := (f7.read (%373) (by decide)).trans r6_373
  have r8_373 := (f8.read (%373) (by decide)).trans r7_373
  have r9_373 := (f9.read (%373) (by decide)).trans r8_373
  have r10_373 := (f10.read (%373) (by decide)).trans r9_373
  have r1_374 := (f1.read (%374) (by decide)).trans (hreg.r374)
  have r2_374 := (f2.read (%374) (by decide)).trans r1_374
  have r3_374 := (f3.read (%374) (by decide)).trans r2_374
  have r4_374 := (f4.read (%374) (by decide)).trans r3_374
  have r5_374 := (f5.read (%374) (by decide)).trans r4_374
  have r6_374 := (f6.read (%374) (by decide)).trans r5_374
  have r7_374 := (f7.read (%374) (by decide)).trans r6_374
  have r8_374 := (f8.read (%374) (by decide)).trans r7_374
  have r9_374 := (f9.read (%374) (by decide)).trans r8_374
  have r10_374 := (f10.read (%374) (by decide)).trans r9_374
  have h123 : runSlice (avx2Kernel.bb22 p) e10 123 5 (pipelineState s q true P C 7) =
      .value (e11, (pipelineState s q true P C 7)) := by
    exact load22_result_slice p e10 (pipelineState s q true P C 7) q.output (packPoint (resultPoint true P C)) (pipelineState_live s q true P C (hmem.live 0) 7) (result_read s q true P C (hmem.live 0)) r10_261 r10_371 r10_372 r10_373 r10_374
  have f11 : RegisterFrame 619 624 e10 e11 :=
    load22_result_frame e10 (packPoint (resultPoint true P C))
  have v619 : e11.read (%619) = Ty.wrap (packPoint (resultPoint true P C) 0) := by
    simp [e11, body22Env11, load22_resultEnv, mlir_env]
  have v620 : e11.read (%620) = Ty.wrap (packPoint (resultPoint true P C) 1) := by
    simp [e11, body22Env11, load22_resultEnv, mlir_env]
  have v621 : e11.read (%621) = Ty.wrap (packPoint (resultPoint true P C) 2) := by
    simp [e11, body22Env11, load22_resultEnv, mlir_env]
  have v622 : e11.read (%622) = Ty.wrap (packPoint (resultPoint true P C) 3) := by
    simp [e11, body22Env11, load22_resultEnv, mlir_env]
  have v623 : e11.read (%623) = Ty.wrap (packPoint (resultPoint true P C) 4) := by
    simp [e11, body22Env11, load22_resultEnv, mlir_env]
  have h128 : runSlice (avx2Kernel.bb22 p) e11 128 1 (pipelineState s q true P C 7) =
      .value (e11, (pipelineState s q true P C 7)) := by
    exact lifetime22_128_slice p e11 (pipelineState s q true P C 7)
  calc
    (avx2Kernel.bb22 p).runBodyFrom E 0 (pipelineState s q true P C 0) = (avx2Kernel.bb22 p).runBodyFrom e1 1 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h0
    _ = (avx2Kernel.bb22 p).runBodyFrom e2 10 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h1
    _ = (avx2Kernel.bb22 p).runBodyFrom e2 11 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h10
    _ = (avx2Kernel.bb22 p).runBodyFrom e3 26 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h11
    _ = (avx2Kernel.bb22 p).runBodyFrom e3 31 (pipelineState s q true P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h26
    _ = (avx2Kernel.bb22 p).runBodyFrom e3 32 (pipelineState s q true P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h31
    _ = (avx2Kernel.bb22 p).runBodyFrom e4 57 (pipelineState s q true P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h32
    _ = (avx2Kernel.bb22 p).runBodyFrom e4 62 (pipelineState s q true P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h57
    _ = (avx2Kernel.bb22 p).runBodyFrom e4 63 (pipelineState s q true P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h62
    _ = (avx2Kernel.bb22 p).runBodyFrom e4 64 (pipelineState s q true P C 3) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h63
    _ = (avx2Kernel.bb22 p).runBodyFrom e4 65 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h64
    _ = (avx2Kernel.bb22 p).runBodyFrom e4 66 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h65
    _ = (avx2Kernel.bb22 p).runBodyFrom e5 70 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h66
    _ = (avx2Kernel.bb22 p).runBodyFrom e6 74 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h70
    _ = (avx2Kernel.bb22 p).runBodyFrom e7 75 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h74
    _ = (avx2Kernel.bb22 p).runBodyFrom e8 96 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h75
    _ = (avx2Kernel.bb22 p).runBodyFrom e8 97 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h96
    _ = (avx2Kernel.bb22 p).runBodyFrom e9 102 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h97
    _ = (avx2Kernel.bb22 p).runBodyFrom e9 107 (pipelineState s q true P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h102
    _ = (avx2Kernel.bb22 p).runBodyFrom e9 108 (pipelineState s q true P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h107
    _ = (avx2Kernel.bb22 p).runBodyFrom e10 113 (pipelineState s q true P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h108
    _ = (avx2Kernel.bb22 p).runBodyFrom e10 118 (pipelineState s q true P C 6) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h113
    _ = (avx2Kernel.bb22 p).runBodyFrom e10 119 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h118
    _ = (avx2Kernel.bb22 p).runBodyFrom e10 123 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h119
    _ = (avx2Kernel.bb22 p).runBodyFrom e11 128 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h123
    _ = (avx2Kernel.bb22 p).runBodyFrom e11 129 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h128
    _ = .value (e11, (pipelineState s q true P C 7)) := by
      rw [BasicBlock.runBodyFrom_done (hpos := by simp [avx2Kernel.bb22])]
      rfl

def exit22Env (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  (body22Env11 E q table index P C)[%698 := Ty.wrap (packPoint (resultPoint true P C) 3), %699 := Ty.wrap (packPoint (resultPoint true P C) 2), %700 := Ty.wrap (packPoint (resultPoint true P C) 1), %701 := Ty.wrap (packPoint (resultPoint true P C) 0), %702 := Ty.wrap (packPoint (resultPoint true P C) 4)]

theorem exit22_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (exit22Env E q table index P C) := by
  unfold exit22Env
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  exact body22_frame E q table index P C

theorem exit22_point (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (exit22Env E q table index P C).read (%698) = Ty.wrap (packPoint (resultPoint true P C) 3) ∧ (exit22Env E q table index P C).read (%699) = Ty.wrap (packPoint (resultPoint true P C) 2) ∧ (exit22Env E q table index P C).read (%700) = Ty.wrap (packPoint (resultPoint true P C) 1) ∧ (exit22Env E q table index P C).read (%701) = Ty.wrap (packPoint (resultPoint true P C) 0) ∧ (exit22Env E q table index P C).read (%702) = Ty.wrap (packPoint (resultPoint true P C) 4) := by
  simp [exit22Env, mlir_env]

theorem block22_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input22 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb22 p).run avx2Kernel.blockParams E s =
      .value ((exit22Env E q table index P C, .inr 26), pipelineState s q true P C 7) := by
  have hb := body22_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC
  obtain ⟨v0, v1, v2, v3, v4⟩ := body22_output E q table index P C
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp [avx2Kernel.bb22, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, DoubleBase.ExecutionAvx2.kernel_params26,
    exit22Env, v0, v1, v2, v3, v4, EffectM.pure_eq]

theorem block22_run (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input22 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) (g : Avx2CFG.Globals) :
    (avx2Kernel p g).runFrom E 22 s =
      (avx2Kernel p g).runFrom (exit22Env E q table index P C) 26 (pipelineState s q true P C 7) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 22 = avx2Kernel.bb22 p from rfl,
    block22_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC]
  simp only [PoisonOr.value_bind, Func.continue]

theorem block22_memoryFrame (s : GlobalState) (q : Scratch) (P C : Point) (hs : s.WF) :
    OutputFrame q s (pipelineState s q true P C 7) := pipelineState_frame s q true P C hs 7

theorem block22_reduced {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointReduced (resultPoint true P C) := resultPoint_reduced true hP hC

theorem block22_field {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (resultPoint true P C) = PointArithmetic.avx2AddCached (pointValue P)
      (PointArithmetic.negateCache (pointValue C)) := by
  simpa [resultPoint_eq] using sub_refines hP hC

/-- Field readback from the actual final output-memory state. -/
theorem block22_memoryPoint (s : GlobalState) (q : Scratch) (P C : Point)
    (hr : Reduce64.Execution.SmallRange s.mem q.output 160)
    (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q true P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (PointArithmetic.negateCache (pointValue C)) := by
  rw [readPoint_of_packed (pointReduced_wide (block22_reduced hP hC)) _ _
    (result_read s q true P C hr)]
  exact block22_field hP hC

/-- One local ladder transition: exact successor, concrete packed output,
preserved static registers/cursor, allocation and byte frame, restored bounds,
and field correctness. It assumes no enclosing iteration or ladder theorem. -/
theorem block22_endpoint (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input22 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb22 p).run avx2Kernel.blockParams E s =
      .value ((exit22Env E q table index P C, .inr 26), pipelineState s q true P C 7) ∧
    OutputFrame q s (pipelineState s q true P C 7) ∧
    RegisterFrame 427 avx2Kernel.Γ.n E (exit22Env E q table index P C) ∧
    Avx2FieldMul.Execution.readBlocks (pipelineState s q true P C 7).mem q.output = packPoint (resultPoint true P C) ∧
    pointReduced (resultPoint true P C) ∧
    (exit22Env E q table index P C).read (%698) = Ty.wrap (packPoint (resultPoint true P C) 3) ∧ (exit22Env E q table index P C).read (%699) = Ty.wrap (packPoint (resultPoint true P C) 2) ∧ (exit22Env E q table index P C).read (%700) = Ty.wrap (packPoint (resultPoint true P C) 1) ∧ (exit22Env E q table index P C).read (%701) = Ty.wrap (packPoint (resultPoint true P C) 0) ∧ (exit22Env E q table index P C).read (%702) = Ty.wrap (packPoint (resultPoint true P C) 4) ∧
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q true P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (PointArithmetic.negateCache (pointValue C)) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := exit22_point E q table index P C
  exact ⟨block22_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC,
    block22_memoryFrame s q P C hmem.wf, exit22_frame E q table index P C,
    result_read s q true P C (hmem.live 0), block22_reduced hP hC,
    v0, v1, v2, v3, v4, block22_memoryPoint s q P C (hmem.live 0) hP hC⟩

end Agave.Ed25519.Avx2PointAdd.CFG
