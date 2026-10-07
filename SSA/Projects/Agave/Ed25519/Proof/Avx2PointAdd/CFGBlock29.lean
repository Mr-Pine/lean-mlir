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

structure Input29 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P : Point) : Prop where
  constants : Constants E
  r3 : E.read (%3) = .value 32#64
  r20 : E.read (%20) = .value 64#64
  r21 : E.read (%21) = .value 96#64
  r22 : E.read (%22) = .value 128#64
  r153 : E.read (%153) = .value 160#64
  r224 : E.read (%224) = .value table
  r241 : E.read (%241) = .value q.right
  r242 : E.read (%242) = .value q.left
  r243 : E.read (%243) = .value q.product
  r244 : E.read (%244) = .value q.prepared
  r245 : E.read (%245) = .value q.negative
  r259 : E.read (%259) = .value q.output
  r391 : E.read (%391) = .value (q.negative.add 32#64)
  r392 : E.read (%392) = .value (q.negative.add 64#64)
  r393 : E.read (%393) = .value (q.negative.add 96#64)
  r394 : E.read (%394) = .value (q.negative.add 128#64)
  r395 : E.read (%395) = .value (q.prepared.add 32#64)
  r396 : E.read (%396) = .value (q.prepared.add 64#64)
  r397 : E.read (%397) = .value (q.prepared.add 96#64)
  r398 : E.read (%398) = .value (q.prepared.add 128#64)
  r399 : E.read (%399) = .value (q.left.add 32#64)
  r400 : E.read (%400) = .value (q.left.add 64#64)
  r401 : E.read (%401) = .value (q.left.add 96#64)
  r402 : E.read (%402) = .value (q.left.add 128#64)
  r403 : E.read (%403) = .value (q.right.add 32#64)
  r404 : E.read (%404) = .value (q.right.add 64#64)
  r405 : E.read (%405) = .value (q.right.add 96#64)
  r406 : E.read (%406) = .value (q.right.add 128#64)
  r407 : E.read (%407) = .value (q.output.add 32#64)
  r408 : E.read (%408) = .value (q.output.add 64#64)
  r409 : E.read (%409) = .value (q.output.add 96#64)
  r410 : E.read (%410) = .value (q.output.add 128#64)
  r698 : E.read (%698) = Ty.wrap (packPoint P 3)
  r699 : E.read (%699) = Ty.wrap (packPoint P 2)
  r700 : E.read (%700) = Ty.wrap (packPoint P 1)
  r701 : E.read (%701) = Ty.wrap (packPoint P 0)
  r702 : E.read (%702) = Ty.wrap (packPoint P 4)
  r708 : E.read (%708) = .value (BitVec.ofNat 64 index.val)

def body29Env1 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  row29Env (E) table index

def body29Env2 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  cached29Env (body29Env1 E q table index P C) (tableRow table index) (packPoint C)

def body29Env3 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  negate29Env (body29Env2 E q table index P C)

def body29Env4 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  prepare29Env (body29Env3 E q table index P C)

def body29Env5 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load29_product4Env (body29Env4 E q table index P C) (packPoint (productPoint true P C))

def body29Env6 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  abdc29Env (body29Env5 E q table index P C)

def body29Env7 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load29_product1Env (body29Env6 E q table index P C) (packPoint (productPoint true P C))

def body29Env8 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  difference29Env (body29Env7 E q table index P C)

def body29Env9 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  adda29Env (body29Env8 E q table index P C)

def body29Env10 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  cbcb29Env (body29Env9 E q table index P C)

def body29Env11 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load29_resultEnv (body29Env10 E q table index P C) (packPoint (resultPoint true P C))

theorem body29_output (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (body29Env11 E q table index P C).read (%800) = Ty.wrap (packPoint (resultPoint true P C) 0) ∧
    (body29Env11 E q table index P C).read (%801) = Ty.wrap (packPoint (resultPoint true P C) 1) ∧
    (body29Env11 E q table index P C).read (%802) = Ty.wrap (packPoint (resultPoint true P C) 2) ∧
    (body29Env11 E q table index P C).read (%803) = Ty.wrap (packPoint (resultPoint true P C) 3) ∧
    (body29Env11 E q table index P C).read (%804) = Ty.wrap (packPoint (resultPoint true P C) 4) := by
  exact load29_result_reads _ _

theorem body29_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (body29Env11 E q table index P C) := by
  have f1 := (row29_frame (E) table index).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f2 := (cached29_frame (body29Env1 E q table index P C) (tableRow table index) (packPoint C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f3 := (negate29_frame (body29Env2 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f4 := (prepare29_frame (body29Env3 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f5 := (load29_product4_frame (body29Env4 E q table index P C) (packPoint (productPoint true P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f6 := (abdc29_frame (body29Env5 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f7 := (load29_product1_frame (body29Env6 E q table index P C) (packPoint (productPoint true P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f8 := (difference29_frame (body29Env7 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f9 := (adda29_frame (body29Env8 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f10 := (cbcb29_frame (body29Env9 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f11 := (load29_result_frame (body29Env10 E q table index P C) (packPoint (resultPoint true P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  exact (((((((((((RegisterFrame.refl 427 avx2Kernel.Γ.n E).trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11

theorem body29_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input29 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb29 p).runBodyFrom E 0 s =
      .value (body29Env11 E q table index P C, pipelineState s q true P C 7) := by
  let e1 := body29Env1 E q table index P C
  let e2 := body29Env2 E q table index P C
  let e3 := body29Env3 E q table index P C
  let e4 := body29Env4 E q table index P C
  let e5 := body29Env5 E q table index P C
  let e6 := body29Env6 E q table index P C
  let e7 := body29Env7 E q table index P C
  let e8 := body29Env8 E q table index P C
  let e9 := body29Env9 E q table index P C
  let e10 := body29Env10 E q table index P C
  let e11 := body29Env11 E q table index P C
  have h0 : runSlice (avx2Kernel.bb29 p) E 0 1 (pipelineState s q true P C 0) =
      .value (e1, (pipelineState s q true P C 0)) := by
    exact row29_slice p E (pipelineState s q true P C 0) table index bytes htable hindex (hreg.r224) (hreg.r708)
  have f1 : RegisterFrame 710 711 E e1 :=
    row29_frame E table index
  have v710 : e1.read (%710) = .value (tableRow table index) := by
    simp [e1, body29Env1, row29Env, mlir_env]
  have r1_3 := (f1.read (%3) (by decide)).trans (hreg.r3)
  have r1_20 := (f1.read (%20) (by decide)).trans (hreg.r20)
  have r1_21 := (f1.read (%21) (by decide)).trans (hreg.r21)
  have r1_22 := (f1.read (%22) (by decide)).trans (hreg.r22)
  have h1 : runSlice (avx2Kernel.bb29 p) e1 1 9 (pipelineState s q true P C 0) =
      .value (e2, (pipelineState s q true P C 0)) := by
    exact cached29_slice p e1 (pipelineState s q true P C 0) (tableRow table index) (packPoint C) (hmem.live 6) hcache (v710) r1_3 r1_20 r1_21 r1_22
  have f2 : RegisterFrame 711 720 e1 e2 :=
    cached29_frame e1 (tableRow table index) (packPoint C)
  have v711 : e2.read (%711) = Ty.wrap (packPoint (C) 0) := by
    simp [e2, body29Env2, cached29Env, mlir_env]
  have v713 : e2.read (%713) = Ty.wrap (packPoint (C) 1) := by
    simp [e2, body29Env2, cached29Env, mlir_env]
  have v715 : e2.read (%715) = Ty.wrap (packPoint (C) 2) := by
    simp [e2, body29Env2, cached29Env, mlir_env]
  have v717 : e2.read (%717) = Ty.wrap (packPoint (C) 3) := by
    simp [e2, body29Env2, cached29Env, mlir_env]
  have v719 : e2.read (%719) = Ty.wrap (packPoint (C) 4) := by
    simp [e2, body29Env2, cached29Env, mlir_env]
  have h10 : runSlice (avx2Kernel.bb29 p) e2 10 1 (pipelineState s q true P C 0) =
      .value (e2, (pipelineState s q true P C 0)) := by
    exact lifetime29_10_slice p e2 (pipelineState s q true P C 0)
  have h11 : runSlice (avx2Kernel.bb29 p) e2 11 15 (pipelineState s q true P C 0) =
      .value (e3, (pipelineState s q true P C 0)) := by
    exact negate29_slice p e2 (pipelineState s q true P C 0)
  have f3 : RegisterFrame 720 735 e2 e3 :=
    negate29_frame e2
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
  have cnegate29 : Constants e2 := ⟨r2_26, r2_135, r2_152, r2_170, r2_187, r2_204, r2_221⟩
  have inegate29 : negate29Inputs e2 (packPoint C) := ⟨(v711), (v713), (v715), (v717), (v719)⟩
  have v730 := negate29_field e2 C hC cnegate29 inegate29 0
  have v731 := negate29_field e2 C hC cnegate29 inegate29 1
  have v732 := negate29_field e2 C hC cnegate29 inegate29 2
  have v733 := negate29_field e2 C hC cnegate29 inegate29 3
  have v734 := negate29_field e2 C hC cnegate29 inegate29 4
  have r1_245 := (f1.read (%245) (by decide)).trans (hreg.r245)
  have r2_245 := (f2.read (%245) (by decide)).trans r1_245
  have r3_245 := (f3.read (%245) (by decide)).trans r2_245
  have r1_391 := (f1.read (%391) (by decide)).trans (hreg.r391)
  have r2_391 := (f2.read (%391) (by decide)).trans r1_391
  have r3_391 := (f3.read (%391) (by decide)).trans r2_391
  have r1_392 := (f1.read (%392) (by decide)).trans (hreg.r392)
  have r2_392 := (f2.read (%392) (by decide)).trans r1_392
  have r3_392 := (f3.read (%392) (by decide)).trans r2_392
  have r1_393 := (f1.read (%393) (by decide)).trans (hreg.r393)
  have r2_393 := (f2.read (%393) (by decide)).trans r1_393
  have r3_393 := (f3.read (%393) (by decide)).trans r2_393
  have r1_394 := (f1.read (%394) (by decide)).trans (hreg.r394)
  have r2_394 := (f2.read (%394) (by decide)).trans r1_394
  have r3_394 := (f3.read (%394) (by decide)).trans r2_394
  have h26 : runSlice (avx2Kernel.bb29 p) e3 26 5 (pipelineState s q true P C 0) =
      .value (e3, (pipelineState s q true P C 1)) := by
    exact negate29_store_slice p e3 (pipelineState s q true P C 0) q.negative (packPoint (negate C)) (pipelineState_live s q true P C (hmem.live 5) 0) r3_245 (v730) r3_391 (v731) r3_392 (v732) r3_393 (v733) r3_394 (v734)
  have h31 : runSlice (avx2Kernel.bb29 p) e3 31 1 (pipelineState s q true P C 1) =
      .value (e3, (pipelineState s q true P C 1)) := by
    exact lifetime29_31_slice p e3 (pipelineState s q true P C 1)
  have h32 : runSlice (avx2Kernel.bb29 p) e3 32 25 (pipelineState s q true P C 1) =
      .value (e4, (pipelineState s q true P C 1)) := by
    exact prepare29_slice p e3 (pipelineState s q true P C 1)
  have f4 : RegisterFrame 735 760 e3 e4 :=
    prepare29_frame e3
  have r1_701 := (f1.read (%701) (by decide)).trans (hreg.r701)
  have r2_701 := (f2.read (%701) (by decide)).trans r1_701
  have r3_701 := (f3.read (%701) (by decide)).trans r2_701
  have r1_700 := (f1.read (%700) (by decide)).trans (hreg.r700)
  have r2_700 := (f2.read (%700) (by decide)).trans r1_700
  have r3_700 := (f3.read (%700) (by decide)).trans r2_700
  have r1_699 := (f1.read (%699) (by decide)).trans (hreg.r699)
  have r2_699 := (f2.read (%699) (by decide)).trans r1_699
  have r3_699 := (f3.read (%699) (by decide)).trans r2_699
  have r1_698 := (f1.read (%698) (by decide)).trans (hreg.r698)
  have r2_698 := (f2.read (%698) (by decide)).trans r1_698
  have r3_698 := (f3.read (%698) (by decide)).trans r2_698
  have r1_702 := (f1.read (%702) (by decide)).trans (hreg.r702)
  have r2_702 := (f2.read (%702) (by decide)).trans r1_702
  have r3_702 := (f3.read (%702) (by decide)).trans r2_702
  have r3_26 := (f3.read (%26) (by decide)).trans r2_26
  have r3_135 := (f3.read (%135) (by decide)).trans r2_135
  have r3_152 := (f3.read (%152) (by decide)).trans r2_152
  have r3_170 := (f3.read (%170) (by decide)).trans r2_170
  have r3_187 := (f3.read (%187) (by decide)).trans r2_187
  have r3_204 := (f3.read (%204) (by decide)).trans r2_204
  have r3_221 := (f3.read (%221) (by decide)).trans r2_221
  have cprepare29 : Constants e3 := ⟨r3_26, r3_135, r3_152, r3_170, r3_187, r3_204, r3_221⟩
  have iprepare29 : prepare29Inputs e3 (packPoint P) := ⟨r3_701, r3_700, r3_699, r3_698, r3_702⟩
  have v755 := prepare29_field e3 P hP cprepare29 iprepare29 0
  have v756 := prepare29_field e3 P hP cprepare29 iprepare29 1
  have v757 := prepare29_field e3 P hP cprepare29 iprepare29 2
  have v758 := prepare29_field e3 P hP cprepare29 iprepare29 3
  have v759 := prepare29_field e3 P hP cprepare29 iprepare29 4
  have r1_244 := (f1.read (%244) (by decide)).trans (hreg.r244)
  have r2_244 := (f2.read (%244) (by decide)).trans r1_244
  have r3_244 := (f3.read (%244) (by decide)).trans r2_244
  have r4_244 := (f4.read (%244) (by decide)).trans r3_244
  have r1_395 := (f1.read (%395) (by decide)).trans (hreg.r395)
  have r2_395 := (f2.read (%395) (by decide)).trans r1_395
  have r3_395 := (f3.read (%395) (by decide)).trans r2_395
  have r4_395 := (f4.read (%395) (by decide)).trans r3_395
  have r1_396 := (f1.read (%396) (by decide)).trans (hreg.r396)
  have r2_396 := (f2.read (%396) (by decide)).trans r1_396
  have r3_396 := (f3.read (%396) (by decide)).trans r2_396
  have r4_396 := (f4.read (%396) (by decide)).trans r3_396
  have r1_397 := (f1.read (%397) (by decide)).trans (hreg.r397)
  have r2_397 := (f2.read (%397) (by decide)).trans r1_397
  have r3_397 := (f3.read (%397) (by decide)).trans r2_397
  have r4_397 := (f4.read (%397) (by decide)).trans r3_397
  have r1_398 := (f1.read (%398) (by decide)).trans (hreg.r398)
  have r2_398 := (f2.read (%398) (by decide)).trans r1_398
  have r3_398 := (f3.read (%398) (by decide)).trans r2_398
  have r4_398 := (f4.read (%398) (by decide)).trans r3_398
  have h57 : runSlice (avx2Kernel.bb29 p) e4 57 5 (pipelineState s q true P C 1) =
      .value (e4, (pipelineState s q true P C 2)) := by
    exact prepare29_store_slice p e4 (pipelineState s q true P C 1) q.prepared (packPoint (prepare P)) (pipelineState_live s q true P C (hmem.live 1) 1) r4_244 (v755) r4_395 (v756) r4_396 (v757) r4_397 (v758) r4_398 (v759)
  have h62 : runSlice (avx2Kernel.bb29 p) e4 62 1 (pipelineState s q true P C 2) =
      .value (e4, (pipelineState s q true P C 2)) := by
    exact lifetime29_62_slice p e4 (pipelineState s q true P C 2)
  have r1_243 := (f1.read (%243) (by decide)).trans (hreg.r243)
  have r2_243 := (f2.read (%243) (by decide)).trans r1_243
  have r3_243 := (f3.read (%243) (by decide)).trans r2_243
  have r4_243 := (f4.read (%243) (by decide)).trans r3_243
  have r4_245 := (f4.read (%245) (by decide)).trans r3_245
  have h63 : runSlice (avx2Kernel.bb29 p) e4 63 1 (pipelineState s q true P C 2) =
      .value (e4, (pipelineState s q true P C 3)) := by
    exact multiply29_0_slice p e4 (pipelineState s q true P C 2) q.product q.prepared (cachePointer true q (tableRow table index)) (prepare P) (chosenCache true C) hmul (pipelineState_wf s q true P C hmem.wf 2) (pipelineState_live s q true P C (hmem.live 2) 2) (pipelineState_live s q true P C (hmem.live 1) 2) (pipelineState_live s q true P C (hmem.live 5) 2) (prepare_wide hP) (chosenCache_wide true hC) (prepared_read s q true P C (hmem.live 1)) (cache_read s q true (tableRow table index) P C hmem hcache) r4_243 r4_244 r4_245
  have r1_153 := (f1.read (%153) (by decide)).trans (hreg.r153)
  have r2_153 := (f2.read (%153) (by decide)).trans r1_153
  have r3_153 := (f3.read (%153) (by decide)).trans r2_153
  have r4_153 := (f4.read (%153) (by decide)).trans r3_153
  have h64 : runSlice (avx2Kernel.bb29 p) e4 64 1 (pipelineState s q true P C 3) =
      .value (e4, (pipelineState s q true P C 4)) := by
    exact copy29_slice p e4 (pipelineState s q true P C 3) q.prepared q.product (pipelineState_live s q true P C (hmem.live 1) 3) (pipelineState_live s q true P C (hmem.live 2) 3) (Or.inl (hmem.ne 1 2 (by decide))) r4_244 r4_243 r4_153
  have h65 : runSlice (avx2Kernel.bb29 p) e4 65 1 (pipelineState s q true P C 4) =
      .value (e4, (pipelineState s q true P C 4)) := by
    exact lifetime29_65_slice p e4 (pipelineState s q true P C 4)
  have h66 : runSlice (avx2Kernel.bb29 p) e4 66 4 (pipelineState s q true P C 4) =
      .value (e5, (pipelineState s q true P C 4)) := by
    exact load29_product4_slice p e4 (pipelineState s q true P C 4) q.prepared (packPoint (productPoint true P C)) (pipelineState_live s q true P C (hmem.live 1) 4) (copied_read s q true P C (hmem.live 1) (hmem.live 2)) r4_244 r4_395 r4_396 r4_397
  have f5 : RegisterFrame 760 764 e4 e5 :=
    load29_product4_frame e4 (packPoint (productPoint true P C))
  have v760 : e5.read (%760) = Ty.wrap (packPoint (productPoint true P C) 0) := by
    simp [e5, body29Env5, load29_product4Env, mlir_env]
  have v761 : e5.read (%761) = Ty.wrap (packPoint (productPoint true P C) 1) := by
    simp [e5, body29Env5, load29_product4Env, mlir_env]
  have v762 : e5.read (%762) = Ty.wrap (packPoint (productPoint true P C) 2) := by
    simp [e5, body29Env5, load29_product4Env, mlir_env]
  have v763 : e5.read (%763) = Ty.wrap (packPoint (productPoint true P C) 3) := by
    simp [e5, body29Env5, load29_product4Env, mlir_env]
  have h70 : runSlice (avx2Kernel.bb29 p) e5 70 4 (pipelineState s q true P C 4) =
      .value (e6, (pipelineState s q true P C 4)) := by
    exact abdc29_slice p e5 (pipelineState s q true P C 4)
  have f6 : RegisterFrame 764 768 e5 e6 :=
    abdc29_frame e5
  have r4_26 := (f4.read (%26) (by decide)).trans r3_26
  have r5_26 := (f5.read (%26) (by decide)).trans r4_26
  obtain ⟨v764, v765, v766, v767⟩ := abdc29_reads e5 (packPoint (productPoint true P C)) r5_26 (v760) (v761) (v762) (v763)
  have r5_398 := (f5.read (%398) (by decide)).trans r4_398
  have r6_398 := (f6.read (%398) (by decide)).trans r5_398
  have h74 : runSlice (avx2Kernel.bb29 p) e6 74 1 (pipelineState s q true P C 4) =
      .value (e7, (pipelineState s q true P C 4)) := by
    exact load29_product1_slice p e6 (pipelineState s q true P C 4) q.prepared (packPoint (productPoint true P C)) (pipelineState_live s q true P C (hmem.live 1) 4) (copied_read s q true P C (hmem.live 1) (hmem.live 2)) r6_398
  have f7 : RegisterFrame 768 769 e6 e7 :=
    load29_product1_frame e6 (packPoint (productPoint true P C))
  have v768 : e7.read (%768) = Ty.wrap (packPoint (productPoint true P C) 4) := by
    simp [e7, body29Env7, load29_product1Env, mlir_env]
  have h75 : runSlice (avx2Kernel.bb29 p) e7 75 21 (pipelineState s q true P C 4) =
      .value (e8, (pipelineState s q true P C 4)) := by
    exact difference29_slice p e7 (pipelineState s q true P C 4)
  have f8 : RegisterFrame 769 790 e7 e8 :=
    difference29_frame e7
  have r6_760 := (f6.read (%760) (by decide)).trans (v760)
  have r7_760 := (f7.read (%760) (by decide)).trans r6_760
  have r6_761 := (f6.read (%761) (by decide)).trans (v761)
  have r7_761 := (f7.read (%761) (by decide)).trans r6_761
  have r6_762 := (f6.read (%762) (by decide)).trans (v762)
  have r7_762 := (f7.read (%762) (by decide)).trans r6_762
  have r6_763 := (f6.read (%763) (by decide)).trans (v763)
  have r7_763 := (f7.read (%763) (by decide)).trans r6_763
  have r7_764 := (f7.read (%764) (by decide)).trans (v764)
  have r7_765 := (f7.read (%765) (by decide)).trans (v765)
  have r7_766 := (f7.read (%766) (by decide)).trans (v766)
  have r7_767 := (f7.read (%767) (by decide)).trans (v767)
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
  have cdifference29 : Constants e7 := ⟨r7_26, r7_135, r7_152, r7_170, r7_187, r7_204, r7_221⟩
  have idifference29 : difference29Inputs e7 (packPoint (productPoint true P C)) := ⟨r7_760, r7_761, r7_762, r7_763, (v768), r7_764, r7_765, r7_766, r7_767⟩
  have v785 := difference29_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference29 idifference29 0
  have v786 := difference29_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference29 idifference29 1
  have v787 := difference29_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference29 idifference29 2
  have v788 := difference29_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference29 idifference29 3
  have v789 := difference29_field e7 (productPoint true P C) (productPoint_reduced true hP hC) cdifference29 idifference29 4
  have h96 : runSlice (avx2Kernel.bb29 p) e8 96 1 (pipelineState s q true P C 4) =
      .value (e8, (pipelineState s q true P C 4)) := by
    exact lifetime29_96_slice p e8 (pipelineState s q true P C 4)
  have h97 : runSlice (avx2Kernel.bb29 p) e8 97 5 (pipelineState s q true P C 4) =
      .value (e9, (pipelineState s q true P C 4)) := by
    exact adda29_slice p e8 (pipelineState s q true P C 4)
  have f9 : RegisterFrame 790 795 e8 e9 :=
    adda29_frame e8
  have r8_26 := (f8.read (%26) (by decide)).trans r7_26
  have r8_135 := (f8.read (%135) (by decide)).trans r7_135
  have r8_152 := (f8.read (%152) (by decide)).trans r7_152
  have r8_170 := (f8.read (%170) (by decide)).trans r7_170
  have r8_187 := (f8.read (%187) (by decide)).trans r7_187
  have r8_204 := (f8.read (%204) (by decide)).trans r7_204
  have r8_221 := (f8.read (%221) (by decide)).trans r7_221
  have cadda29 : Constants e8 := ⟨r8_26, r8_135, r8_152, r8_170, r8_187, r8_204, r8_221⟩
  have iadda29 : adda29Inputs e8 (packPoint (differencePoint true P C)) := ⟨(v785), (v786), (v787), (v788), (v789)⟩
  have v790 := adda29_field e8 (differencePoint true P C) cadda29 iadda29 0
  have v791 := adda29_field e8 (differencePoint true P C) cadda29 iadda29 1
  have v792 := adda29_field e8 (differencePoint true P C) cadda29 iadda29 2
  have v793 := adda29_field e8 (differencePoint true P C) cadda29 iadda29 3
  have v794 := adda29_field e8 (differencePoint true P C) cadda29 iadda29 4
  have r1_242 := (f1.read (%242) (by decide)).trans (hreg.r242)
  have r2_242 := (f2.read (%242) (by decide)).trans r1_242
  have r3_242 := (f3.read (%242) (by decide)).trans r2_242
  have r4_242 := (f4.read (%242) (by decide)).trans r3_242
  have r5_242 := (f5.read (%242) (by decide)).trans r4_242
  have r6_242 := (f6.read (%242) (by decide)).trans r5_242
  have r7_242 := (f7.read (%242) (by decide)).trans r6_242
  have r8_242 := (f8.read (%242) (by decide)).trans r7_242
  have r9_242 := (f9.read (%242) (by decide)).trans r8_242
  have r1_399 := (f1.read (%399) (by decide)).trans (hreg.r399)
  have r2_399 := (f2.read (%399) (by decide)).trans r1_399
  have r3_399 := (f3.read (%399) (by decide)).trans r2_399
  have r4_399 := (f4.read (%399) (by decide)).trans r3_399
  have r5_399 := (f5.read (%399) (by decide)).trans r4_399
  have r6_399 := (f6.read (%399) (by decide)).trans r5_399
  have r7_399 := (f7.read (%399) (by decide)).trans r6_399
  have r8_399 := (f8.read (%399) (by decide)).trans r7_399
  have r9_399 := (f9.read (%399) (by decide)).trans r8_399
  have r1_400 := (f1.read (%400) (by decide)).trans (hreg.r400)
  have r2_400 := (f2.read (%400) (by decide)).trans r1_400
  have r3_400 := (f3.read (%400) (by decide)).trans r2_400
  have r4_400 := (f4.read (%400) (by decide)).trans r3_400
  have r5_400 := (f5.read (%400) (by decide)).trans r4_400
  have r6_400 := (f6.read (%400) (by decide)).trans r5_400
  have r7_400 := (f7.read (%400) (by decide)).trans r6_400
  have r8_400 := (f8.read (%400) (by decide)).trans r7_400
  have r9_400 := (f9.read (%400) (by decide)).trans r8_400
  have r1_401 := (f1.read (%401) (by decide)).trans (hreg.r401)
  have r2_401 := (f2.read (%401) (by decide)).trans r1_401
  have r3_401 := (f3.read (%401) (by decide)).trans r2_401
  have r4_401 := (f4.read (%401) (by decide)).trans r3_401
  have r5_401 := (f5.read (%401) (by decide)).trans r4_401
  have r6_401 := (f6.read (%401) (by decide)).trans r5_401
  have r7_401 := (f7.read (%401) (by decide)).trans r6_401
  have r8_401 := (f8.read (%401) (by decide)).trans r7_401
  have r9_401 := (f9.read (%401) (by decide)).trans r8_401
  have r1_402 := (f1.read (%402) (by decide)).trans (hreg.r402)
  have r2_402 := (f2.read (%402) (by decide)).trans r1_402
  have r3_402 := (f3.read (%402) (by decide)).trans r2_402
  have r4_402 := (f4.read (%402) (by decide)).trans r3_402
  have r5_402 := (f5.read (%402) (by decide)).trans r4_402
  have r6_402 := (f6.read (%402) (by decide)).trans r5_402
  have r7_402 := (f7.read (%402) (by decide)).trans r6_402
  have r8_402 := (f8.read (%402) (by decide)).trans r7_402
  have r9_402 := (f9.read (%402) (by decide)).trans r8_402
  have h102 : runSlice (avx2Kernel.bb29 p) e9 102 5 (pipelineState s q true P C 4) =
      .value (e9, (pipelineState s q true P C 5)) := by
    exact adda29_store_slice p e9 (pipelineState s q true P C 4) q.left (packPoint (leftPoint true P C)) (pipelineState_live s q true P C (hmem.live 3) 4) r9_242 (v790) r9_399 (v791) r9_400 (v792) r9_401 (v793) r9_402 (v794)
  have h107 : runSlice (avx2Kernel.bb29 p) e9 107 1 (pipelineState s q true P C 5) =
      .value (e9, (pipelineState s q true P C 5)) := by
    exact lifetime29_107_slice p e9 (pipelineState s q true P C 5)
  have h108 : runSlice (avx2Kernel.bb29 p) e9 108 5 (pipelineState s q true P C 5) =
      .value (e10, (pipelineState s q true P C 5)) := by
    exact cbcb29_slice p e9 (pipelineState s q true P C 5)
  have f10 : RegisterFrame 795 800 e9 e10 :=
    cbcb29_frame e9
  have r9_785 := (f9.read (%785) (by decide)).trans (v785)
  have r9_786 := (f9.read (%786) (by decide)).trans (v786)
  have r9_787 := (f9.read (%787) (by decide)).trans (v787)
  have r9_788 := (f9.read (%788) (by decide)).trans (v788)
  have r9_789 := (f9.read (%789) (by decide)).trans (v789)
  have r9_26 := (f9.read (%26) (by decide)).trans r8_26
  have r9_135 := (f9.read (%135) (by decide)).trans r8_135
  have r9_152 := (f9.read (%152) (by decide)).trans r8_152
  have r9_170 := (f9.read (%170) (by decide)).trans r8_170
  have r9_187 := (f9.read (%187) (by decide)).trans r8_187
  have r9_204 := (f9.read (%204) (by decide)).trans r8_204
  have r9_221 := (f9.read (%221) (by decide)).trans r8_221
  have ccbcb29 : Constants e9 := ⟨r9_26, r9_135, r9_152, r9_170, r9_187, r9_204, r9_221⟩
  have icbcb29 : cbcb29Inputs e9 (packPoint (differencePoint true P C)) := ⟨r9_785, r9_786, r9_787, r9_788, r9_789⟩
  have v795 := cbcb29_field e9 (differencePoint true P C) ccbcb29 icbcb29 0
  have v796 := cbcb29_field e9 (differencePoint true P C) ccbcb29 icbcb29 1
  have v797 := cbcb29_field e9 (differencePoint true P C) ccbcb29 icbcb29 2
  have v798 := cbcb29_field e9 (differencePoint true P C) ccbcb29 icbcb29 3
  have v799 := cbcb29_field e9 (differencePoint true P C) ccbcb29 icbcb29 4
  have r1_241 := (f1.read (%241) (by decide)).trans (hreg.r241)
  have r2_241 := (f2.read (%241) (by decide)).trans r1_241
  have r3_241 := (f3.read (%241) (by decide)).trans r2_241
  have r4_241 := (f4.read (%241) (by decide)).trans r3_241
  have r5_241 := (f5.read (%241) (by decide)).trans r4_241
  have r6_241 := (f6.read (%241) (by decide)).trans r5_241
  have r7_241 := (f7.read (%241) (by decide)).trans r6_241
  have r8_241 := (f8.read (%241) (by decide)).trans r7_241
  have r9_241 := (f9.read (%241) (by decide)).trans r8_241
  have r10_241 := (f10.read (%241) (by decide)).trans r9_241
  have r1_403 := (f1.read (%403) (by decide)).trans (hreg.r403)
  have r2_403 := (f2.read (%403) (by decide)).trans r1_403
  have r3_403 := (f3.read (%403) (by decide)).trans r2_403
  have r4_403 := (f4.read (%403) (by decide)).trans r3_403
  have r5_403 := (f5.read (%403) (by decide)).trans r4_403
  have r6_403 := (f6.read (%403) (by decide)).trans r5_403
  have r7_403 := (f7.read (%403) (by decide)).trans r6_403
  have r8_403 := (f8.read (%403) (by decide)).trans r7_403
  have r9_403 := (f9.read (%403) (by decide)).trans r8_403
  have r10_403 := (f10.read (%403) (by decide)).trans r9_403
  have r1_404 := (f1.read (%404) (by decide)).trans (hreg.r404)
  have r2_404 := (f2.read (%404) (by decide)).trans r1_404
  have r3_404 := (f3.read (%404) (by decide)).trans r2_404
  have r4_404 := (f4.read (%404) (by decide)).trans r3_404
  have r5_404 := (f5.read (%404) (by decide)).trans r4_404
  have r6_404 := (f6.read (%404) (by decide)).trans r5_404
  have r7_404 := (f7.read (%404) (by decide)).trans r6_404
  have r8_404 := (f8.read (%404) (by decide)).trans r7_404
  have r9_404 := (f9.read (%404) (by decide)).trans r8_404
  have r10_404 := (f10.read (%404) (by decide)).trans r9_404
  have r1_405 := (f1.read (%405) (by decide)).trans (hreg.r405)
  have r2_405 := (f2.read (%405) (by decide)).trans r1_405
  have r3_405 := (f3.read (%405) (by decide)).trans r2_405
  have r4_405 := (f4.read (%405) (by decide)).trans r3_405
  have r5_405 := (f5.read (%405) (by decide)).trans r4_405
  have r6_405 := (f6.read (%405) (by decide)).trans r5_405
  have r7_405 := (f7.read (%405) (by decide)).trans r6_405
  have r8_405 := (f8.read (%405) (by decide)).trans r7_405
  have r9_405 := (f9.read (%405) (by decide)).trans r8_405
  have r10_405 := (f10.read (%405) (by decide)).trans r9_405
  have r1_406 := (f1.read (%406) (by decide)).trans (hreg.r406)
  have r2_406 := (f2.read (%406) (by decide)).trans r1_406
  have r3_406 := (f3.read (%406) (by decide)).trans r2_406
  have r4_406 := (f4.read (%406) (by decide)).trans r3_406
  have r5_406 := (f5.read (%406) (by decide)).trans r4_406
  have r6_406 := (f6.read (%406) (by decide)).trans r5_406
  have r7_406 := (f7.read (%406) (by decide)).trans r6_406
  have r8_406 := (f8.read (%406) (by decide)).trans r7_406
  have r9_406 := (f9.read (%406) (by decide)).trans r8_406
  have r10_406 := (f10.read (%406) (by decide)).trans r9_406
  have h113 : runSlice (avx2Kernel.bb29 p) e10 113 5 (pipelineState s q true P C 5) =
      .value (e10, (pipelineState s q true P C 6)) := by
    exact cbcb29_store_slice p e10 (pipelineState s q true P C 5) q.right (packPoint (rightPoint true P C)) (pipelineState_live s q true P C (hmem.live 4) 5) r10_241 (v795) r10_403 (v796) r10_404 (v797) r10_405 (v798) r10_406 (v799)
  have r1_259 := (f1.read (%259) (by decide)).trans (hreg.r259)
  have r2_259 := (f2.read (%259) (by decide)).trans r1_259
  have r3_259 := (f3.read (%259) (by decide)).trans r2_259
  have r4_259 := (f4.read (%259) (by decide)).trans r3_259
  have r5_259 := (f5.read (%259) (by decide)).trans r4_259
  have r6_259 := (f6.read (%259) (by decide)).trans r5_259
  have r7_259 := (f7.read (%259) (by decide)).trans r6_259
  have r8_259 := (f8.read (%259) (by decide)).trans r7_259
  have r9_259 := (f9.read (%259) (by decide)).trans r8_259
  have r10_259 := (f10.read (%259) (by decide)).trans r9_259
  have r10_242 := (f10.read (%242) (by decide)).trans r9_242
  have h118 : runSlice (avx2Kernel.bb29 p) e10 118 1 (pipelineState s q true P C 6) =
      .value (e10, (pipelineState s q true P C 7)) := by
    exact multiply29_1_slice p e10 (pipelineState s q true P C 6) q.output q.left q.right (leftPoint true P C) (rightPoint true P C) hmul (pipelineState_wf s q true P C hmem.wf 6) (pipelineState_live s q true P C (hmem.live 0) 6) (pipelineState_live s q true P C (hmem.live 3) 6) (pipelineState_live s q true P C (hmem.live 4) 6) (leftPoint_wide true hP hC) (rightPoint_wide true hP hC) (factors_read s q true (tableRow table index) P C hmem).1 (factors_read s q true (tableRow table index) P C hmem).2 r10_259 r10_242 r10_241
  have h119 : runSlice (avx2Kernel.bb29 p) e10 119 4 (pipelineState s q true P C 7) =
      .value (e10, (pipelineState s q true P C 7)) := by
    exact lifetime29_119_slice p e10 (pipelineState s q true P C 7)
  have r1_407 := (f1.read (%407) (by decide)).trans (hreg.r407)
  have r2_407 := (f2.read (%407) (by decide)).trans r1_407
  have r3_407 := (f3.read (%407) (by decide)).trans r2_407
  have r4_407 := (f4.read (%407) (by decide)).trans r3_407
  have r5_407 := (f5.read (%407) (by decide)).trans r4_407
  have r6_407 := (f6.read (%407) (by decide)).trans r5_407
  have r7_407 := (f7.read (%407) (by decide)).trans r6_407
  have r8_407 := (f8.read (%407) (by decide)).trans r7_407
  have r9_407 := (f9.read (%407) (by decide)).trans r8_407
  have r10_407 := (f10.read (%407) (by decide)).trans r9_407
  have r1_408 := (f1.read (%408) (by decide)).trans (hreg.r408)
  have r2_408 := (f2.read (%408) (by decide)).trans r1_408
  have r3_408 := (f3.read (%408) (by decide)).trans r2_408
  have r4_408 := (f4.read (%408) (by decide)).trans r3_408
  have r5_408 := (f5.read (%408) (by decide)).trans r4_408
  have r6_408 := (f6.read (%408) (by decide)).trans r5_408
  have r7_408 := (f7.read (%408) (by decide)).trans r6_408
  have r8_408 := (f8.read (%408) (by decide)).trans r7_408
  have r9_408 := (f9.read (%408) (by decide)).trans r8_408
  have r10_408 := (f10.read (%408) (by decide)).trans r9_408
  have r1_409 := (f1.read (%409) (by decide)).trans (hreg.r409)
  have r2_409 := (f2.read (%409) (by decide)).trans r1_409
  have r3_409 := (f3.read (%409) (by decide)).trans r2_409
  have r4_409 := (f4.read (%409) (by decide)).trans r3_409
  have r5_409 := (f5.read (%409) (by decide)).trans r4_409
  have r6_409 := (f6.read (%409) (by decide)).trans r5_409
  have r7_409 := (f7.read (%409) (by decide)).trans r6_409
  have r8_409 := (f8.read (%409) (by decide)).trans r7_409
  have r9_409 := (f9.read (%409) (by decide)).trans r8_409
  have r10_409 := (f10.read (%409) (by decide)).trans r9_409
  have r1_410 := (f1.read (%410) (by decide)).trans (hreg.r410)
  have r2_410 := (f2.read (%410) (by decide)).trans r1_410
  have r3_410 := (f3.read (%410) (by decide)).trans r2_410
  have r4_410 := (f4.read (%410) (by decide)).trans r3_410
  have r5_410 := (f5.read (%410) (by decide)).trans r4_410
  have r6_410 := (f6.read (%410) (by decide)).trans r5_410
  have r7_410 := (f7.read (%410) (by decide)).trans r6_410
  have r8_410 := (f8.read (%410) (by decide)).trans r7_410
  have r9_410 := (f9.read (%410) (by decide)).trans r8_410
  have r10_410 := (f10.read (%410) (by decide)).trans r9_410
  have h123 : runSlice (avx2Kernel.bb29 p) e10 123 5 (pipelineState s q true P C 7) =
      .value (e11, (pipelineState s q true P C 7)) := by
    exact load29_result_slice p e10 (pipelineState s q true P C 7) q.output (packPoint (resultPoint true P C)) (pipelineState_live s q true P C (hmem.live 0) 7) (result_read s q true P C (hmem.live 0)) r10_259 r10_407 r10_408 r10_409 r10_410
  have f11 : RegisterFrame 800 805 e10 e11 :=
    load29_result_frame e10 (packPoint (resultPoint true P C))
  have v800 : e11.read (%800) = Ty.wrap (packPoint (resultPoint true P C) 0) := by
    simp [e11, body29Env11, load29_resultEnv, mlir_env]
  have v801 : e11.read (%801) = Ty.wrap (packPoint (resultPoint true P C) 1) := by
    simp [e11, body29Env11, load29_resultEnv, mlir_env]
  have v802 : e11.read (%802) = Ty.wrap (packPoint (resultPoint true P C) 2) := by
    simp [e11, body29Env11, load29_resultEnv, mlir_env]
  have v803 : e11.read (%803) = Ty.wrap (packPoint (resultPoint true P C) 3) := by
    simp [e11, body29Env11, load29_resultEnv, mlir_env]
  have v804 : e11.read (%804) = Ty.wrap (packPoint (resultPoint true P C) 4) := by
    simp [e11, body29Env11, load29_resultEnv, mlir_env]
  have h128 : runSlice (avx2Kernel.bb29 p) e11 128 1 (pipelineState s q true P C 7) =
      .value (e11, (pipelineState s q true P C 7)) := by
    exact lifetime29_128_slice p e11 (pipelineState s q true P C 7)
  calc
    (avx2Kernel.bb29 p).runBodyFrom E 0 (pipelineState s q true P C 0) = (avx2Kernel.bb29 p).runBodyFrom e1 1 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h0
    _ = (avx2Kernel.bb29 p).runBodyFrom e2 10 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h1
    _ = (avx2Kernel.bb29 p).runBodyFrom e2 11 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h10
    _ = (avx2Kernel.bb29 p).runBodyFrom e3 26 (pipelineState s q true P C 0) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h11
    _ = (avx2Kernel.bb29 p).runBodyFrom e3 31 (pipelineState s q true P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h26
    _ = (avx2Kernel.bb29 p).runBodyFrom e3 32 (pipelineState s q true P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h31
    _ = (avx2Kernel.bb29 p).runBodyFrom e4 57 (pipelineState s q true P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h32
    _ = (avx2Kernel.bb29 p).runBodyFrom e4 62 (pipelineState s q true P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h57
    _ = (avx2Kernel.bb29 p).runBodyFrom e4 63 (pipelineState s q true P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h62
    _ = (avx2Kernel.bb29 p).runBodyFrom e4 64 (pipelineState s q true P C 3) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h63
    _ = (avx2Kernel.bb29 p).runBodyFrom e4 65 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h64
    _ = (avx2Kernel.bb29 p).runBodyFrom e4 66 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h65
    _ = (avx2Kernel.bb29 p).runBodyFrom e5 70 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h66
    _ = (avx2Kernel.bb29 p).runBodyFrom e6 74 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h70
    _ = (avx2Kernel.bb29 p).runBodyFrom e7 75 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h74
    _ = (avx2Kernel.bb29 p).runBodyFrom e8 96 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h75
    _ = (avx2Kernel.bb29 p).runBodyFrom e8 97 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h96
    _ = (avx2Kernel.bb29 p).runBodyFrom e9 102 (pipelineState s q true P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h97
    _ = (avx2Kernel.bb29 p).runBodyFrom e9 107 (pipelineState s q true P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h102
    _ = (avx2Kernel.bb29 p).runBodyFrom e9 108 (pipelineState s q true P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h107
    _ = (avx2Kernel.bb29 p).runBodyFrom e10 113 (pipelineState s q true P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h108
    _ = (avx2Kernel.bb29 p).runBodyFrom e10 118 (pipelineState s q true P C 6) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h113
    _ = (avx2Kernel.bb29 p).runBodyFrom e10 119 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h118
    _ = (avx2Kernel.bb29 p).runBodyFrom e10 123 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h119
    _ = (avx2Kernel.bb29 p).runBodyFrom e11 128 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h123
    _ = (avx2Kernel.bb29 p).runBodyFrom e11 129 (pipelineState s q true P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h128
    _ = .value (e11, (pipelineState s q true P C 7)) := by
      rw [BasicBlock.runBodyFrom_done (hpos := by simp [avx2Kernel.bb29])]
      rfl

def exit29Env (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  (body29Env11 E q table index P C)[%805 := Ty.wrap (packPoint (resultPoint true P C) 3), %806 := Ty.wrap (packPoint (resultPoint true P C) 2), %807 := Ty.wrap (packPoint (resultPoint true P C) 1), %808 := Ty.wrap (packPoint (resultPoint true P C) 0), %809 := Ty.wrap (packPoint (resultPoint true P C) 4)]

theorem exit29_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (exit29Env E q table index P C) := by
  unfold exit29Env
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  exact body29_frame E q table index P C

theorem exit29_point (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (exit29Env E q table index P C).read (%805) = Ty.wrap (packPoint (resultPoint true P C) 3) ∧ (exit29Env E q table index P C).read (%806) = Ty.wrap (packPoint (resultPoint true P C) 2) ∧ (exit29Env E q table index P C).read (%807) = Ty.wrap (packPoint (resultPoint true P C) 1) ∧ (exit29Env E q table index P C).read (%808) = Ty.wrap (packPoint (resultPoint true P C) 0) ∧ (exit29Env E q table index P C).read (%809) = Ty.wrap (packPoint (resultPoint true P C) 4) := by
  simp [exit29Env, mlir_env]

theorem block29_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input29 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb29 p).run avx2Kernel.blockParams E s =
      .value ((exit29Env E q table index P C, .inr 30), pipelineState s q true P C 7) := by
  have hb := body29_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC
  obtain ⟨v0, v1, v2, v3, v4⟩ := body29_output E q table index P C
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp [avx2Kernel.bb29, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, DoubleBase.ExecutionAvx2.kernel_params30,
    exit29Env, v0, v1, v2, v3, v4, EffectM.pure_eq]

theorem block29_run (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input29 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) (g : Avx2CFG.Globals) :
    (avx2Kernel p g).runFrom E 29 s =
      (avx2Kernel p g).runFrom (exit29Env E q table index P C) 30 (pipelineState s q true P C 7) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 29 = avx2Kernel.bb29 p from rfl,
    block29_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC]
  simp only [PoisonOr.value_bind, Func.continue]

theorem block29_memoryFrame (s : GlobalState) (q : Scratch) (P C : Point) (hs : s.WF) :
    OutputFrame q s (pipelineState s q true P C 7) := pipelineState_frame s q true P C hs 7

theorem block29_reduced {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointReduced (resultPoint true P C) := resultPoint_reduced true hP hC

theorem block29_field {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (resultPoint true P C) = PointArithmetic.avx2AddCached (pointValue P)
      (PointArithmetic.negateCache (pointValue C)) := by
  simpa [resultPoint_eq] using sub_refines hP hC

/-- Field readback from the actual final output-memory state. -/
theorem block29_memoryPoint (s : GlobalState) (q : Scratch) (P C : Point)
    (hr : Reduce64.Execution.SmallRange s.mem q.output 160)
    (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q true P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (PointArithmetic.negateCache (pointValue C)) := by
  rw [readPoint_of_packed (pointReduced_wide (block29_reduced hP hC)) _ _
    (result_read s q true P C hr)]
  exact block29_field hP hC

/-- One local ladder transition: exact successor, concrete packed output,
preserved static registers/cursor, allocation and byte frame, restored bounds,
and field correctness. It assumes no enclosing iteration or ladder theorem. -/
theorem block29_endpoint (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input29 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb29 p).run avx2Kernel.blockParams E s =
      .value ((exit29Env E q table index P C, .inr 30), pipelineState s q true P C 7) ∧
    OutputFrame q s (pipelineState s q true P C 7) ∧
    RegisterFrame 427 avx2Kernel.Γ.n E (exit29Env E q table index P C) ∧
    Avx2FieldMul.Execution.readBlocks (pipelineState s q true P C 7).mem q.output = packPoint (resultPoint true P C) ∧
    pointReduced (resultPoint true P C) ∧
    (exit29Env E q table index P C).read (%805) = Ty.wrap (packPoint (resultPoint true P C) 3) ∧ (exit29Env E q table index P C).read (%806) = Ty.wrap (packPoint (resultPoint true P C) 2) ∧ (exit29Env E q table index P C).read (%807) = Ty.wrap (packPoint (resultPoint true P C) 1) ∧ (exit29Env E q table index P C).read (%808) = Ty.wrap (packPoint (resultPoint true P C) 0) ∧ (exit29Env E q table index P C).read (%809) = Ty.wrap (packPoint (resultPoint true P C) 4) ∧
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q true P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (PointArithmetic.negateCache (pointValue C)) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := exit29_point E q table index P C
  exact ⟨block29_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC,
    block29_memoryFrame s q P C hmem.wf, exit29_frame E q table index P C,
    result_read s q true P C (hmem.live 0), block29_reduced hP hC,
    v0, v1, v2, v3, v4, block29_memoryPoint s q P C (hmem.live 0) hP hC⟩

end Agave.Ed25519.Avx2PointAdd.CFG
