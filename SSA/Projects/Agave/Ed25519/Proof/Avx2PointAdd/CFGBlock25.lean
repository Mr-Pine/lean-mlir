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

structure Input25 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P : Point) : Prop where
  constants : Constants E
  r153 : E.read (%153) = .value 160#64
  r246 : E.read (%246) = .value q.right
  r247 : E.read (%247) = .value q.left
  r248 : E.read (%248) = .value q.product
  r249 : E.read (%249) = .value q.prepared
  r262 : E.read (%262) = .value q.output
  r264 : E.read (%264) = .value table
  r339 : E.read (%339) = .value (q.prepared.add 32#64)
  r340 : E.read (%340) = .value (q.prepared.add 64#64)
  r341 : E.read (%341) = .value (q.prepared.add 96#64)
  r342 : E.read (%342) = .value (q.prepared.add 128#64)
  r343 : E.read (%343) = .value (q.left.add 32#64)
  r344 : E.read (%344) = .value (q.left.add 64#64)
  r345 : E.read (%345) = .value (q.left.add 96#64)
  r346 : E.read (%346) = .value (q.left.add 128#64)
  r347 : E.read (%347) = .value (q.right.add 32#64)
  r348 : E.read (%348) = .value (q.right.add 64#64)
  r349 : E.read (%349) = .value (q.right.add 96#64)
  r350 : E.read (%350) = .value (q.right.add 128#64)
  r351 : E.read (%351) = .value (q.output.add 32#64)
  r352 : E.read (%352) = .value (q.output.add 64#64)
  r353 : E.read (%353) = .value (q.output.add 96#64)
  r354 : E.read (%354) = .value (q.output.add 128#64)
  r517 : E.read (%517) = Ty.wrap (packPoint P 0)
  r518 : E.read (%518) = Ty.wrap (packPoint P 1)
  r519 : E.read (%519) = Ty.wrap (packPoint P 2)
  r520 : E.read (%520) = Ty.wrap (packPoint P 3)
  r521 : E.read (%521) = Ty.wrap (packPoint P 4)
  r625 : E.read (%625) = .value (BitVec.ofNat 64 index.val)

def body25Env1 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  row25Env (E) table index

def body25Env2 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  prepare25Env (body25Env1 E q table index P C)

def body25Env3 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load25_product4Env (body25Env2 E q table index P C) (packPoint (productPoint false P C))

def body25Env4 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  abdc25Env (body25Env3 E q table index P C)

def body25Env5 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load25_product1Env (body25Env4 E q table index P C) (packPoint (productPoint false P C))

def body25Env6 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  difference25Env (body25Env5 E q table index P C)

def body25Env7 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  adda25Env (body25Env6 E q table index P C)

def body25Env8 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  cbcb25Env (body25Env7 E q table index P C)

def body25Env9 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load25_resultEnv (body25Env8 E q table index P C) (packPoint (resultPoint false P C))

theorem body25_output (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (body25Env9 E q table index P C).read (%693) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧
    (body25Env9 E q table index P C).read (%694) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧
    (body25Env9 E q table index P C).read (%695) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧
    (body25Env9 E q table index P C).read (%696) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧
    (body25Env9 E q table index P C).read (%697) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
  exact load25_result_reads _ _

theorem body25_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (body25Env9 E q table index P C) := by
  have f1 := (row25_frame (E) table index).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f2 := (prepare25_frame (body25Env1 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f3 := (load25_product4_frame (body25Env2 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f4 := (abdc25_frame (body25Env3 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f5 := (load25_product1_frame (body25Env4 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f6 := (difference25_frame (body25Env5 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f7 := (adda25_frame (body25Env6 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f8 := (cbcb25_frame (body25Env7 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f9 := (load25_result_frame (body25Env8 E q table index P C) (packPoint (resultPoint false P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  exact (((((((((RegisterFrame.refl 427 avx2Kernel.Γ.n E).trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9

theorem body25_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input25 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb25 p).runBodyFrom E 0 s =
      .value (body25Env9 E q table index P C, pipelineState s q false P C 7) := by
  let e1 := body25Env1 E q table index P C
  let e2 := body25Env2 E q table index P C
  let e3 := body25Env3 E q table index P C
  let e4 := body25Env4 E q table index P C
  let e5 := body25Env5 E q table index P C
  let e6 := body25Env6 E q table index P C
  let e7 := body25Env7 E q table index P C
  let e8 := body25Env8 E q table index P C
  let e9 := body25Env9 E q table index P C
  have h0 : runSlice (avx2Kernel.bb25 p) E 0 1 (pipelineState s q false P C 1) =
      .value (e1, (pipelineState s q false P C 1)) := by
    exact row25_slice p E (pipelineState s q false P C 1) table index bytes htable hindex (hreg.r264) (hreg.r625)
  have f1 : RegisterFrame 627 628 E e1 :=
    row25_frame E table index
  have v627 : e1.read (%627) = .value (tableRow table index) := by
    simp [e1, body25Env1, row25Env, mlir_env]
  have h1 : runSlice (avx2Kernel.bb25 p) e1 1 1 (pipelineState s q false P C 1) =
      .value (e1, (pipelineState s q false P C 1)) := by
    exact lifetime25_1_slice p e1 (pipelineState s q false P C 1)
  have h2 : runSlice (avx2Kernel.bb25 p) e1 2 25 (pipelineState s q false P C 1) =
      .value (e2, (pipelineState s q false P C 1)) := by
    exact prepare25_slice p e1 (pipelineState s q false P C 1)
  have f2 : RegisterFrame 628 653 e1 e2 :=
    prepare25_frame e1
  have r1_517 := (f1.read (%517) (by decide)).trans (hreg.r517)
  have r1_518 := (f1.read (%518) (by decide)).trans (hreg.r518)
  have r1_519 := (f1.read (%519) (by decide)).trans (hreg.r519)
  have r1_520 := (f1.read (%520) (by decide)).trans (hreg.r520)
  have r1_521 := (f1.read (%521) (by decide)).trans (hreg.r521)
  have r1_26 := (f1.read (%26) (by decide)).trans (hreg.constants.poison)
  have r1_135 := (f1.read (%135) (by decide)).trans (hreg.constants.prepare0)
  have r1_152 := (f1.read (%152) (by decide)).trans (hreg.constants.prepareN)
  have r1_170 := (f1.read (%170) (by decide)).trans (hreg.constants.difference0)
  have r1_187 := (f1.read (%187) (by decide)).trans (hreg.constants.differenceN)
  have r1_204 := (f1.read (%204) (by decide)).trans (hreg.constants.negate0)
  have r1_221 := (f1.read (%221) (by decide)).trans (hreg.constants.negateN)
  have cprepare25 : Constants e1 := ⟨r1_26, r1_135, r1_152, r1_170, r1_187, r1_204, r1_221⟩
  have iprepare25 : prepare25Inputs e1 (packPoint P) := ⟨r1_517, r1_518, r1_519, r1_520, r1_521⟩
  have v648 := prepare25_field e1 P hP cprepare25 iprepare25 0
  have v649 := prepare25_field e1 P hP cprepare25 iprepare25 1
  have v650 := prepare25_field e1 P hP cprepare25 iprepare25 2
  have v651 := prepare25_field e1 P hP cprepare25 iprepare25 3
  have v652 := prepare25_field e1 P hP cprepare25 iprepare25 4
  have r1_249 := (f1.read (%249) (by decide)).trans (hreg.r249)
  have r2_249 := (f2.read (%249) (by decide)).trans r1_249
  have r1_339 := (f1.read (%339) (by decide)).trans (hreg.r339)
  have r2_339 := (f2.read (%339) (by decide)).trans r1_339
  have r1_340 := (f1.read (%340) (by decide)).trans (hreg.r340)
  have r2_340 := (f2.read (%340) (by decide)).trans r1_340
  have r1_341 := (f1.read (%341) (by decide)).trans (hreg.r341)
  have r2_341 := (f2.read (%341) (by decide)).trans r1_341
  have r1_342 := (f1.read (%342) (by decide)).trans (hreg.r342)
  have r2_342 := (f2.read (%342) (by decide)).trans r1_342
  have h27 : runSlice (avx2Kernel.bb25 p) e2 27 5 (pipelineState s q false P C 1) =
      .value (e2, (pipelineState s q false P C 2)) := by
    exact prepare25_store_slice p e2 (pipelineState s q false P C 1) q.prepared (packPoint (prepare P)) (pipelineState_live s q false P C (hmem.live 1) 1) r2_249 (v648) r2_339 (v649) r2_340 (v650) r2_341 (v651) r2_342 (v652)
  have h32 : runSlice (avx2Kernel.bb25 p) e2 32 1 (pipelineState s q false P C 2) =
      .value (e2, (pipelineState s q false P C 2)) := by
    exact lifetime25_32_slice p e2 (pipelineState s q false P C 2)
  have r1_248 := (f1.read (%248) (by decide)).trans (hreg.r248)
  have r2_248 := (f2.read (%248) (by decide)).trans r1_248
  have r2_627 := (f2.read (%627) (by decide)).trans (v627)
  have h33 : runSlice (avx2Kernel.bb25 p) e2 33 1 (pipelineState s q false P C 2) =
      .value (e2, (pipelineState s q false P C 3)) := by
    exact multiply25_0_slice p e2 (pipelineState s q false P C 2) q.product q.prepared (cachePointer false q (tableRow table index)) (prepare P) (chosenCache false C) hmul (pipelineState_wf s q false P C hmem.wf 2) (pipelineState_live s q false P C (hmem.live 2) 2) (pipelineState_live s q false P C (hmem.live 1) 2) (pipelineState_live s q false P C (hmem.live 6) 2) (prepare_wide hP) (chosenCache_wide false hC) (prepared_read s q false P C (hmem.live 1)) (cache_read s q false (tableRow table index) P C hmem hcache) r2_248 r2_249 r2_627
  have r1_153 := (f1.read (%153) (by decide)).trans (hreg.r153)
  have r2_153 := (f2.read (%153) (by decide)).trans r1_153
  have h34 : runSlice (avx2Kernel.bb25 p) e2 34 1 (pipelineState s q false P C 3) =
      .value (e2, (pipelineState s q false P C 4)) := by
    exact copy25_slice p e2 (pipelineState s q false P C 3) q.prepared q.product (pipelineState_live s q false P C (hmem.live 1) 3) (pipelineState_live s q false P C (hmem.live 2) 3) (Or.inl (hmem.ne 1 2 (by decide))) r2_249 r2_248 r2_153
  have h35 : runSlice (avx2Kernel.bb25 p) e2 35 1 (pipelineState s q false P C 4) =
      .value (e2, (pipelineState s q false P C 4)) := by
    exact lifetime25_35_slice p e2 (pipelineState s q false P C 4)
  have h36 : runSlice (avx2Kernel.bb25 p) e2 36 4 (pipelineState s q false P C 4) =
      .value (e3, (pipelineState s q false P C 4)) := by
    exact load25_product4_slice p e2 (pipelineState s q false P C 4) q.prepared (packPoint (productPoint false P C)) (pipelineState_live s q false P C (hmem.live 1) 4) (copied_read s q false P C (hmem.live 1) (hmem.live 2)) r2_249 r2_339 r2_340 r2_341
  have f3 : RegisterFrame 653 657 e2 e3 :=
    load25_product4_frame e2 (packPoint (productPoint false P C))
  have v653 : e3.read (%653) = Ty.wrap (packPoint (productPoint false P C) 0) := by
    simp [e3, body25Env3, load25_product4Env, mlir_env]
  have v654 : e3.read (%654) = Ty.wrap (packPoint (productPoint false P C) 1) := by
    simp [e3, body25Env3, load25_product4Env, mlir_env]
  have v655 : e3.read (%655) = Ty.wrap (packPoint (productPoint false P C) 2) := by
    simp [e3, body25Env3, load25_product4Env, mlir_env]
  have v656 : e3.read (%656) = Ty.wrap (packPoint (productPoint false P C) 3) := by
    simp [e3, body25Env3, load25_product4Env, mlir_env]
  have h40 : runSlice (avx2Kernel.bb25 p) e3 40 4 (pipelineState s q false P C 4) =
      .value (e4, (pipelineState s q false P C 4)) := by
    exact abdc25_slice p e3 (pipelineState s q false P C 4)
  have f4 : RegisterFrame 657 661 e3 e4 :=
    abdc25_frame e3
  have r2_26 := (f2.read (%26) (by decide)).trans r1_26
  have r3_26 := (f3.read (%26) (by decide)).trans r2_26
  obtain ⟨v657, v658, v659, v660⟩ := abdc25_reads e3 (packPoint (productPoint false P C)) r3_26 (v653) (v654) (v655) (v656)
  have r3_342 := (f3.read (%342) (by decide)).trans r2_342
  have r4_342 := (f4.read (%342) (by decide)).trans r3_342
  have h44 : runSlice (avx2Kernel.bb25 p) e4 44 1 (pipelineState s q false P C 4) =
      .value (e5, (pipelineState s q false P C 4)) := by
    exact load25_product1_slice p e4 (pipelineState s q false P C 4) q.prepared (packPoint (productPoint false P C)) (pipelineState_live s q false P C (hmem.live 1) 4) (copied_read s q false P C (hmem.live 1) (hmem.live 2)) r4_342
  have f5 : RegisterFrame 661 662 e4 e5 :=
    load25_product1_frame e4 (packPoint (productPoint false P C))
  have v661 : e5.read (%661) = Ty.wrap (packPoint (productPoint false P C) 4) := by
    simp [e5, body25Env5, load25_product1Env, mlir_env]
  have h45 : runSlice (avx2Kernel.bb25 p) e5 45 21 (pipelineState s q false P C 4) =
      .value (e6, (pipelineState s q false P C 4)) := by
    exact difference25_slice p e5 (pipelineState s q false P C 4)
  have f6 : RegisterFrame 662 683 e5 e6 :=
    difference25_frame e5
  have r4_653 := (f4.read (%653) (by decide)).trans (v653)
  have r5_653 := (f5.read (%653) (by decide)).trans r4_653
  have r4_654 := (f4.read (%654) (by decide)).trans (v654)
  have r5_654 := (f5.read (%654) (by decide)).trans r4_654
  have r4_655 := (f4.read (%655) (by decide)).trans (v655)
  have r5_655 := (f5.read (%655) (by decide)).trans r4_655
  have r4_656 := (f4.read (%656) (by decide)).trans (v656)
  have r5_656 := (f5.read (%656) (by decide)).trans r4_656
  have r5_657 := (f5.read (%657) (by decide)).trans (v657)
  have r5_658 := (f5.read (%658) (by decide)).trans (v658)
  have r5_659 := (f5.read (%659) (by decide)).trans (v659)
  have r5_660 := (f5.read (%660) (by decide)).trans (v660)
  have r4_26 := (f4.read (%26) (by decide)).trans r3_26
  have r5_26 := (f5.read (%26) (by decide)).trans r4_26
  have r2_135 := (f2.read (%135) (by decide)).trans r1_135
  have r3_135 := (f3.read (%135) (by decide)).trans r2_135
  have r4_135 := (f4.read (%135) (by decide)).trans r3_135
  have r5_135 := (f5.read (%135) (by decide)).trans r4_135
  have r2_152 := (f2.read (%152) (by decide)).trans r1_152
  have r3_152 := (f3.read (%152) (by decide)).trans r2_152
  have r4_152 := (f4.read (%152) (by decide)).trans r3_152
  have r5_152 := (f5.read (%152) (by decide)).trans r4_152
  have r2_170 := (f2.read (%170) (by decide)).trans r1_170
  have r3_170 := (f3.read (%170) (by decide)).trans r2_170
  have r4_170 := (f4.read (%170) (by decide)).trans r3_170
  have r5_170 := (f5.read (%170) (by decide)).trans r4_170
  have r2_187 := (f2.read (%187) (by decide)).trans r1_187
  have r3_187 := (f3.read (%187) (by decide)).trans r2_187
  have r4_187 := (f4.read (%187) (by decide)).trans r3_187
  have r5_187 := (f5.read (%187) (by decide)).trans r4_187
  have r2_204 := (f2.read (%204) (by decide)).trans r1_204
  have r3_204 := (f3.read (%204) (by decide)).trans r2_204
  have r4_204 := (f4.read (%204) (by decide)).trans r3_204
  have r5_204 := (f5.read (%204) (by decide)).trans r4_204
  have r2_221 := (f2.read (%221) (by decide)).trans r1_221
  have r3_221 := (f3.read (%221) (by decide)).trans r2_221
  have r4_221 := (f4.read (%221) (by decide)).trans r3_221
  have r5_221 := (f5.read (%221) (by decide)).trans r4_221
  have cdifference25 : Constants e5 := ⟨r5_26, r5_135, r5_152, r5_170, r5_187, r5_204, r5_221⟩
  have idifference25 : difference25Inputs e5 (packPoint (productPoint false P C)) := ⟨r5_653, r5_654, r5_655, r5_656, (v661), r5_657, r5_658, r5_659, r5_660⟩
  have v678 := difference25_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference25 idifference25 0
  have v679 := difference25_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference25 idifference25 1
  have v680 := difference25_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference25 idifference25 2
  have v681 := difference25_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference25 idifference25 3
  have v682 := difference25_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference25 idifference25 4
  have h66 : runSlice (avx2Kernel.bb25 p) e6 66 1 (pipelineState s q false P C 4) =
      .value (e6, (pipelineState s q false P C 4)) := by
    exact lifetime25_66_slice p e6 (pipelineState s q false P C 4)
  have h67 : runSlice (avx2Kernel.bb25 p) e6 67 5 (pipelineState s q false P C 4) =
      .value (e7, (pipelineState s q false P C 4)) := by
    exact adda25_slice p e6 (pipelineState s q false P C 4)
  have f7 : RegisterFrame 683 688 e6 e7 :=
    adda25_frame e6
  have r6_26 := (f6.read (%26) (by decide)).trans r5_26
  have r6_135 := (f6.read (%135) (by decide)).trans r5_135
  have r6_152 := (f6.read (%152) (by decide)).trans r5_152
  have r6_170 := (f6.read (%170) (by decide)).trans r5_170
  have r6_187 := (f6.read (%187) (by decide)).trans r5_187
  have r6_204 := (f6.read (%204) (by decide)).trans r5_204
  have r6_221 := (f6.read (%221) (by decide)).trans r5_221
  have cadda25 : Constants e6 := ⟨r6_26, r6_135, r6_152, r6_170, r6_187, r6_204, r6_221⟩
  have iadda25 : adda25Inputs e6 (packPoint (differencePoint false P C)) := ⟨(v678), (v679), (v680), (v681), (v682)⟩
  have v683 := adda25_field e6 (differencePoint false P C) cadda25 iadda25 0
  have v684 := adda25_field e6 (differencePoint false P C) cadda25 iadda25 1
  have v685 := adda25_field e6 (differencePoint false P C) cadda25 iadda25 2
  have v686 := adda25_field e6 (differencePoint false P C) cadda25 iadda25 3
  have v687 := adda25_field e6 (differencePoint false P C) cadda25 iadda25 4
  have r1_247 := (f1.read (%247) (by decide)).trans (hreg.r247)
  have r2_247 := (f2.read (%247) (by decide)).trans r1_247
  have r3_247 := (f3.read (%247) (by decide)).trans r2_247
  have r4_247 := (f4.read (%247) (by decide)).trans r3_247
  have r5_247 := (f5.read (%247) (by decide)).trans r4_247
  have r6_247 := (f6.read (%247) (by decide)).trans r5_247
  have r7_247 := (f7.read (%247) (by decide)).trans r6_247
  have r1_343 := (f1.read (%343) (by decide)).trans (hreg.r343)
  have r2_343 := (f2.read (%343) (by decide)).trans r1_343
  have r3_343 := (f3.read (%343) (by decide)).trans r2_343
  have r4_343 := (f4.read (%343) (by decide)).trans r3_343
  have r5_343 := (f5.read (%343) (by decide)).trans r4_343
  have r6_343 := (f6.read (%343) (by decide)).trans r5_343
  have r7_343 := (f7.read (%343) (by decide)).trans r6_343
  have r1_344 := (f1.read (%344) (by decide)).trans (hreg.r344)
  have r2_344 := (f2.read (%344) (by decide)).trans r1_344
  have r3_344 := (f3.read (%344) (by decide)).trans r2_344
  have r4_344 := (f4.read (%344) (by decide)).trans r3_344
  have r5_344 := (f5.read (%344) (by decide)).trans r4_344
  have r6_344 := (f6.read (%344) (by decide)).trans r5_344
  have r7_344 := (f7.read (%344) (by decide)).trans r6_344
  have r1_345 := (f1.read (%345) (by decide)).trans (hreg.r345)
  have r2_345 := (f2.read (%345) (by decide)).trans r1_345
  have r3_345 := (f3.read (%345) (by decide)).trans r2_345
  have r4_345 := (f4.read (%345) (by decide)).trans r3_345
  have r5_345 := (f5.read (%345) (by decide)).trans r4_345
  have r6_345 := (f6.read (%345) (by decide)).trans r5_345
  have r7_345 := (f7.read (%345) (by decide)).trans r6_345
  have r1_346 := (f1.read (%346) (by decide)).trans (hreg.r346)
  have r2_346 := (f2.read (%346) (by decide)).trans r1_346
  have r3_346 := (f3.read (%346) (by decide)).trans r2_346
  have r4_346 := (f4.read (%346) (by decide)).trans r3_346
  have r5_346 := (f5.read (%346) (by decide)).trans r4_346
  have r6_346 := (f6.read (%346) (by decide)).trans r5_346
  have r7_346 := (f7.read (%346) (by decide)).trans r6_346
  have h72 : runSlice (avx2Kernel.bb25 p) e7 72 5 (pipelineState s q false P C 4) =
      .value (e7, (pipelineState s q false P C 5)) := by
    exact adda25_store_slice p e7 (pipelineState s q false P C 4) q.left (packPoint (leftPoint false P C)) (pipelineState_live s q false P C (hmem.live 3) 4) r7_247 (v683) r7_343 (v684) r7_344 (v685) r7_345 (v686) r7_346 (v687)
  have h77 : runSlice (avx2Kernel.bb25 p) e7 77 1 (pipelineState s q false P C 5) =
      .value (e7, (pipelineState s q false P C 5)) := by
    exact lifetime25_77_slice p e7 (pipelineState s q false P C 5)
  have h78 : runSlice (avx2Kernel.bb25 p) e7 78 5 (pipelineState s q false P C 5) =
      .value (e8, (pipelineState s q false P C 5)) := by
    exact cbcb25_slice p e7 (pipelineState s q false P C 5)
  have f8 : RegisterFrame 688 693 e7 e8 :=
    cbcb25_frame e7
  have r7_678 := (f7.read (%678) (by decide)).trans (v678)
  have r7_679 := (f7.read (%679) (by decide)).trans (v679)
  have r7_680 := (f7.read (%680) (by decide)).trans (v680)
  have r7_681 := (f7.read (%681) (by decide)).trans (v681)
  have r7_682 := (f7.read (%682) (by decide)).trans (v682)
  have r7_26 := (f7.read (%26) (by decide)).trans r6_26
  have r7_135 := (f7.read (%135) (by decide)).trans r6_135
  have r7_152 := (f7.read (%152) (by decide)).trans r6_152
  have r7_170 := (f7.read (%170) (by decide)).trans r6_170
  have r7_187 := (f7.read (%187) (by decide)).trans r6_187
  have r7_204 := (f7.read (%204) (by decide)).trans r6_204
  have r7_221 := (f7.read (%221) (by decide)).trans r6_221
  have ccbcb25 : Constants e7 := ⟨r7_26, r7_135, r7_152, r7_170, r7_187, r7_204, r7_221⟩
  have icbcb25 : cbcb25Inputs e7 (packPoint (differencePoint false P C)) := ⟨r7_678, r7_679, r7_680, r7_681, r7_682⟩
  have v688 := cbcb25_field e7 (differencePoint false P C) ccbcb25 icbcb25 0
  have v689 := cbcb25_field e7 (differencePoint false P C) ccbcb25 icbcb25 1
  have v690 := cbcb25_field e7 (differencePoint false P C) ccbcb25 icbcb25 2
  have v691 := cbcb25_field e7 (differencePoint false P C) ccbcb25 icbcb25 3
  have v692 := cbcb25_field e7 (differencePoint false P C) ccbcb25 icbcb25 4
  have r1_246 := (f1.read (%246) (by decide)).trans (hreg.r246)
  have r2_246 := (f2.read (%246) (by decide)).trans r1_246
  have r3_246 := (f3.read (%246) (by decide)).trans r2_246
  have r4_246 := (f4.read (%246) (by decide)).trans r3_246
  have r5_246 := (f5.read (%246) (by decide)).trans r4_246
  have r6_246 := (f6.read (%246) (by decide)).trans r5_246
  have r7_246 := (f7.read (%246) (by decide)).trans r6_246
  have r8_246 := (f8.read (%246) (by decide)).trans r7_246
  have r1_347 := (f1.read (%347) (by decide)).trans (hreg.r347)
  have r2_347 := (f2.read (%347) (by decide)).trans r1_347
  have r3_347 := (f3.read (%347) (by decide)).trans r2_347
  have r4_347 := (f4.read (%347) (by decide)).trans r3_347
  have r5_347 := (f5.read (%347) (by decide)).trans r4_347
  have r6_347 := (f6.read (%347) (by decide)).trans r5_347
  have r7_347 := (f7.read (%347) (by decide)).trans r6_347
  have r8_347 := (f8.read (%347) (by decide)).trans r7_347
  have r1_348 := (f1.read (%348) (by decide)).trans (hreg.r348)
  have r2_348 := (f2.read (%348) (by decide)).trans r1_348
  have r3_348 := (f3.read (%348) (by decide)).trans r2_348
  have r4_348 := (f4.read (%348) (by decide)).trans r3_348
  have r5_348 := (f5.read (%348) (by decide)).trans r4_348
  have r6_348 := (f6.read (%348) (by decide)).trans r5_348
  have r7_348 := (f7.read (%348) (by decide)).trans r6_348
  have r8_348 := (f8.read (%348) (by decide)).trans r7_348
  have r1_349 := (f1.read (%349) (by decide)).trans (hreg.r349)
  have r2_349 := (f2.read (%349) (by decide)).trans r1_349
  have r3_349 := (f3.read (%349) (by decide)).trans r2_349
  have r4_349 := (f4.read (%349) (by decide)).trans r3_349
  have r5_349 := (f5.read (%349) (by decide)).trans r4_349
  have r6_349 := (f6.read (%349) (by decide)).trans r5_349
  have r7_349 := (f7.read (%349) (by decide)).trans r6_349
  have r8_349 := (f8.read (%349) (by decide)).trans r7_349
  have r1_350 := (f1.read (%350) (by decide)).trans (hreg.r350)
  have r2_350 := (f2.read (%350) (by decide)).trans r1_350
  have r3_350 := (f3.read (%350) (by decide)).trans r2_350
  have r4_350 := (f4.read (%350) (by decide)).trans r3_350
  have r5_350 := (f5.read (%350) (by decide)).trans r4_350
  have r6_350 := (f6.read (%350) (by decide)).trans r5_350
  have r7_350 := (f7.read (%350) (by decide)).trans r6_350
  have r8_350 := (f8.read (%350) (by decide)).trans r7_350
  have h83 : runSlice (avx2Kernel.bb25 p) e8 83 5 (pipelineState s q false P C 5) =
      .value (e8, (pipelineState s q false P C 6)) := by
    exact cbcb25_store_slice p e8 (pipelineState s q false P C 5) q.right (packPoint (rightPoint false P C)) (pipelineState_live s q false P C (hmem.live 4) 5) r8_246 (v688) r8_347 (v689) r8_348 (v690) r8_349 (v691) r8_350 (v692)
  have r1_262 := (f1.read (%262) (by decide)).trans (hreg.r262)
  have r2_262 := (f2.read (%262) (by decide)).trans r1_262
  have r3_262 := (f3.read (%262) (by decide)).trans r2_262
  have r4_262 := (f4.read (%262) (by decide)).trans r3_262
  have r5_262 := (f5.read (%262) (by decide)).trans r4_262
  have r6_262 := (f6.read (%262) (by decide)).trans r5_262
  have r7_262 := (f7.read (%262) (by decide)).trans r6_262
  have r8_262 := (f8.read (%262) (by decide)).trans r7_262
  have r8_247 := (f8.read (%247) (by decide)).trans r7_247
  have h88 : runSlice (avx2Kernel.bb25 p) e8 88 1 (pipelineState s q false P C 6) =
      .value (e8, (pipelineState s q false P C 7)) := by
    exact multiply25_1_slice p e8 (pipelineState s q false P C 6) q.output q.left q.right (leftPoint false P C) (rightPoint false P C) hmul (pipelineState_wf s q false P C hmem.wf 6) (pipelineState_live s q false P C (hmem.live 0) 6) (pipelineState_live s q false P C (hmem.live 3) 6) (pipelineState_live s q false P C (hmem.live 4) 6) (leftPoint_wide false hP hC) (rightPoint_wide false hP hC) (factors_read s q false (tableRow table index) P C hmem).1 (factors_read s q false (tableRow table index) P C hmem).2 r8_262 r8_247 r8_246
  have h89 : runSlice (avx2Kernel.bb25 p) e8 89 3 (pipelineState s q false P C 7) =
      .value (e8, (pipelineState s q false P C 7)) := by
    exact lifetime25_89_slice p e8 (pipelineState s q false P C 7)
  have r1_351 := (f1.read (%351) (by decide)).trans (hreg.r351)
  have r2_351 := (f2.read (%351) (by decide)).trans r1_351
  have r3_351 := (f3.read (%351) (by decide)).trans r2_351
  have r4_351 := (f4.read (%351) (by decide)).trans r3_351
  have r5_351 := (f5.read (%351) (by decide)).trans r4_351
  have r6_351 := (f6.read (%351) (by decide)).trans r5_351
  have r7_351 := (f7.read (%351) (by decide)).trans r6_351
  have r8_351 := (f8.read (%351) (by decide)).trans r7_351
  have r1_352 := (f1.read (%352) (by decide)).trans (hreg.r352)
  have r2_352 := (f2.read (%352) (by decide)).trans r1_352
  have r3_352 := (f3.read (%352) (by decide)).trans r2_352
  have r4_352 := (f4.read (%352) (by decide)).trans r3_352
  have r5_352 := (f5.read (%352) (by decide)).trans r4_352
  have r6_352 := (f6.read (%352) (by decide)).trans r5_352
  have r7_352 := (f7.read (%352) (by decide)).trans r6_352
  have r8_352 := (f8.read (%352) (by decide)).trans r7_352
  have r1_353 := (f1.read (%353) (by decide)).trans (hreg.r353)
  have r2_353 := (f2.read (%353) (by decide)).trans r1_353
  have r3_353 := (f3.read (%353) (by decide)).trans r2_353
  have r4_353 := (f4.read (%353) (by decide)).trans r3_353
  have r5_353 := (f5.read (%353) (by decide)).trans r4_353
  have r6_353 := (f6.read (%353) (by decide)).trans r5_353
  have r7_353 := (f7.read (%353) (by decide)).trans r6_353
  have r8_353 := (f8.read (%353) (by decide)).trans r7_353
  have r1_354 := (f1.read (%354) (by decide)).trans (hreg.r354)
  have r2_354 := (f2.read (%354) (by decide)).trans r1_354
  have r3_354 := (f3.read (%354) (by decide)).trans r2_354
  have r4_354 := (f4.read (%354) (by decide)).trans r3_354
  have r5_354 := (f5.read (%354) (by decide)).trans r4_354
  have r6_354 := (f6.read (%354) (by decide)).trans r5_354
  have r7_354 := (f7.read (%354) (by decide)).trans r6_354
  have r8_354 := (f8.read (%354) (by decide)).trans r7_354
  have h92 : runSlice (avx2Kernel.bb25 p) e8 92 5 (pipelineState s q false P C 7) =
      .value (e9, (pipelineState s q false P C 7)) := by
    exact load25_result_slice p e8 (pipelineState s q false P C 7) q.output (packPoint (resultPoint false P C)) (pipelineState_live s q false P C (hmem.live 0) 7) (result_read s q false P C (hmem.live 0)) r8_262 r8_351 r8_352 r8_353 r8_354
  have f9 : RegisterFrame 693 698 e8 e9 :=
    load25_result_frame e8 (packPoint (resultPoint false P C))
  have v693 : e9.read (%693) = Ty.wrap (packPoint (resultPoint false P C) 0) := by
    simp [e9, body25Env9, load25_resultEnv, mlir_env]
  have v694 : e9.read (%694) = Ty.wrap (packPoint (resultPoint false P C) 1) := by
    simp [e9, body25Env9, load25_resultEnv, mlir_env]
  have v695 : e9.read (%695) = Ty.wrap (packPoint (resultPoint false P C) 2) := by
    simp [e9, body25Env9, load25_resultEnv, mlir_env]
  have v696 : e9.read (%696) = Ty.wrap (packPoint (resultPoint false P C) 3) := by
    simp [e9, body25Env9, load25_resultEnv, mlir_env]
  have v697 : e9.read (%697) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
    simp [e9, body25Env9, load25_resultEnv, mlir_env]
  have h97 : runSlice (avx2Kernel.bb25 p) e9 97 1 (pipelineState s q false P C 7) =
      .value (e9, (pipelineState s q false P C 7)) := by
    exact lifetime25_97_slice p e9 (pipelineState s q false P C 7)
  calc
    (avx2Kernel.bb25 p).runBodyFrom E 0 (pipelineState s q false P C 1) = (avx2Kernel.bb25 p).runBodyFrom e1 1 (pipelineState s q false P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h0
    _ = (avx2Kernel.bb25 p).runBodyFrom e1 2 (pipelineState s q false P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h1
    _ = (avx2Kernel.bb25 p).runBodyFrom e2 27 (pipelineState s q false P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h2
    _ = (avx2Kernel.bb25 p).runBodyFrom e2 32 (pipelineState s q false P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h27
    _ = (avx2Kernel.bb25 p).runBodyFrom e2 33 (pipelineState s q false P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h32
    _ = (avx2Kernel.bb25 p).runBodyFrom e2 34 (pipelineState s q false P C 3) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h33
    _ = (avx2Kernel.bb25 p).runBodyFrom e2 35 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h34
    _ = (avx2Kernel.bb25 p).runBodyFrom e2 36 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h35
    _ = (avx2Kernel.bb25 p).runBodyFrom e3 40 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h36
    _ = (avx2Kernel.bb25 p).runBodyFrom e4 44 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h40
    _ = (avx2Kernel.bb25 p).runBodyFrom e5 45 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h44
    _ = (avx2Kernel.bb25 p).runBodyFrom e6 66 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h45
    _ = (avx2Kernel.bb25 p).runBodyFrom e6 67 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h66
    _ = (avx2Kernel.bb25 p).runBodyFrom e7 72 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h67
    _ = (avx2Kernel.bb25 p).runBodyFrom e7 77 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h72
    _ = (avx2Kernel.bb25 p).runBodyFrom e7 78 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h77
    _ = (avx2Kernel.bb25 p).runBodyFrom e8 83 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h78
    _ = (avx2Kernel.bb25 p).runBodyFrom e8 88 (pipelineState s q false P C 6) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h83
    _ = (avx2Kernel.bb25 p).runBodyFrom e8 89 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h88
    _ = (avx2Kernel.bb25 p).runBodyFrom e8 92 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h89
    _ = (avx2Kernel.bb25 p).runBodyFrom e9 97 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h92
    _ = (avx2Kernel.bb25 p).runBodyFrom e9 98 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h97
    _ = .value (e9, (pipelineState s q false P C 7)) := by
      rw [BasicBlock.runBodyFrom_done (hpos := by simp [avx2Kernel.bb25])]
      rfl

def exit25Env (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  (body25Env9 E q table index P C)[%698 := Ty.wrap (packPoint (resultPoint false P C) 3), %699 := Ty.wrap (packPoint (resultPoint false P C) 2), %700 := Ty.wrap (packPoint (resultPoint false P C) 1), %701 := Ty.wrap (packPoint (resultPoint false P C) 0), %702 := Ty.wrap (packPoint (resultPoint false P C) 4)]

theorem exit25_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (exit25Env E q table index P C) := by
  unfold exit25Env
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  exact body25_frame E q table index P C

theorem exit25_point (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (exit25Env E q table index P C).read (%698) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧ (exit25Env E q table index P C).read (%699) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧ (exit25Env E q table index P C).read (%700) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧ (exit25Env E q table index P C).read (%701) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧ (exit25Env E q table index P C).read (%702) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
  simp [exit25Env, mlir_env]

theorem block25_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input25 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb25 p).run avx2Kernel.blockParams E s =
      .value ((exit25Env E q table index P C, .inr 26), pipelineState s q false P C 7) := by
  have hb := body25_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC
  obtain ⟨v0, v1, v2, v3, v4⟩ := body25_output E q table index P C
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp [avx2Kernel.bb25, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, DoubleBase.ExecutionAvx2.kernel_params26,
    exit25Env, v0, v1, v2, v3, v4, EffectM.pure_eq]

theorem block25_run (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input25 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) (g : Avx2CFG.Globals) :
    (avx2Kernel p g).runFrom E 25 s =
      (avx2Kernel p g).runFrom (exit25Env E q table index P C) 26 (pipelineState s q false P C 7) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 25 = avx2Kernel.bb25 p from rfl,
    block25_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC]
  simp only [PoisonOr.value_bind, Func.continue]

theorem block25_memoryFrame (s : GlobalState) (q : Scratch) (P C : Point) (hs : s.WF) :
    OutputFrame q s (pipelineState s q false P C 7) := pipelineState_frame s q false P C hs 7

theorem block25_reduced {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointReduced (resultPoint false P C) := resultPoint_reduced false hP hC

theorem block25_field {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (resultPoint false P C) = PointArithmetic.avx2AddCached (pointValue P)
      (pointValue C) := by
  simpa [resultPoint_eq] using add_refines hP (pointReduced_wide hC)

/-- Field readback from the actual final output-memory state. -/
theorem block25_memoryPoint (s : GlobalState) (q : Scratch) (P C : Point)
    (hr : Reduce64.Execution.SmallRange s.mem q.output 160)
    (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q false P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (pointValue C) := by
  rw [readPoint_of_packed (pointReduced_wide (block25_reduced hP hC)) _ _
    (result_read s q false P C hr)]
  exact block25_field hP hC

/-- One local ladder transition: exact successor, concrete packed output,
preserved static registers/cursor, allocation and byte frame, restored bounds,
and field correctness. It assumes no enclosing iteration or ladder theorem. -/
theorem block25_endpoint (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input25 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb25 p).run avx2Kernel.blockParams E s =
      .value ((exit25Env E q table index P C, .inr 26), pipelineState s q false P C 7) ∧
    OutputFrame q s (pipelineState s q false P C 7) ∧
    RegisterFrame 427 avx2Kernel.Γ.n E (exit25Env E q table index P C) ∧
    Avx2FieldMul.Execution.readBlocks (pipelineState s q false P C 7).mem q.output = packPoint (resultPoint false P C) ∧
    pointReduced (resultPoint false P C) ∧
    (exit25Env E q table index P C).read (%698) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧ (exit25Env E q table index P C).read (%699) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧ (exit25Env E q table index P C).read (%700) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧ (exit25Env E q table index P C).read (%701) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧ (exit25Env E q table index P C).read (%702) = Ty.wrap (packPoint (resultPoint false P C) 4) ∧
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q false P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (pointValue C) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := exit25_point E q table index P C
  exact ⟨block25_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC,
    block25_memoryFrame s q P C hmem.wf, exit25_frame E q table index P C,
    result_read s q false P C (hmem.live 0), block25_reduced hP hC,
    v0, v1, v2, v3, v4, block25_memoryPoint s q P C (hmem.live 0) hP hC⟩

end Agave.Ed25519.Avx2PointAdd.CFG
