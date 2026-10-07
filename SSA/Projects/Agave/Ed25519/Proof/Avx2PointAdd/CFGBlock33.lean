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

structure Input33 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P : Point) : Prop where
  constants : Constants E
  r153 : E.read (%153) = .value 160#64
  r224 : E.read (%224) = .value table
  r237 : E.read (%237) = .value q.right
  r238 : E.read (%238) = .value q.left
  r239 : E.read (%239) = .value q.product
  r240 : E.read (%240) = .value q.prepared
  r260 : E.read (%260) = .value q.output
  r375 : E.read (%375) = .value (q.prepared.add 32#64)
  r376 : E.read (%376) = .value (q.prepared.add 64#64)
  r377 : E.read (%377) = .value (q.prepared.add 96#64)
  r378 : E.read (%378) = .value (q.prepared.add 128#64)
  r379 : E.read (%379) = .value (q.left.add 32#64)
  r380 : E.read (%380) = .value (q.left.add 64#64)
  r381 : E.read (%381) = .value (q.left.add 96#64)
  r382 : E.read (%382) = .value (q.left.add 128#64)
  r383 : E.read (%383) = .value (q.right.add 32#64)
  r384 : E.read (%384) = .value (q.right.add 64#64)
  r385 : E.read (%385) = .value (q.right.add 96#64)
  r386 : E.read (%386) = .value (q.right.add 128#64)
  r387 : E.read (%387) = .value (q.output.add 32#64)
  r388 : E.read (%388) = .value (q.output.add 64#64)
  r389 : E.read (%389) = .value (q.output.add 96#64)
  r390 : E.read (%390) = .value (q.output.add 128#64)
  r698 : E.read (%698) = Ty.wrap (packPoint P 3)
  r699 : E.read (%699) = Ty.wrap (packPoint P 2)
  r700 : E.read (%700) = Ty.wrap (packPoint P 1)
  r701 : E.read (%701) = Ty.wrap (packPoint P 0)
  r702 : E.read (%702) = Ty.wrap (packPoint P 4)
  r813 : E.read (%813) = .value (BitVec.ofNat 64 index.val)

def body33Env1 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  row33Env (E) table index

def body33Env2 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  prepare33Env (body33Env1 E q table index P C)

def body33Env3 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load33_product4Env (body33Env2 E q table index P C) (packPoint (productPoint false P C))

def body33Env4 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  abdc33Env (body33Env3 E q table index P C)

def body33Env5 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load33_product1Env (body33Env4 E q table index P C) (packPoint (productPoint false P C))

def body33Env6 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  difference33Env (body33Env5 E q table index P C)

def body33Env7 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  adda33Env (body33Env6 E q table index P C)

def body33Env8 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  cbcb33Env (body33Env7 E q table index P C)

def body33Env9 (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  load33_resultEnv (body33Env8 E q table index P C) (packPoint (resultPoint false P C))

theorem body33_output (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (body33Env9 E q table index P C).read (%881) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧
    (body33Env9 E q table index P C).read (%882) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧
    (body33Env9 E q table index P C).read (%883) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧
    (body33Env9 E q table index P C).read (%884) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧
    (body33Env9 E q table index P C).read (%885) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
  exact load33_result_reads _ _

theorem body33_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (body33Env9 E q table index P C) := by
  have f1 := (row33_frame (E) table index).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f2 := (prepare33_frame (body33Env1 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f3 := (load33_product4_frame (body33Env2 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f4 := (abdc33_frame (body33Env3 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f5 := (load33_product1_frame (body33Env4 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f6 := (difference33_frame (body33Env5 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f7 := (adda33_frame (body33Env6 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f8 := (cbcb33_frame (body33Env7 E q table index P C)).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  have f9 := (load33_result_frame (body33Env8 E q table index P C) (packPoint (resultPoint false P C))).weaken (lo' := 427) (hi' := avx2Kernel.Γ.n) (by decide) (by decide)
  exact (((((((((RegisterFrame.refl 427 avx2Kernel.Γ.n E).trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9

theorem body33_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input33 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb33 p).runBodyFrom E 0 s =
      .value (body33Env9 E q table index P C, pipelineState s q false P C 7) := by
  let e1 := body33Env1 E q table index P C
  let e2 := body33Env2 E q table index P C
  let e3 := body33Env3 E q table index P C
  let e4 := body33Env4 E q table index P C
  let e5 := body33Env5 E q table index P C
  let e6 := body33Env6 E q table index P C
  let e7 := body33Env7 E q table index P C
  let e8 := body33Env8 E q table index P C
  let e9 := body33Env9 E q table index P C
  have h0 : runSlice (avx2Kernel.bb33 p) E 0 1 (pipelineState s q false P C 1) =
      .value (e1, (pipelineState s q false P C 1)) := by
    exact row33_slice p E (pipelineState s q false P C 1) table index bytes htable hindex (hreg.r224) (hreg.r813)
  have f1 : RegisterFrame 815 816 E e1 :=
    row33_frame E table index
  have v815 : e1.read (%815) = .value (tableRow table index) := by
    simp [e1, body33Env1, row33Env, mlir_env]
  have h1 : runSlice (avx2Kernel.bb33 p) e1 1 1 (pipelineState s q false P C 1) =
      .value (e1, (pipelineState s q false P C 1)) := by
    exact lifetime33_1_slice p e1 (pipelineState s q false P C 1)
  have h2 : runSlice (avx2Kernel.bb33 p) e1 2 25 (pipelineState s q false P C 1) =
      .value (e2, (pipelineState s q false P C 1)) := by
    exact prepare33_slice p e1 (pipelineState s q false P C 1)
  have f2 : RegisterFrame 816 841 e1 e2 :=
    prepare33_frame e1
  have r1_701 := (f1.read (%701) (by decide)).trans (hreg.r701)
  have r1_700 := (f1.read (%700) (by decide)).trans (hreg.r700)
  have r1_699 := (f1.read (%699) (by decide)).trans (hreg.r699)
  have r1_698 := (f1.read (%698) (by decide)).trans (hreg.r698)
  have r1_702 := (f1.read (%702) (by decide)).trans (hreg.r702)
  have r1_26 := (f1.read (%26) (by decide)).trans (hreg.constants.poison)
  have r1_135 := (f1.read (%135) (by decide)).trans (hreg.constants.prepare0)
  have r1_152 := (f1.read (%152) (by decide)).trans (hreg.constants.prepareN)
  have r1_170 := (f1.read (%170) (by decide)).trans (hreg.constants.difference0)
  have r1_187 := (f1.read (%187) (by decide)).trans (hreg.constants.differenceN)
  have r1_204 := (f1.read (%204) (by decide)).trans (hreg.constants.negate0)
  have r1_221 := (f1.read (%221) (by decide)).trans (hreg.constants.negateN)
  have cprepare33 : Constants e1 := ⟨r1_26, r1_135, r1_152, r1_170, r1_187, r1_204, r1_221⟩
  have iprepare33 : prepare33Inputs e1 (packPoint P) := ⟨r1_701, r1_700, r1_699, r1_698, r1_702⟩
  have v836 := prepare33_field e1 P hP cprepare33 iprepare33 0
  have v837 := prepare33_field e1 P hP cprepare33 iprepare33 1
  have v838 := prepare33_field e1 P hP cprepare33 iprepare33 2
  have v839 := prepare33_field e1 P hP cprepare33 iprepare33 3
  have v840 := prepare33_field e1 P hP cprepare33 iprepare33 4
  have r1_240 := (f1.read (%240) (by decide)).trans (hreg.r240)
  have r2_240 := (f2.read (%240) (by decide)).trans r1_240
  have r1_375 := (f1.read (%375) (by decide)).trans (hreg.r375)
  have r2_375 := (f2.read (%375) (by decide)).trans r1_375
  have r1_376 := (f1.read (%376) (by decide)).trans (hreg.r376)
  have r2_376 := (f2.read (%376) (by decide)).trans r1_376
  have r1_377 := (f1.read (%377) (by decide)).trans (hreg.r377)
  have r2_377 := (f2.read (%377) (by decide)).trans r1_377
  have r1_378 := (f1.read (%378) (by decide)).trans (hreg.r378)
  have r2_378 := (f2.read (%378) (by decide)).trans r1_378
  have h27 : runSlice (avx2Kernel.bb33 p) e2 27 5 (pipelineState s q false P C 1) =
      .value (e2, (pipelineState s q false P C 2)) := by
    exact prepare33_store_slice p e2 (pipelineState s q false P C 1) q.prepared (packPoint (prepare P)) (pipelineState_live s q false P C (hmem.live 1) 1) r2_240 (v836) r2_375 (v837) r2_376 (v838) r2_377 (v839) r2_378 (v840)
  have h32 : runSlice (avx2Kernel.bb33 p) e2 32 1 (pipelineState s q false P C 2) =
      .value (e2, (pipelineState s q false P C 2)) := by
    exact lifetime33_32_slice p e2 (pipelineState s q false P C 2)
  have r1_239 := (f1.read (%239) (by decide)).trans (hreg.r239)
  have r2_239 := (f2.read (%239) (by decide)).trans r1_239
  have r2_815 := (f2.read (%815) (by decide)).trans (v815)
  have h33 : runSlice (avx2Kernel.bb33 p) e2 33 1 (pipelineState s q false P C 2) =
      .value (e2, (pipelineState s q false P C 3)) := by
    exact multiply33_0_slice p e2 (pipelineState s q false P C 2) q.product q.prepared (cachePointer false q (tableRow table index)) (prepare P) (chosenCache false C) hmul (pipelineState_wf s q false P C hmem.wf 2) (pipelineState_live s q false P C (hmem.live 2) 2) (pipelineState_live s q false P C (hmem.live 1) 2) (pipelineState_live s q false P C (hmem.live 6) 2) (prepare_wide hP) (chosenCache_wide false hC) (prepared_read s q false P C (hmem.live 1)) (cache_read s q false (tableRow table index) P C hmem hcache) r2_239 r2_240 r2_815
  have r1_153 := (f1.read (%153) (by decide)).trans (hreg.r153)
  have r2_153 := (f2.read (%153) (by decide)).trans r1_153
  have h34 : runSlice (avx2Kernel.bb33 p) e2 34 1 (pipelineState s q false P C 3) =
      .value (e2, (pipelineState s q false P C 4)) := by
    exact copy33_slice p e2 (pipelineState s q false P C 3) q.prepared q.product (pipelineState_live s q false P C (hmem.live 1) 3) (pipelineState_live s q false P C (hmem.live 2) 3) (Or.inl (hmem.ne 1 2 (by decide))) r2_240 r2_239 r2_153
  have h35 : runSlice (avx2Kernel.bb33 p) e2 35 1 (pipelineState s q false P C 4) =
      .value (e2, (pipelineState s q false P C 4)) := by
    exact lifetime33_35_slice p e2 (pipelineState s q false P C 4)
  have h36 : runSlice (avx2Kernel.bb33 p) e2 36 4 (pipelineState s q false P C 4) =
      .value (e3, (pipelineState s q false P C 4)) := by
    exact load33_product4_slice p e2 (pipelineState s q false P C 4) q.prepared (packPoint (productPoint false P C)) (pipelineState_live s q false P C (hmem.live 1) 4) (copied_read s q false P C (hmem.live 1) (hmem.live 2)) r2_240 r2_375 r2_376 r2_377
  have f3 : RegisterFrame 841 845 e2 e3 :=
    load33_product4_frame e2 (packPoint (productPoint false P C))
  have v841 : e3.read (%841) = Ty.wrap (packPoint (productPoint false P C) 0) := by
    simp [e3, body33Env3, load33_product4Env, mlir_env]
  have v842 : e3.read (%842) = Ty.wrap (packPoint (productPoint false P C) 1) := by
    simp [e3, body33Env3, load33_product4Env, mlir_env]
  have v843 : e3.read (%843) = Ty.wrap (packPoint (productPoint false P C) 2) := by
    simp [e3, body33Env3, load33_product4Env, mlir_env]
  have v844 : e3.read (%844) = Ty.wrap (packPoint (productPoint false P C) 3) := by
    simp [e3, body33Env3, load33_product4Env, mlir_env]
  have h40 : runSlice (avx2Kernel.bb33 p) e3 40 4 (pipelineState s q false P C 4) =
      .value (e4, (pipelineState s q false P C 4)) := by
    exact abdc33_slice p e3 (pipelineState s q false P C 4)
  have f4 : RegisterFrame 845 849 e3 e4 :=
    abdc33_frame e3
  have r2_26 := (f2.read (%26) (by decide)).trans r1_26
  have r3_26 := (f3.read (%26) (by decide)).trans r2_26
  obtain ⟨v845, v846, v847, v848⟩ := abdc33_reads e3 (packPoint (productPoint false P C)) r3_26 (v841) (v842) (v843) (v844)
  have r3_378 := (f3.read (%378) (by decide)).trans r2_378
  have r4_378 := (f4.read (%378) (by decide)).trans r3_378
  have h44 : runSlice (avx2Kernel.bb33 p) e4 44 1 (pipelineState s q false P C 4) =
      .value (e5, (pipelineState s q false P C 4)) := by
    exact load33_product1_slice p e4 (pipelineState s q false P C 4) q.prepared (packPoint (productPoint false P C)) (pipelineState_live s q false P C (hmem.live 1) 4) (copied_read s q false P C (hmem.live 1) (hmem.live 2)) r4_378
  have f5 : RegisterFrame 849 850 e4 e5 :=
    load33_product1_frame e4 (packPoint (productPoint false P C))
  have v849 : e5.read (%849) = Ty.wrap (packPoint (productPoint false P C) 4) := by
    simp [e5, body33Env5, load33_product1Env, mlir_env]
  have h45 : runSlice (avx2Kernel.bb33 p) e5 45 21 (pipelineState s q false P C 4) =
      .value (e6, (pipelineState s q false P C 4)) := by
    exact difference33_slice p e5 (pipelineState s q false P C 4)
  have f6 : RegisterFrame 850 871 e5 e6 :=
    difference33_frame e5
  have r4_841 := (f4.read (%841) (by decide)).trans (v841)
  have r5_841 := (f5.read (%841) (by decide)).trans r4_841
  have r4_842 := (f4.read (%842) (by decide)).trans (v842)
  have r5_842 := (f5.read (%842) (by decide)).trans r4_842
  have r4_843 := (f4.read (%843) (by decide)).trans (v843)
  have r5_843 := (f5.read (%843) (by decide)).trans r4_843
  have r4_844 := (f4.read (%844) (by decide)).trans (v844)
  have r5_844 := (f5.read (%844) (by decide)).trans r4_844
  have r5_845 := (f5.read (%845) (by decide)).trans (v845)
  have r5_846 := (f5.read (%846) (by decide)).trans (v846)
  have r5_847 := (f5.read (%847) (by decide)).trans (v847)
  have r5_848 := (f5.read (%848) (by decide)).trans (v848)
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
  have cdifference33 : Constants e5 := ⟨r5_26, r5_135, r5_152, r5_170, r5_187, r5_204, r5_221⟩
  have idifference33 : difference33Inputs e5 (packPoint (productPoint false P C)) := ⟨r5_841, r5_842, r5_843, r5_844, (v849), r5_845, r5_846, r5_847, r5_848⟩
  have v866 := difference33_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference33 idifference33 0
  have v867 := difference33_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference33 idifference33 1
  have v868 := difference33_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference33 idifference33 2
  have v869 := difference33_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference33 idifference33 3
  have v870 := difference33_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference33 idifference33 4
  have h66 : runSlice (avx2Kernel.bb33 p) e6 66 1 (pipelineState s q false P C 4) =
      .value (e6, (pipelineState s q false P C 4)) := by
    exact lifetime33_66_slice p e6 (pipelineState s q false P C 4)
  have h67 : runSlice (avx2Kernel.bb33 p) e6 67 5 (pipelineState s q false P C 4) =
      .value (e7, (pipelineState s q false P C 4)) := by
    exact adda33_slice p e6 (pipelineState s q false P C 4)
  have f7 : RegisterFrame 871 876 e6 e7 :=
    adda33_frame e6
  have r6_26 := (f6.read (%26) (by decide)).trans r5_26
  have r6_135 := (f6.read (%135) (by decide)).trans r5_135
  have r6_152 := (f6.read (%152) (by decide)).trans r5_152
  have r6_170 := (f6.read (%170) (by decide)).trans r5_170
  have r6_187 := (f6.read (%187) (by decide)).trans r5_187
  have r6_204 := (f6.read (%204) (by decide)).trans r5_204
  have r6_221 := (f6.read (%221) (by decide)).trans r5_221
  have cadda33 : Constants e6 := ⟨r6_26, r6_135, r6_152, r6_170, r6_187, r6_204, r6_221⟩
  have iadda33 : adda33Inputs e6 (packPoint (differencePoint false P C)) := ⟨(v866), (v867), (v868), (v869), (v870)⟩
  have v871 := adda33_field e6 (differencePoint false P C) cadda33 iadda33 0
  have v872 := adda33_field e6 (differencePoint false P C) cadda33 iadda33 1
  have v873 := adda33_field e6 (differencePoint false P C) cadda33 iadda33 2
  have v874 := adda33_field e6 (differencePoint false P C) cadda33 iadda33 3
  have v875 := adda33_field e6 (differencePoint false P C) cadda33 iadda33 4
  have r1_238 := (f1.read (%238) (by decide)).trans (hreg.r238)
  have r2_238 := (f2.read (%238) (by decide)).trans r1_238
  have r3_238 := (f3.read (%238) (by decide)).trans r2_238
  have r4_238 := (f4.read (%238) (by decide)).trans r3_238
  have r5_238 := (f5.read (%238) (by decide)).trans r4_238
  have r6_238 := (f6.read (%238) (by decide)).trans r5_238
  have r7_238 := (f7.read (%238) (by decide)).trans r6_238
  have r1_379 := (f1.read (%379) (by decide)).trans (hreg.r379)
  have r2_379 := (f2.read (%379) (by decide)).trans r1_379
  have r3_379 := (f3.read (%379) (by decide)).trans r2_379
  have r4_379 := (f4.read (%379) (by decide)).trans r3_379
  have r5_379 := (f5.read (%379) (by decide)).trans r4_379
  have r6_379 := (f6.read (%379) (by decide)).trans r5_379
  have r7_379 := (f7.read (%379) (by decide)).trans r6_379
  have r1_380 := (f1.read (%380) (by decide)).trans (hreg.r380)
  have r2_380 := (f2.read (%380) (by decide)).trans r1_380
  have r3_380 := (f3.read (%380) (by decide)).trans r2_380
  have r4_380 := (f4.read (%380) (by decide)).trans r3_380
  have r5_380 := (f5.read (%380) (by decide)).trans r4_380
  have r6_380 := (f6.read (%380) (by decide)).trans r5_380
  have r7_380 := (f7.read (%380) (by decide)).trans r6_380
  have r1_381 := (f1.read (%381) (by decide)).trans (hreg.r381)
  have r2_381 := (f2.read (%381) (by decide)).trans r1_381
  have r3_381 := (f3.read (%381) (by decide)).trans r2_381
  have r4_381 := (f4.read (%381) (by decide)).trans r3_381
  have r5_381 := (f5.read (%381) (by decide)).trans r4_381
  have r6_381 := (f6.read (%381) (by decide)).trans r5_381
  have r7_381 := (f7.read (%381) (by decide)).trans r6_381
  have r1_382 := (f1.read (%382) (by decide)).trans (hreg.r382)
  have r2_382 := (f2.read (%382) (by decide)).trans r1_382
  have r3_382 := (f3.read (%382) (by decide)).trans r2_382
  have r4_382 := (f4.read (%382) (by decide)).trans r3_382
  have r5_382 := (f5.read (%382) (by decide)).trans r4_382
  have r6_382 := (f6.read (%382) (by decide)).trans r5_382
  have r7_382 := (f7.read (%382) (by decide)).trans r6_382
  have h72 : runSlice (avx2Kernel.bb33 p) e7 72 5 (pipelineState s q false P C 4) =
      .value (e7, (pipelineState s q false P C 5)) := by
    exact adda33_store_slice p e7 (pipelineState s q false P C 4) q.left (packPoint (leftPoint false P C)) (pipelineState_live s q false P C (hmem.live 3) 4) r7_238 (v871) r7_379 (v872) r7_380 (v873) r7_381 (v874) r7_382 (v875)
  have h77 : runSlice (avx2Kernel.bb33 p) e7 77 1 (pipelineState s q false P C 5) =
      .value (e7, (pipelineState s q false P C 5)) := by
    exact lifetime33_77_slice p e7 (pipelineState s q false P C 5)
  have h78 : runSlice (avx2Kernel.bb33 p) e7 78 5 (pipelineState s q false P C 5) =
      .value (e8, (pipelineState s q false P C 5)) := by
    exact cbcb33_slice p e7 (pipelineState s q false P C 5)
  have f8 : RegisterFrame 876 881 e7 e8 :=
    cbcb33_frame e7
  have r7_866 := (f7.read (%866) (by decide)).trans (v866)
  have r7_867 := (f7.read (%867) (by decide)).trans (v867)
  have r7_868 := (f7.read (%868) (by decide)).trans (v868)
  have r7_869 := (f7.read (%869) (by decide)).trans (v869)
  have r7_870 := (f7.read (%870) (by decide)).trans (v870)
  have r7_26 := (f7.read (%26) (by decide)).trans r6_26
  have r7_135 := (f7.read (%135) (by decide)).trans r6_135
  have r7_152 := (f7.read (%152) (by decide)).trans r6_152
  have r7_170 := (f7.read (%170) (by decide)).trans r6_170
  have r7_187 := (f7.read (%187) (by decide)).trans r6_187
  have r7_204 := (f7.read (%204) (by decide)).trans r6_204
  have r7_221 := (f7.read (%221) (by decide)).trans r6_221
  have ccbcb33 : Constants e7 := ⟨r7_26, r7_135, r7_152, r7_170, r7_187, r7_204, r7_221⟩
  have icbcb33 : cbcb33Inputs e7 (packPoint (differencePoint false P C)) := ⟨r7_866, r7_867, r7_868, r7_869, r7_870⟩
  have v876 := cbcb33_field e7 (differencePoint false P C) ccbcb33 icbcb33 0
  have v877 := cbcb33_field e7 (differencePoint false P C) ccbcb33 icbcb33 1
  have v878 := cbcb33_field e7 (differencePoint false P C) ccbcb33 icbcb33 2
  have v879 := cbcb33_field e7 (differencePoint false P C) ccbcb33 icbcb33 3
  have v880 := cbcb33_field e7 (differencePoint false P C) ccbcb33 icbcb33 4
  have r1_237 := (f1.read (%237) (by decide)).trans (hreg.r237)
  have r2_237 := (f2.read (%237) (by decide)).trans r1_237
  have r3_237 := (f3.read (%237) (by decide)).trans r2_237
  have r4_237 := (f4.read (%237) (by decide)).trans r3_237
  have r5_237 := (f5.read (%237) (by decide)).trans r4_237
  have r6_237 := (f6.read (%237) (by decide)).trans r5_237
  have r7_237 := (f7.read (%237) (by decide)).trans r6_237
  have r8_237 := (f8.read (%237) (by decide)).trans r7_237
  have r1_383 := (f1.read (%383) (by decide)).trans (hreg.r383)
  have r2_383 := (f2.read (%383) (by decide)).trans r1_383
  have r3_383 := (f3.read (%383) (by decide)).trans r2_383
  have r4_383 := (f4.read (%383) (by decide)).trans r3_383
  have r5_383 := (f5.read (%383) (by decide)).trans r4_383
  have r6_383 := (f6.read (%383) (by decide)).trans r5_383
  have r7_383 := (f7.read (%383) (by decide)).trans r6_383
  have r8_383 := (f8.read (%383) (by decide)).trans r7_383
  have r1_384 := (f1.read (%384) (by decide)).trans (hreg.r384)
  have r2_384 := (f2.read (%384) (by decide)).trans r1_384
  have r3_384 := (f3.read (%384) (by decide)).trans r2_384
  have r4_384 := (f4.read (%384) (by decide)).trans r3_384
  have r5_384 := (f5.read (%384) (by decide)).trans r4_384
  have r6_384 := (f6.read (%384) (by decide)).trans r5_384
  have r7_384 := (f7.read (%384) (by decide)).trans r6_384
  have r8_384 := (f8.read (%384) (by decide)).trans r7_384
  have r1_385 := (f1.read (%385) (by decide)).trans (hreg.r385)
  have r2_385 := (f2.read (%385) (by decide)).trans r1_385
  have r3_385 := (f3.read (%385) (by decide)).trans r2_385
  have r4_385 := (f4.read (%385) (by decide)).trans r3_385
  have r5_385 := (f5.read (%385) (by decide)).trans r4_385
  have r6_385 := (f6.read (%385) (by decide)).trans r5_385
  have r7_385 := (f7.read (%385) (by decide)).trans r6_385
  have r8_385 := (f8.read (%385) (by decide)).trans r7_385
  have r1_386 := (f1.read (%386) (by decide)).trans (hreg.r386)
  have r2_386 := (f2.read (%386) (by decide)).trans r1_386
  have r3_386 := (f3.read (%386) (by decide)).trans r2_386
  have r4_386 := (f4.read (%386) (by decide)).trans r3_386
  have r5_386 := (f5.read (%386) (by decide)).trans r4_386
  have r6_386 := (f6.read (%386) (by decide)).trans r5_386
  have r7_386 := (f7.read (%386) (by decide)).trans r6_386
  have r8_386 := (f8.read (%386) (by decide)).trans r7_386
  have h83 : runSlice (avx2Kernel.bb33 p) e8 83 5 (pipelineState s q false P C 5) =
      .value (e8, (pipelineState s q false P C 6)) := by
    exact cbcb33_store_slice p e8 (pipelineState s q false P C 5) q.right (packPoint (rightPoint false P C)) (pipelineState_live s q false P C (hmem.live 4) 5) r8_237 (v876) r8_383 (v877) r8_384 (v878) r8_385 (v879) r8_386 (v880)
  have r1_260 := (f1.read (%260) (by decide)).trans (hreg.r260)
  have r2_260 := (f2.read (%260) (by decide)).trans r1_260
  have r3_260 := (f3.read (%260) (by decide)).trans r2_260
  have r4_260 := (f4.read (%260) (by decide)).trans r3_260
  have r5_260 := (f5.read (%260) (by decide)).trans r4_260
  have r6_260 := (f6.read (%260) (by decide)).trans r5_260
  have r7_260 := (f7.read (%260) (by decide)).trans r6_260
  have r8_260 := (f8.read (%260) (by decide)).trans r7_260
  have r8_238 := (f8.read (%238) (by decide)).trans r7_238
  have h88 : runSlice (avx2Kernel.bb33 p) e8 88 1 (pipelineState s q false P C 6) =
      .value (e8, (pipelineState s q false P C 7)) := by
    exact multiply33_1_slice p e8 (pipelineState s q false P C 6) q.output q.left q.right (leftPoint false P C) (rightPoint false P C) hmul (pipelineState_wf s q false P C hmem.wf 6) (pipelineState_live s q false P C (hmem.live 0) 6) (pipelineState_live s q false P C (hmem.live 3) 6) (pipelineState_live s q false P C (hmem.live 4) 6) (leftPoint_wide false hP hC) (rightPoint_wide false hP hC) (factors_read s q false (tableRow table index) P C hmem).1 (factors_read s q false (tableRow table index) P C hmem).2 r8_260 r8_238 r8_237
  have h89 : runSlice (avx2Kernel.bb33 p) e8 89 3 (pipelineState s q false P C 7) =
      .value (e8, (pipelineState s q false P C 7)) := by
    exact lifetime33_89_slice p e8 (pipelineState s q false P C 7)
  have r1_387 := (f1.read (%387) (by decide)).trans (hreg.r387)
  have r2_387 := (f2.read (%387) (by decide)).trans r1_387
  have r3_387 := (f3.read (%387) (by decide)).trans r2_387
  have r4_387 := (f4.read (%387) (by decide)).trans r3_387
  have r5_387 := (f5.read (%387) (by decide)).trans r4_387
  have r6_387 := (f6.read (%387) (by decide)).trans r5_387
  have r7_387 := (f7.read (%387) (by decide)).trans r6_387
  have r8_387 := (f8.read (%387) (by decide)).trans r7_387
  have r1_388 := (f1.read (%388) (by decide)).trans (hreg.r388)
  have r2_388 := (f2.read (%388) (by decide)).trans r1_388
  have r3_388 := (f3.read (%388) (by decide)).trans r2_388
  have r4_388 := (f4.read (%388) (by decide)).trans r3_388
  have r5_388 := (f5.read (%388) (by decide)).trans r4_388
  have r6_388 := (f6.read (%388) (by decide)).trans r5_388
  have r7_388 := (f7.read (%388) (by decide)).trans r6_388
  have r8_388 := (f8.read (%388) (by decide)).trans r7_388
  have r1_389 := (f1.read (%389) (by decide)).trans (hreg.r389)
  have r2_389 := (f2.read (%389) (by decide)).trans r1_389
  have r3_389 := (f3.read (%389) (by decide)).trans r2_389
  have r4_389 := (f4.read (%389) (by decide)).trans r3_389
  have r5_389 := (f5.read (%389) (by decide)).trans r4_389
  have r6_389 := (f6.read (%389) (by decide)).trans r5_389
  have r7_389 := (f7.read (%389) (by decide)).trans r6_389
  have r8_389 := (f8.read (%389) (by decide)).trans r7_389
  have r1_390 := (f1.read (%390) (by decide)).trans (hreg.r390)
  have r2_390 := (f2.read (%390) (by decide)).trans r1_390
  have r3_390 := (f3.read (%390) (by decide)).trans r2_390
  have r4_390 := (f4.read (%390) (by decide)).trans r3_390
  have r5_390 := (f5.read (%390) (by decide)).trans r4_390
  have r6_390 := (f6.read (%390) (by decide)).trans r5_390
  have r7_390 := (f7.read (%390) (by decide)).trans r6_390
  have r8_390 := (f8.read (%390) (by decide)).trans r7_390
  have h92 : runSlice (avx2Kernel.bb33 p) e8 92 5 (pipelineState s q false P C 7) =
      .value (e9, (pipelineState s q false P C 7)) := by
    exact load33_result_slice p e8 (pipelineState s q false P C 7) q.output (packPoint (resultPoint false P C)) (pipelineState_live s q false P C (hmem.live 0) 7) (result_read s q false P C (hmem.live 0)) r8_260 r8_387 r8_388 r8_389 r8_390
  have f9 : RegisterFrame 881 886 e8 e9 :=
    load33_result_frame e8 (packPoint (resultPoint false P C))
  have v881 : e9.read (%881) = Ty.wrap (packPoint (resultPoint false P C) 0) := by
    simp [e9, body33Env9, load33_resultEnv, mlir_env]
  have v882 : e9.read (%882) = Ty.wrap (packPoint (resultPoint false P C) 1) := by
    simp [e9, body33Env9, load33_resultEnv, mlir_env]
  have v883 : e9.read (%883) = Ty.wrap (packPoint (resultPoint false P C) 2) := by
    simp [e9, body33Env9, load33_resultEnv, mlir_env]
  have v884 : e9.read (%884) = Ty.wrap (packPoint (resultPoint false P C) 3) := by
    simp [e9, body33Env9, load33_resultEnv, mlir_env]
  have v885 : e9.read (%885) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
    simp [e9, body33Env9, load33_resultEnv, mlir_env]
  have h97 : runSlice (avx2Kernel.bb33 p) e9 97 1 (pipelineState s q false P C 7) =
      .value (e9, (pipelineState s q false P C 7)) := by
    exact lifetime33_97_slice p e9 (pipelineState s q false P C 7)
  calc
    (avx2Kernel.bb33 p).runBodyFrom E 0 (pipelineState s q false P C 1) = (avx2Kernel.bb33 p).runBodyFrom e1 1 (pipelineState s q false P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h0
    _ = (avx2Kernel.bb33 p).runBodyFrom e1 2 (pipelineState s q false P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h1
    _ = (avx2Kernel.bb33 p).runBodyFrom e2 27 (pipelineState s q false P C 1) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h2
    _ = (avx2Kernel.bb33 p).runBodyFrom e2 32 (pipelineState s q false P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h27
    _ = (avx2Kernel.bb33 p).runBodyFrom e2 33 (pipelineState s q false P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h32
    _ = (avx2Kernel.bb33 p).runBodyFrom e2 34 (pipelineState s q false P C 3) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h33
    _ = (avx2Kernel.bb33 p).runBodyFrom e2 35 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h34
    _ = (avx2Kernel.bb33 p).runBodyFrom e2 36 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h35
    _ = (avx2Kernel.bb33 p).runBodyFrom e3 40 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h36
    _ = (avx2Kernel.bb33 p).runBodyFrom e4 44 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h40
    _ = (avx2Kernel.bb33 p).runBodyFrom e5 45 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h44
    _ = (avx2Kernel.bb33 p).runBodyFrom e6 66 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h45
    _ = (avx2Kernel.bb33 p).runBodyFrom e6 67 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h66
    _ = (avx2Kernel.bb33 p).runBodyFrom e7 72 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h67
    _ = (avx2Kernel.bb33 p).runBodyFrom e7 77 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h72
    _ = (avx2Kernel.bb33 p).runBodyFrom e7 78 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h77
    _ = (avx2Kernel.bb33 p).runBodyFrom e8 83 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h78
    _ = (avx2Kernel.bb33 p).runBodyFrom e8 88 (pipelineState s q false P C 6) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h83
    _ = (avx2Kernel.bb33 p).runBodyFrom e8 89 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h88
    _ = (avx2Kernel.bb33 p).runBodyFrom e8 92 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h89
    _ = (avx2Kernel.bb33 p).runBodyFrom e9 97 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h92
    _ = (avx2Kernel.bb33 p).runBodyFrom e9 98 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h97
    _ = .value (e9, (pipelineState s q false P C 7)) := by
      rw [BasicBlock.runBodyFrom_done (hpos := by simp [avx2Kernel.bb33])]
      rfl

def exit33Env (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪avx2Kernel.Γ⟫ :=
  (body33Env9 E q table index P C)[%805 := Ty.wrap (packPoint (resultPoint false P C) 3), %806 := Ty.wrap (packPoint (resultPoint false P C) 2), %807 := Ty.wrap (packPoint (resultPoint false P C) 1), %808 := Ty.wrap (packPoint (resultPoint false P C) 0), %809 := Ty.wrap (packPoint (resultPoint false P C) 4)]

theorem exit33_frame (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (exit33Env E q table index P C) := by
  unfold exit33Env
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  apply RegisterFrame.write (hd := by decide)
  exact body33_frame E q table index P C

theorem exit33_point (E : ⟪avx2Kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (exit33Env E q table index P C).read (%805) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧ (exit33Env E q table index P C).read (%806) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧ (exit33Env E q table index P C).read (%807) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧ (exit33Env E q table index P C).read (%808) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧ (exit33Env E q table index P C).read (%809) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
  simp [exit33Env, mlir_env]

theorem block33_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input33 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb33 p).run avx2Kernel.blockParams E s =
      .value ((exit33Env E q table index P C, .inr 30), pipelineState s q false P C 7) := by
  have hb := body33_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC
  obtain ⟨v0, v1, v2, v3, v4⟩ := body33_output E q table index P C
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq, hb, PoisonOr.value_bind]
  simp [avx2Kernel.bb33, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, DoubleBase.ExecutionAvx2.kernel_params30,
    exit33Env, v0, v1, v2, v3, v4, EffectM.pure_eq]

theorem block33_run (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input33 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) (g : Avx2CFG.Globals) :
    (avx2Kernel p g).runFrom E 33 s =
      (avx2Kernel p g).runFrom (exit33Env E q table index P C) 30 (pipelineState s q false P C 7) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 33 = avx2Kernel.bb33 p from rfl,
    block33_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC]
  simp only [PoisonOr.value_bind, Func.continue]

theorem block33_memoryFrame (s : GlobalState) (q : Scratch) (P C : Point) (hs : s.WF) :
    OutputFrame q s (pipelineState s q false P C 7) := pipelineState_frame s q false P C hs 7

theorem block33_reduced {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointReduced (resultPoint false P C) := resultPoint_reduced false hP hC

theorem block33_field {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (resultPoint false P C) = PointArithmetic.avx2AddCached (pointValue P)
      (pointValue C) := by
  simpa [resultPoint_eq] using add_refines hP (pointReduced_wide hC)

/-- Field readback from the actual final output-memory state. -/
theorem block33_memoryPoint (s : GlobalState) (q : Scratch) (P C : Point)
    (hr : Reduce64.Execution.SmallRange s.mem q.output 160)
    (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q false P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (pointValue C) := by
  rw [readPoint_of_packed (pointReduced_wide (block33_reduced hP hC)) _ _
    (result_read s q false P C hr)]
  exact block33_field hP hC

/-- One local ladder transition: exact successor, concrete packed output,
preserved static registers/cursor, allocation and byte frame, restored bounds,
and field correctness. It assumes no enclosing iteration or ladder theorem. -/
theorem block33_endpoint (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (q : Scratch) (table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hreg : Input33 E q table index P)
    (hmem : MemoryReady s q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache : Avx2FieldMul.Execution.readBlocks s.mem (tableRow table index) = packPoint C)
    (hP : pointReduced P) (hC : pointReduced C) :
    (avx2Kernel.bb33 p).run avx2Kernel.blockParams E s =
      .value ((exit33Env E q table index P C, .inr 30), pipelineState s q false P C 7) ∧
    OutputFrame q s (pipelineState s q false P C 7) ∧
    RegisterFrame 427 avx2Kernel.Γ.n E (exit33Env E q table index P C) ∧
    Avx2FieldMul.Execution.readBlocks (pipelineState s q false P C 7).mem q.output = packPoint (resultPoint false P C) ∧
    pointReduced (resultPoint false P C) ∧
    (exit33Env E q table index P C).read (%805) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧ (exit33Env E q table index P C).read (%806) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧ (exit33Env E q table index P C).read (%807) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧ (exit33Env E q table index P C).read (%808) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧ (exit33Env E q table index P C).read (%809) = Ty.wrap (packPoint (resultPoint false P C) 4) ∧
    pointValue (Avx2PointAdd.Execution.readPoint (pipelineState s q false P C 7).mem q.output) =
      PointArithmetic.avx2AddCached (pointValue P)
        (pointValue C) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := exit33_point E q table index P C
  exact ⟨block33_correct p E s q table index bytes P C hmul hreg hmem htable hindex hcache hP hC,
    block33_memoryFrame s q P C hmem.wf, exit33_frame E q table index P C,
    result_read s q false P C (hmem.live 0), block33_reduced hP hC,
    v0, v1, v2, v3, v4, block33_memoryPoint s q P C (hmem.live 0) hP hC⟩

end Agave.Ed25519.Avx2PointAdd.CFG
