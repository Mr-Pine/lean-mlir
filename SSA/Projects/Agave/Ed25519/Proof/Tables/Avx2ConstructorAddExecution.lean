import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddPrepare
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddPhases
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddPrefix

/-! Exact positive-add body of the unchanged AVX2 table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Add
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice abdcVec)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

structure Input (E : ⟪kernel.Γ⟫) (q : Scratch)
    (fixed table : Pointer) (index : Fin 64) : Prop where
  constants : Constants E
  one : E.read (%22) = .value 1#64
  fixed : E.read (%359) = .value fixed
  r195 : E.read (%195) = .value 160#64
  r352 : E.read (%352) = .value q.right
  r353 : E.read (%353) = .value q.left
  r354 : E.read (%354) = .value q.product
  r355 : E.read (%355) = .value q.prepared
  r358 : E.read (%358) = .value q.output
  r360 : E.read (%360) = .value table
  r787 : E.read (%787) = .value (q.prepared.add 32#64)
  r788 : E.read (%788) = .value (q.prepared.add 64#64)
  r789 : E.read (%789) = .value (q.prepared.add 96#64)
  r790 : E.read (%790) = .value (q.prepared.add 128#64)
  r791 : E.read (%791) = .value (q.left.add 32#64)
  r792 : E.read (%792) = .value (q.left.add 64#64)
  r793 : E.read (%793) = .value (q.left.add 96#64)
  r794 : E.read (%794) = .value (q.left.add 128#64)
  r795 : E.read (%795) = .value (q.right.add 32#64)
  r796 : E.read (%796) = .value (q.right.add 64#64)
  r797 : E.read (%797) = .value (q.right.add 96#64)
  r798 : E.read (%798) = .value (q.right.add 128#64)
  r799 : E.read (%799) = .value (q.output.add 32#64)
  r800 : E.read (%800) = .value (q.output.add 64#64)
  r801 : E.read (%801) = .value (q.output.add 96#64)
  r802 : E.read (%802) = .value (q.output.add 128#64)
  r803 : E.read (%803) = .value (BitVec.ofNat 64 index.val)

def bodyEnv1 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  rowEnv (E) table index

def bodyEnv2 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  prepareEnv (bodyEnv1 E q table index P C) (packPoint P)

def bodyEnv3 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  load_product4Env (bodyEnv2 E q table index P C) (packPoint (productPoint false P C))

def bodyEnv4 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  abdcEnv (bodyEnv3 E q table index P C)

def bodyEnv5 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  load_product1Env (bodyEnv4 E q table index P C) (packPoint (productPoint false P C))

def bodyEnv6 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  differenceEnv (bodyEnv5 E q table index P C)

def bodyEnv7 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  addaEnv (bodyEnv6 E q table index P C)

def bodyEnv8 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  cbcbEnv (bodyEnv7 E q table index P C)

def bodyEnv9 (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) : ⟪kernel.Γ⟫ :=
  load_resultEnv (bodyEnv8 E q table index P C) (packPoint (resultPoint false P C))

theorem body_output (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    (bodyEnv9 E q table index P C).read (%876) = Ty.wrap (packPoint (resultPoint false P C) 0) ∧
    (bodyEnv9 E q table index P C).read (%877) = Ty.wrap (packPoint (resultPoint false P C) 1) ∧
    (bodyEnv9 E q table index P C).read (%878) = Ty.wrap (packPoint (resultPoint false P C) 2) ∧
    (bodyEnv9 E q table index P C).read (%879) = Ty.wrap (packPoint (resultPoint false P C) 3) ∧
    (bodyEnv9 E q table index P C).read (%880) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
  exact load_result_reads _ _

theorem body_frame (E : ⟪kernel.Γ⟫) (q : Scratch)
    (table : Pointer) (index : Fin 64) (P C : Point) :
    RegisterFrame 804 kernel.Γ.n E (bodyEnv9 E q table index P C) := by
  have f1 := (row_frame (E) table index).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f2 := (prepare_frame (bodyEnv1 E q table index P C) (packPoint P)).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f3 := (load_product4_frame (bodyEnv2 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f4 := (abdc_frame (bodyEnv3 E q table index P C)).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f5 := (load_product1_frame (bodyEnv4 E q table index P C) (packPoint (productPoint false P C))).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f6 := (difference_frame (bodyEnv5 E q table index P C)).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f7 := (adda_frame (bodyEnv6 E q table index P C)).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f8 := (cbcb_frame (bodyEnv7 E q table index P C)).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  have f9 := (load_result_frame (bodyEnv8 E q table index P C) (packPoint (resultPoint false P C))).weaken (lo' := 804) (hi' := kernel.Γ.n) (by decide) (by decide)
  exact (((((((((RegisterFrame.refl 804 kernel.Γ.n E).trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9

theorem body_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s0 : GlobalState)
    (q : Scratch) (fixed table : Pointer) (index : Fin 64) (bytes : Nat) (P C : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call1)
    (hreg : Input E q fixed table index)
    (hmem0 : MemoryReady s0 q (tableRow table index))
    (htable : Reduce64.Execution.SmallRange s0.mem table bytes)
    (hindex : 160 * index.val + 160 ≤ bytes)
    (hcache0 : Avx2FieldMul.Execution.readBlocks s0.mem (tableRow table index) = packPoint C)
    (hfixed : Reduce64.Execution.SmallRange s0.mem fixed 160)
    (hfixedRead : Avx2FieldMul.Execution.readBlocks s0.mem fixed = packPoint P)
    (hdisjoint : q.prepared.id ≠ fixed.id)
    (hP : pointReduced P) (hC : pointReduced C) :
    (kernel.bb2 p).runBodyFrom E 0 s0 =
      (kernel.bb2 p).runBodyFrom (bodyEnv9 E q table index P C) 105
        (resultState s0 q fixed P C) := by
  let s := copyInput s0 q fixed
  have hmem := copyInput_ready s0 q fixed (tableRow table index) hmem0
  have hcache := (copyInput_cached s0 q fixed (tableRow table index) hmem0).trans hcache0
  have hloaded := (copyInput_read s0 q fixed (hmem0.live 1) hfixed).trans hfixedRead
  let e1 := bodyEnv1 E q table index P C
  let e2 := bodyEnv2 E q table index P C
  let e3 := bodyEnv3 E q table index P C
  let e4 := bodyEnv4 E q table index P C
  let e5 := bodyEnv5 E q table index P C
  let e6 := bodyEnv6 E q table index P C
  let e7 := bodyEnv7 E q table index P C
  let e8 := bodyEnv8 E q table index P C
  let e9 := bodyEnv9 E q table index P C
  have h0 : runSlice (kernel.bb2 p) E 0 4 s0 = .value (e1, s0) :=
    row_slice p E s0 table index bytes htable hindex hreg.r360 hreg.r803 hreg.one
  have f1 : RegisterFrame 804 806 E e1 := row_frame E table index
  have v805 : e1.read (%805) = .value (tableRow table index) := by
    simp [e1, bodyEnv1, rowEnv, mlir_env]
  have hcopy : runSlice (kernel.bb2 p) e1 4 1 s0 = .value (e1, s) := by
    exact initialCopy_slice p e1 s0 q.prepared fixed (hmem0.live 1) hfixed
      (Or.inl hdisjoint) ((f1.read (%355) (by decide)).trans hreg.r355)
      ((f1.read (%359) (by decide)).trans hreg.fixed)
      ((f1.read (%195) (by decide)).trans hreg.r195)
  have h2 : runSlice (kernel.bb2 p) e1 5 30 s = .value (e2, s) := by
    exact prepare_slice p e1 s q.prepared (packPoint P) (hmem.live 1) hloaded
      ((f1.read (%355) (by decide)).trans hreg.r355)
      ((f1.read (%787) (by decide)).trans hreg.r787)
      ((f1.read (%788) (by decide)).trans hreg.r788)
      ((f1.read (%789) (by decide)).trans hreg.r789)
      ((f1.read (%790) (by decide)).trans hreg.r790)
  have f2 : RegisterFrame 806 836 e1 e2 :=
    prepare_frame e1 (packPoint P)
  have r1_31 := (f1.read (%31) (by decide)).trans (hreg.constants.poison)
  have r1_52 := (f1.read (%52) (by decide)).trans (hreg.constants.prepare0)
  have r1_70 := (f1.read (%70) (by decide)).trans (hreg.constants.prepareN)
  have r1_332 := (f1.read (%332) (by decide)).trans (hreg.constants.difference0)
  have r1_349 := (f1.read (%349) (by decide)).trans (hreg.constants.differenceN)
  have cprepare : Constants e1 := ⟨r1_31, r1_52, r1_70, r1_332, r1_349⟩
  have v831 := prepare_field e1 P hP cprepare 0
  have v832 := prepare_field e1 P hP cprepare 1
  have v833 := prepare_field e1 P hP cprepare 2
  have v834 := prepare_field e1 P hP cprepare 3
  have v835 := prepare_field e1 P hP cprepare 4
  have r1_355 := (f1.read (%355) (by decide)).trans (hreg.r355)
  have r2_355 := (f2.read (%355) (by decide)).trans r1_355
  have r1_787 := (f1.read (%787) (by decide)).trans (hreg.r787)
  have r2_787 := (f2.read (%787) (by decide)).trans r1_787
  have r1_788 := (f1.read (%788) (by decide)).trans (hreg.r788)
  have r2_788 := (f2.read (%788) (by decide)).trans r1_788
  have r1_789 := (f1.read (%789) (by decide)).trans (hreg.r789)
  have r2_789 := (f2.read (%789) (by decide)).trans r1_789
  have r1_790 := (f1.read (%790) (by decide)).trans (hreg.r790)
  have r2_790 := (f2.read (%790) (by decide)).trans r1_790
  have h27 : runSlice (kernel.bb2 p) e2 35 5 (pipelineState s q false P C 1) =
      .value (e2, (pipelineState s q false P C 2)) := by
    exact prepare_store_slice p e2 (pipelineState s q false P C 1) q.prepared (packPoint (prepare P)) (pipelineState_live s q false P C (hmem.live 1) 1) r2_355 (v831) r2_787 (v832) r2_788 (v833) r2_789 (v834) r2_790 (v835)
  have h32 : runSlice (kernel.bb2 p) e2 40 1 (pipelineState s q false P C 2) =
      .value (e2, (pipelineState s q false P C 2)) := by
    exact lifetime_40_slice p e2 (pipelineState s q false P C 2)
  have r1_354 := (f1.read (%354) (by decide)).trans (hreg.r354)
  have r2_354 := (f2.read (%354) (by decide)).trans r1_354
  have r2_805 := (f2.read (%805) (by decide)).trans (v805)
  have h33 : runSlice (kernel.bb2 p) e2 41 1 (pipelineState s q false P C 2) =
      .value (e2, (pipelineState s q false P C 3)) := by
    exact multiply_0_slice p e2 (pipelineState s q false P C 2) q.product q.prepared (cachePointer false q (tableRow table index)) (prepare P) (chosenCache false C) hmul (pipelineState_wf s q false P C hmem.wf 2) (pipelineState_live s q false P C (hmem.live 2) 2) (pipelineState_live s q false P C (hmem.live 1) 2) (pipelineState_live s q false P C (hmem.live 6) 2) (prepare_wide hP) (chosenCache_wide false hC) (prepared_read s q false P C (hmem.live 1)) (cache_read s q false (tableRow table index) P C hmem hcache) r2_354 r2_355 r2_805
  have r1_195 := (f1.read (%195) (by decide)).trans (hreg.r195)
  have r2_195 := (f2.read (%195) (by decide)).trans r1_195
  have h34 : runSlice (kernel.bb2 p) e2 42 1 (pipelineState s q false P C 3) =
      .value (e2, (pipelineState s q false P C 4)) := by
    exact copy_slice p e2 (pipelineState s q false P C 3) q.prepared q.product (pipelineState_live s q false P C (hmem.live 1) 3) (pipelineState_live s q false P C (hmem.live 2) 3) (Or.inl (hmem.ne 1 2 (by decide))) r2_355 r2_354 r2_195
  have h35 : runSlice (kernel.bb2 p) e2 43 1 (pipelineState s q false P C 4) =
      .value (e2, (pipelineState s q false P C 4)) := by
    exact lifetime_43_slice p e2 (pipelineState s q false P C 4)
  have h36 : runSlice (kernel.bb2 p) e2 44 4 (pipelineState s q false P C 4) =
      .value (e3, (pipelineState s q false P C 4)) := by
    exact load_product4_slice p e2 (pipelineState s q false P C 4) q.prepared (packPoint (productPoint false P C)) (pipelineState_live s q false P C (hmem.live 1) 4) (copied_read s q false P C (hmem.live 1) (hmem.live 2)) r2_355 r2_787 r2_788 r2_789
  have f3 : RegisterFrame 836 840 e2 e3 :=
    load_product4_frame e2 (packPoint (productPoint false P C))
  have v836 : e3.read (%836) = Ty.wrap (packPoint (productPoint false P C) 0) := by
    simp [e3, bodyEnv3, load_product4Env, mlir_env]
  have v837 : e3.read (%837) = Ty.wrap (packPoint (productPoint false P C) 1) := by
    simp [e3, bodyEnv3, load_product4Env, mlir_env]
  have v838 : e3.read (%838) = Ty.wrap (packPoint (productPoint false P C) 2) := by
    simp [e3, bodyEnv3, load_product4Env, mlir_env]
  have v839 : e3.read (%839) = Ty.wrap (packPoint (productPoint false P C) 3) := by
    simp [e3, bodyEnv3, load_product4Env, mlir_env]
  have h40 : runSlice (kernel.bb2 p) e3 48 4 (pipelineState s q false P C 4) =
      .value (e4, (pipelineState s q false P C 4)) := by
    exact abdc_slice p e3 (pipelineState s q false P C 4)
  have f4 : RegisterFrame 840 844 e3 e4 :=
    abdc_frame e3
  have r2_31 := (f2.read (%31) (by decide)).trans r1_31
  have r3_31 := (f3.read (%31) (by decide)).trans r2_31
  obtain ⟨v840, v841, v842, v843⟩ := abdc_reads e3 (packPoint (productPoint false P C)) r3_31 (v836) (v837) (v838) (v839)
  have r3_790 := (f3.read (%790) (by decide)).trans r2_790
  have r4_790 := (f4.read (%790) (by decide)).trans r3_790
  have h44 : runSlice (kernel.bb2 p) e4 52 1 (pipelineState s q false P C 4) =
      .value (e5, (pipelineState s q false P C 4)) := by
    exact load_product1_slice p e4 (pipelineState s q false P C 4) q.prepared (packPoint (productPoint false P C)) (pipelineState_live s q false P C (hmem.live 1) 4) (copied_read s q false P C (hmem.live 1) (hmem.live 2)) r4_790
  have f5 : RegisterFrame 844 845 e4 e5 :=
    load_product1_frame e4 (packPoint (productPoint false P C))
  have v844 : e5.read (%844) = Ty.wrap (packPoint (productPoint false P C) 4) := by
    simp [e5, bodyEnv5, load_product1Env, mlir_env]
  have h45 : runSlice (kernel.bb2 p) e5 53 21 (pipelineState s q false P C 4) =
      .value (e6, (pipelineState s q false P C 4)) := by
    exact difference_slice p e5 (pipelineState s q false P C 4)
  have f6 : RegisterFrame 845 866 e5 e6 :=
    difference_frame e5
  have r4_836 := (f4.read (%836) (by decide)).trans (v836)
  have r5_836 := (f5.read (%836) (by decide)).trans r4_836
  have r4_837 := (f4.read (%837) (by decide)).trans (v837)
  have r5_837 := (f5.read (%837) (by decide)).trans r4_837
  have r4_838 := (f4.read (%838) (by decide)).trans (v838)
  have r5_838 := (f5.read (%838) (by decide)).trans r4_838
  have r4_839 := (f4.read (%839) (by decide)).trans (v839)
  have r5_839 := (f5.read (%839) (by decide)).trans r4_839
  have r5_840 := (f5.read (%840) (by decide)).trans (v840)
  have r5_841 := (f5.read (%841) (by decide)).trans (v841)
  have r5_842 := (f5.read (%842) (by decide)).trans (v842)
  have r5_843 := (f5.read (%843) (by decide)).trans (v843)
  have r4_31 := (f4.read (%31) (by decide)).trans r3_31
  have r5_31 := (f5.read (%31) (by decide)).trans r4_31
  have r2_52 := (f2.read (%52) (by decide)).trans r1_52
  have r3_52 := (f3.read (%52) (by decide)).trans r2_52
  have r4_52 := (f4.read (%52) (by decide)).trans r3_52
  have r5_52 := (f5.read (%52) (by decide)).trans r4_52
  have r2_70 := (f2.read (%70) (by decide)).trans r1_70
  have r3_70 := (f3.read (%70) (by decide)).trans r2_70
  have r4_70 := (f4.read (%70) (by decide)).trans r3_70
  have r5_70 := (f5.read (%70) (by decide)).trans r4_70
  have r2_332 := (f2.read (%332) (by decide)).trans r1_332
  have r3_332 := (f3.read (%332) (by decide)).trans r2_332
  have r4_332 := (f4.read (%332) (by decide)).trans r3_332
  have r5_332 := (f5.read (%332) (by decide)).trans r4_332
  have r2_349 := (f2.read (%349) (by decide)).trans r1_349
  have r3_349 := (f3.read (%349) (by decide)).trans r2_349
  have r4_349 := (f4.read (%349) (by decide)).trans r3_349
  have r5_349 := (f5.read (%349) (by decide)).trans r4_349
  have cdifference : Constants e5 := ⟨r5_31, r5_52, r5_70, r5_332, r5_349⟩
  have idifference : differenceInputs e5 (packPoint (productPoint false P C)) := ⟨r5_836, r5_837, r5_838, r5_839, (v844), r5_840, r5_841, r5_842, r5_843⟩
  have v861 := difference_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference idifference 0
  have v862 := difference_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference idifference 1
  have v863 := difference_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference idifference 2
  have v864 := difference_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference idifference 3
  have v865 := difference_field e5 (productPoint false P C) (productPoint_reduced false hP hC) cdifference idifference 4
  have h66 : runSlice (kernel.bb2 p) e6 74 1 (pipelineState s q false P C 4) =
      .value (e6, (pipelineState s q false P C 4)) := by
    exact lifetime_74_slice p e6 (pipelineState s q false P C 4)
  have h67 : runSlice (kernel.bb2 p) e6 75 5 (pipelineState s q false P C 4) =
      .value (e7, (pipelineState s q false P C 4)) := by
    exact adda_slice p e6 (pipelineState s q false P C 4)
  have f7 : RegisterFrame 866 871 e6 e7 :=
    adda_frame e6
  have r6_31 := (f6.read (%31) (by decide)).trans r5_31
  have r6_52 := (f6.read (%52) (by decide)).trans r5_52
  have r6_70 := (f6.read (%70) (by decide)).trans r5_70
  have r6_332 := (f6.read (%332) (by decide)).trans r5_332
  have r6_349 := (f6.read (%349) (by decide)).trans r5_349
  have cadda : Constants e6 := ⟨r6_31, r6_52, r6_70, r6_332, r6_349⟩
  have iadda : addaInputs e6 (packPoint (differencePoint false P C)) := ⟨(v861), (v862), (v863), (v864), (v865)⟩
  have v866 := adda_field e6 (differencePoint false P C) cadda iadda 0
  have v867 := adda_field e6 (differencePoint false P C) cadda iadda 1
  have v868 := adda_field e6 (differencePoint false P C) cadda iadda 2
  have v869 := adda_field e6 (differencePoint false P C) cadda iadda 3
  have v870 := adda_field e6 (differencePoint false P C) cadda iadda 4
  have r1_353 := (f1.read (%353) (by decide)).trans (hreg.r353)
  have r2_353 := (f2.read (%353) (by decide)).trans r1_353
  have r3_353 := (f3.read (%353) (by decide)).trans r2_353
  have r4_353 := (f4.read (%353) (by decide)).trans r3_353
  have r5_353 := (f5.read (%353) (by decide)).trans r4_353
  have r6_353 := (f6.read (%353) (by decide)).trans r5_353
  have r7_353 := (f7.read (%353) (by decide)).trans r6_353
  have r1_791 := (f1.read (%791) (by decide)).trans (hreg.r791)
  have r2_791 := (f2.read (%791) (by decide)).trans r1_791
  have r3_791 := (f3.read (%791) (by decide)).trans r2_791
  have r4_791 := (f4.read (%791) (by decide)).trans r3_791
  have r5_791 := (f5.read (%791) (by decide)).trans r4_791
  have r6_791 := (f6.read (%791) (by decide)).trans r5_791
  have r7_791 := (f7.read (%791) (by decide)).trans r6_791
  have r1_792 := (f1.read (%792) (by decide)).trans (hreg.r792)
  have r2_792 := (f2.read (%792) (by decide)).trans r1_792
  have r3_792 := (f3.read (%792) (by decide)).trans r2_792
  have r4_792 := (f4.read (%792) (by decide)).trans r3_792
  have r5_792 := (f5.read (%792) (by decide)).trans r4_792
  have r6_792 := (f6.read (%792) (by decide)).trans r5_792
  have r7_792 := (f7.read (%792) (by decide)).trans r6_792
  have r1_793 := (f1.read (%793) (by decide)).trans (hreg.r793)
  have r2_793 := (f2.read (%793) (by decide)).trans r1_793
  have r3_793 := (f3.read (%793) (by decide)).trans r2_793
  have r4_793 := (f4.read (%793) (by decide)).trans r3_793
  have r5_793 := (f5.read (%793) (by decide)).trans r4_793
  have r6_793 := (f6.read (%793) (by decide)).trans r5_793
  have r7_793 := (f7.read (%793) (by decide)).trans r6_793
  have r1_794 := (f1.read (%794) (by decide)).trans (hreg.r794)
  have r2_794 := (f2.read (%794) (by decide)).trans r1_794
  have r3_794 := (f3.read (%794) (by decide)).trans r2_794
  have r4_794 := (f4.read (%794) (by decide)).trans r3_794
  have r5_794 := (f5.read (%794) (by decide)).trans r4_794
  have r6_794 := (f6.read (%794) (by decide)).trans r5_794
  have r7_794 := (f7.read (%794) (by decide)).trans r6_794
  have h72 : runSlice (kernel.bb2 p) e7 80 5 (pipelineState s q false P C 4) =
      .value (e7, (pipelineState s q false P C 5)) := by
    exact adda_store_slice p e7 (pipelineState s q false P C 4) q.left (packPoint (leftPoint false P C)) (pipelineState_live s q false P C (hmem.live 3) 4) r7_353 (v866) r7_791 (v867) r7_792 (v868) r7_793 (v869) r7_794 (v870)
  have h77 : runSlice (kernel.bb2 p) e7 85 1 (pipelineState s q false P C 5) =
      .value (e7, (pipelineState s q false P C 5)) := by
    exact lifetime_85_slice p e7 (pipelineState s q false P C 5)
  have h78 : runSlice (kernel.bb2 p) e7 86 5 (pipelineState s q false P C 5) =
      .value (e8, (pipelineState s q false P C 5)) := by
    exact cbcb_slice p e7 (pipelineState s q false P C 5)
  have f8 : RegisterFrame 871 876 e7 e8 :=
    cbcb_frame e7
  have r7_861 := (f7.read (%861) (by decide)).trans (v861)
  have r7_862 := (f7.read (%862) (by decide)).trans (v862)
  have r7_863 := (f7.read (%863) (by decide)).trans (v863)
  have r7_864 := (f7.read (%864) (by decide)).trans (v864)
  have r7_865 := (f7.read (%865) (by decide)).trans (v865)
  have r7_31 := (f7.read (%31) (by decide)).trans r6_31
  have r7_52 := (f7.read (%52) (by decide)).trans r6_52
  have r7_70 := (f7.read (%70) (by decide)).trans r6_70
  have r7_332 := (f7.read (%332) (by decide)).trans r6_332
  have r7_349 := (f7.read (%349) (by decide)).trans r6_349
  have ccbcb : Constants e7 := ⟨r7_31, r7_52, r7_70, r7_332, r7_349⟩
  have icbcb : cbcbInputs e7 (packPoint (differencePoint false P C)) := ⟨r7_861, r7_862, r7_863, r7_864, r7_865⟩
  have v871 := cbcb_field e7 (differencePoint false P C) ccbcb icbcb 0
  have v872 := cbcb_field e7 (differencePoint false P C) ccbcb icbcb 1
  have v873 := cbcb_field e7 (differencePoint false P C) ccbcb icbcb 2
  have v874 := cbcb_field e7 (differencePoint false P C) ccbcb icbcb 3
  have v875 := cbcb_field e7 (differencePoint false P C) ccbcb icbcb 4
  have r1_352 := (f1.read (%352) (by decide)).trans (hreg.r352)
  have r2_352 := (f2.read (%352) (by decide)).trans r1_352
  have r3_352 := (f3.read (%352) (by decide)).trans r2_352
  have r4_352 := (f4.read (%352) (by decide)).trans r3_352
  have r5_352 := (f5.read (%352) (by decide)).trans r4_352
  have r6_352 := (f6.read (%352) (by decide)).trans r5_352
  have r7_352 := (f7.read (%352) (by decide)).trans r6_352
  have r8_352 := (f8.read (%352) (by decide)).trans r7_352
  have r1_795 := (f1.read (%795) (by decide)).trans (hreg.r795)
  have r2_795 := (f2.read (%795) (by decide)).trans r1_795
  have r3_795 := (f3.read (%795) (by decide)).trans r2_795
  have r4_795 := (f4.read (%795) (by decide)).trans r3_795
  have r5_795 := (f5.read (%795) (by decide)).trans r4_795
  have r6_795 := (f6.read (%795) (by decide)).trans r5_795
  have r7_795 := (f7.read (%795) (by decide)).trans r6_795
  have r8_795 := (f8.read (%795) (by decide)).trans r7_795
  have r1_796 := (f1.read (%796) (by decide)).trans (hreg.r796)
  have r2_796 := (f2.read (%796) (by decide)).trans r1_796
  have r3_796 := (f3.read (%796) (by decide)).trans r2_796
  have r4_796 := (f4.read (%796) (by decide)).trans r3_796
  have r5_796 := (f5.read (%796) (by decide)).trans r4_796
  have r6_796 := (f6.read (%796) (by decide)).trans r5_796
  have r7_796 := (f7.read (%796) (by decide)).trans r6_796
  have r8_796 := (f8.read (%796) (by decide)).trans r7_796
  have r1_797 := (f1.read (%797) (by decide)).trans (hreg.r797)
  have r2_797 := (f2.read (%797) (by decide)).trans r1_797
  have r3_797 := (f3.read (%797) (by decide)).trans r2_797
  have r4_797 := (f4.read (%797) (by decide)).trans r3_797
  have r5_797 := (f5.read (%797) (by decide)).trans r4_797
  have r6_797 := (f6.read (%797) (by decide)).trans r5_797
  have r7_797 := (f7.read (%797) (by decide)).trans r6_797
  have r8_797 := (f8.read (%797) (by decide)).trans r7_797
  have r1_798 := (f1.read (%798) (by decide)).trans (hreg.r798)
  have r2_798 := (f2.read (%798) (by decide)).trans r1_798
  have r3_798 := (f3.read (%798) (by decide)).trans r2_798
  have r4_798 := (f4.read (%798) (by decide)).trans r3_798
  have r5_798 := (f5.read (%798) (by decide)).trans r4_798
  have r6_798 := (f6.read (%798) (by decide)).trans r5_798
  have r7_798 := (f7.read (%798) (by decide)).trans r6_798
  have r8_798 := (f8.read (%798) (by decide)).trans r7_798
  have h83 : runSlice (kernel.bb2 p) e8 91 5 (pipelineState s q false P C 5) =
      .value (e8, (pipelineState s q false P C 6)) := by
    exact cbcb_store_slice p e8 (pipelineState s q false P C 5) q.right (packPoint (rightPoint false P C)) (pipelineState_live s q false P C (hmem.live 4) 5) r8_352 (v871) r8_795 (v872) r8_796 (v873) r8_797 (v874) r8_798 (v875)
  have r1_358 := (f1.read (%358) (by decide)).trans (hreg.r358)
  have r2_358 := (f2.read (%358) (by decide)).trans r1_358
  have r3_358 := (f3.read (%358) (by decide)).trans r2_358
  have r4_358 := (f4.read (%358) (by decide)).trans r3_358
  have r5_358 := (f5.read (%358) (by decide)).trans r4_358
  have r6_358 := (f6.read (%358) (by decide)).trans r5_358
  have r7_358 := (f7.read (%358) (by decide)).trans r6_358
  have r8_358 := (f8.read (%358) (by decide)).trans r7_358
  have r8_353 := (f8.read (%353) (by decide)).trans r7_353
  have h88 : runSlice (kernel.bb2 p) e8 96 1 (pipelineState s q false P C 6) =
      .value (e8, (pipelineState s q false P C 7)) := by
    exact multiply_1_slice p e8 (pipelineState s q false P C 6) q.output q.left q.right (leftPoint false P C) (rightPoint false P C) hmul (pipelineState_wf s q false P C hmem.wf 6) (pipelineState_live s q false P C (hmem.live 0) 6) (pipelineState_live s q false P C (hmem.live 3) 6) (pipelineState_live s q false P C (hmem.live 4) 6) (leftPoint_wide false hP hC) (rightPoint_wide false hP hC) (factors_read s q false (tableRow table index) P C hmem).1 (factors_read s q false (tableRow table index) P C hmem).2 r8_358 r8_353 r8_352
  have h89 : runSlice (kernel.bb2 p) e8 97 3 (pipelineState s q false P C 7) =
      .value (e8, (pipelineState s q false P C 7)) := by
    exact lifetime_97_slice p e8 (pipelineState s q false P C 7)
  have r1_799 := (f1.read (%799) (by decide)).trans (hreg.r799)
  have r2_799 := (f2.read (%799) (by decide)).trans r1_799
  have r3_799 := (f3.read (%799) (by decide)).trans r2_799
  have r4_799 := (f4.read (%799) (by decide)).trans r3_799
  have r5_799 := (f5.read (%799) (by decide)).trans r4_799
  have r6_799 := (f6.read (%799) (by decide)).trans r5_799
  have r7_799 := (f7.read (%799) (by decide)).trans r6_799
  have r8_799 := (f8.read (%799) (by decide)).trans r7_799
  have r1_800 := (f1.read (%800) (by decide)).trans (hreg.r800)
  have r2_800 := (f2.read (%800) (by decide)).trans r1_800
  have r3_800 := (f3.read (%800) (by decide)).trans r2_800
  have r4_800 := (f4.read (%800) (by decide)).trans r3_800
  have r5_800 := (f5.read (%800) (by decide)).trans r4_800
  have r6_800 := (f6.read (%800) (by decide)).trans r5_800
  have r7_800 := (f7.read (%800) (by decide)).trans r6_800
  have r8_800 := (f8.read (%800) (by decide)).trans r7_800
  have r1_801 := (f1.read (%801) (by decide)).trans (hreg.r801)
  have r2_801 := (f2.read (%801) (by decide)).trans r1_801
  have r3_801 := (f3.read (%801) (by decide)).trans r2_801
  have r4_801 := (f4.read (%801) (by decide)).trans r3_801
  have r5_801 := (f5.read (%801) (by decide)).trans r4_801
  have r6_801 := (f6.read (%801) (by decide)).trans r5_801
  have r7_801 := (f7.read (%801) (by decide)).trans r6_801
  have r8_801 := (f8.read (%801) (by decide)).trans r7_801
  have r1_802 := (f1.read (%802) (by decide)).trans (hreg.r802)
  have r2_802 := (f2.read (%802) (by decide)).trans r1_802
  have r3_802 := (f3.read (%802) (by decide)).trans r2_802
  have r4_802 := (f4.read (%802) (by decide)).trans r3_802
  have r5_802 := (f5.read (%802) (by decide)).trans r4_802
  have r6_802 := (f6.read (%802) (by decide)).trans r5_802
  have r7_802 := (f7.read (%802) (by decide)).trans r6_802
  have r8_802 := (f8.read (%802) (by decide)).trans r7_802
  have h92 : runSlice (kernel.bb2 p) e8 100 5 (pipelineState s q false P C 7) =
      .value (e9, (pipelineState s q false P C 7)) := by
    exact load_result_slice p e8 (pipelineState s q false P C 7) q.output (packPoint (resultPoint false P C)) (pipelineState_live s q false P C (hmem.live 0) 7) (result_read s q false P C (hmem.live 0)) r8_358 r8_799 r8_800 r8_801 r8_802
  have f9 : RegisterFrame 876 881 e8 e9 :=
    load_result_frame e8 (packPoint (resultPoint false P C))
  have v876 : e9.read (%876) = Ty.wrap (packPoint (resultPoint false P C) 0) := by
    simp [e9, bodyEnv9, load_resultEnv, mlir_env]
  have v877 : e9.read (%877) = Ty.wrap (packPoint (resultPoint false P C) 1) := by
    simp [e9, bodyEnv9, load_resultEnv, mlir_env]
  have v878 : e9.read (%878) = Ty.wrap (packPoint (resultPoint false P C) 2) := by
    simp [e9, bodyEnv9, load_resultEnv, mlir_env]
  have v879 : e9.read (%879) = Ty.wrap (packPoint (resultPoint false P C) 3) := by
    simp [e9, bodyEnv9, load_resultEnv, mlir_env]
  have v880 : e9.read (%880) = Ty.wrap (packPoint (resultPoint false P C) 4) := by
    simp [e9, bodyEnv9, load_resultEnv, mlir_env]
  calc
    (kernel.bb2 p).runBodyFrom E 0 s0 = (kernel.bb2 p).runBodyFrom e1 4 s0 :=
      runBodyFrom_slice _ _ _ _ _ _ _ h0
    _ = (kernel.bb2 p).runBodyFrom e1 5 s := runBodyFrom_slice _ _ _ _ _ _ _ hcopy
    _ = (kernel.bb2 p).runBodyFrom e2 35 s := runBodyFrom_slice _ _ _ _ _ _ _ h2
    _ = (kernel.bb2 p).runBodyFrom e2 40 (pipelineState s q false P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h27
    _ = (kernel.bb2 p).runBodyFrom e2 41 (pipelineState s q false P C 2) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h32
    _ = (kernel.bb2 p).runBodyFrom e2 42 (pipelineState s q false P C 3) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h33
    _ = (kernel.bb2 p).runBodyFrom e2 43 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h34
    _ = (kernel.bb2 p).runBodyFrom e2 44 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h35
    _ = (kernel.bb2 p).runBodyFrom e3 48 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h36
    _ = (kernel.bb2 p).runBodyFrom e4 52 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h40
    _ = (kernel.bb2 p).runBodyFrom e5 53 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h44
    _ = (kernel.bb2 p).runBodyFrom e6 74 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h45
    _ = (kernel.bb2 p).runBodyFrom e6 75 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h66
    _ = (kernel.bb2 p).runBodyFrom e7 80 (pipelineState s q false P C 4) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h67
    _ = (kernel.bb2 p).runBodyFrom e7 85 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h72
    _ = (kernel.bb2 p).runBodyFrom e7 86 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h77
    _ = (kernel.bb2 p).runBodyFrom e8 91 (pipelineState s q false P C 5) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h78
    _ = (kernel.bb2 p).runBodyFrom e8 96 (pipelineState s q false P C 6) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h83
    _ = (kernel.bb2 p).runBodyFrom e8 97 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h88
    _ = (kernel.bb2 p).runBodyFrom e8 100 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h89
    _ = (kernel.bb2 p).runBodyFrom e9 105 (pipelineState s q false P C 7) :=
      runBodyFrom_slice _ _ _ _ _ _ _ h92

end Agave.Ed25519.Tables.Avx2Constructor.Add
