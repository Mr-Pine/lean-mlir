import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2Constructor
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorBroadcastMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame

/-! The original eight-record broadcast, split at each five-vector record.
All 40 stores and 39 inbounds GEPs are executed from the imported body. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Broadcast
open LeanMLIR.RIR
open Avx2FieldMul.Execution (Blocks)
open Reduce64.Execution (SmallRange)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

structure Reads (E : ⟪kernel.Γ⟫) (table : Pointer) (v : Blocks) : Prop where
  ptr : E.read (%360) = .value table
  v0 : E.read (%645) = Ty.wrap (v 0)
  v1 : E.read (%646) = Ty.wrap (v 1)
  v2 : E.read (%647) = Ty.wrap (v 2)
  v3 : E.read (%648) = Ty.wrap (v 3)
  v4 : E.read (%649) = Ty.wrap (v 4)

theorem Reads.frame {E F : ⟪kernel.Γ⟫} (h : Reads E table v)
    (hf : RegisterFrame 650 689 E F) : Reads F table v :=
  ⟨(hf.read (%360) (by decide)).trans h.ptr,
   (hf.read (%645) (by decide)).trans h.v0,
   (hf.read (%646) (by decide)).trans h.v1,
   (hf.read (%647) (by decide)).trans h.v2,
   (hf.read (%648) (by decide)).trans h.v3,
   (hf.read (%649) (by decide)).trans h.v4⟩

def recordState (s : GlobalState) (table : Pointer) (v : Blocks) (i : Nat) : GlobalState :=
  let m := s.mem
  let m := m.storeAt (table.add (BitVec.ofNat 64 (160*i+0))) (BitVec.packLanes (v 0))
  let m := m.storeAt (table.add (BitVec.ofNat 64 (160*i+32))) (BitVec.packLanes (v 1))
  let m := m.storeAt (table.add (BitVec.ofNat 64 (160*i+64))) (BitVec.packLanes (v 2))
  let m := m.storeAt (table.add (BitVec.ofNat 64 (160*i+96))) (BitVec.packLanes (v 3))
  let m := m.storeAt (table.add (BitVec.ofNat 64 (160*i+128))) (BitVec.packLanes (v 4))
  {s with mem := m}

theorem recordState_step (s : GlobalState) (table : Pointer) (v : Blocks) (i : Fin 8) :
    recordState (state s table v (5*i.val)) table v i.val = state s table v (5*(i.val+1)) := by
  fin_cases i <;> rfl

def record0Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%650 := .value (table.add 32#64),
    %651 := .value (table.add 64#64),
    %652 := .value (table.add 96#64),
    %653 := .value (table.add 128#64)]

theorem record0_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record0Env E table) := by
  unfold record0Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record0_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 650 9 s = .value (record0Env E table, recordState s table v 0) := by
  have ht0 := ht
  have hf0 := ht0.fits_add (k := 0) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 0#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 32) (by decide)
  have hf1 := ht1.fits_add (k := 32) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 32#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 64) (by decide)
  have hf2 := ht2.fits_add (k := 64) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 64#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 96) (by decide)
  have hf3 := ht3.fits_add (k := 96) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 96#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 128) (by decide)
  have hf4 := ht4.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0 ht1 hg1 hf1 ht2 hg2 hf2 ht3 hg3 hf3 ht4 hg4 hf4
  norm_num only [Nat.cast_ofNat] at hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record0Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record1Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%654 := .value (table.add 160#64),
    %655 := .value (table.add 192#64),
    %656 := .value (table.add 224#64),
    %657 := .value (table.add 256#64),
    %658 := .value (table.add 288#64)]

theorem record1_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record1Env E table) := by
  unfold record1Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record1_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 659 10 s = .value (record1Env E table, recordState s table v 1) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 160) (by decide)
  have hf0 := ht0.fits_add (k := 160) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 160#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 192) (by decide)
  have hf1 := ht1.fits_add (k := 192) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 192#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 224) (by decide)
  have hf2 := ht2.fits_add (k := 224) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 224#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 256) (by decide)
  have hf3 := ht3.fits_add (k := 256) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 256#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 288) (by decide)
  have hf4 := ht4.fits_add (k := 288) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record1Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record2Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%659 := .value (table.add 320#64),
    %660 := .value (table.add 352#64),
    %661 := .value (table.add 384#64),
    %662 := .value (table.add 416#64),
    %663 := .value (table.add 448#64)]

theorem record2_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record2Env E table) := by
  unfold record2Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record2_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 669 10 s = .value (record2Env E table, recordState s table v 2) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 320) (by decide)
  have hf0 := ht0.fits_add (k := 320) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 320#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 352) (by decide)
  have hf1 := ht1.fits_add (k := 352) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 352#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 384) (by decide)
  have hf2 := ht2.fits_add (k := 384) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 384#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 416) (by decide)
  have hf3 := ht3.fits_add (k := 416) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 416#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 448) (by decide)
  have hf4 := ht4.fits_add (k := 448) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record2Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record3Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%664 := .value (table.add 480#64),
    %665 := .value (table.add 512#64),
    %666 := .value (table.add 544#64),
    %667 := .value (table.add 576#64),
    %668 := .value (table.add 608#64)]

theorem record3_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record3Env E table) := by
  unfold record3Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record3_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 679 10 s = .value (record3Env E table, recordState s table v 3) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 480) (by decide)
  have hf0 := ht0.fits_add (k := 480) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 480#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 512) (by decide)
  have hf1 := ht1.fits_add (k := 512) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 512#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 544) (by decide)
  have hf2 := ht2.fits_add (k := 544) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 544#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 576) (by decide)
  have hf3 := ht3.fits_add (k := 576) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 576#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 608) (by decide)
  have hf4 := ht4.fits_add (k := 608) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record3Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record4Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%669 := .value (table.add 640#64),
    %670 := .value (table.add 672#64),
    %671 := .value (table.add 704#64),
    %672 := .value (table.add 736#64),
    %673 := .value (table.add 768#64)]

theorem record4_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record4Env E table) := by
  unfold record4Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record4_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 689 10 s = .value (record4Env E table, recordState s table v 4) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 640) (by decide)
  have hf0 := ht0.fits_add (k := 640) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 640#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 672) (by decide)
  have hf1 := ht1.fits_add (k := 672) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 672#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 704) (by decide)
  have hf2 := ht2.fits_add (k := 704) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 704#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 736) (by decide)
  have hf3 := ht3.fits_add (k := 736) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 736#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 768) (by decide)
  have hf4 := ht4.fits_add (k := 768) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record4Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record5Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%674 := .value (table.add 800#64),
    %675 := .value (table.add 832#64),
    %676 := .value (table.add 864#64),
    %677 := .value (table.add 896#64),
    %678 := .value (table.add 928#64)]

theorem record5_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record5Env E table) := by
  unfold record5Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record5_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 699 10 s = .value (record5Env E table, recordState s table v 5) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 800) (by decide)
  have hf0 := ht0.fits_add (k := 800) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 800#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 832) (by decide)
  have hf1 := ht1.fits_add (k := 832) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 832#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 864) (by decide)
  have hf2 := ht2.fits_add (k := 864) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 864#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 896) (by decide)
  have hf3 := ht3.fits_add (k := 896) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 896#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 928) (by decide)
  have hf4 := ht4.fits_add (k := 928) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record5Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record6Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%679 := .value (table.add 960#64),
    %680 := .value (table.add 992#64),
    %681 := .value (table.add 1024#64),
    %682 := .value (table.add 1056#64),
    %683 := .value (table.add 1088#64)]

theorem record6_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record6Env E table) := by
  unfold record6Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record6_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 709 10 s = .value (record6Env E table, recordState s table v 6) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 960) (by decide)
  have hf0 := ht0.fits_add (k := 960) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 960#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 992) (by decide)
  have hf1 := ht1.fits_add (k := 992) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 992#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 1024) (by decide)
  have hf2 := ht2.fits_add (k := 1024) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 1024#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 1056) (by decide)
  have hf3 := ht3.fits_add (k := 1056) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 1056#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 1088) (by decide)
  have hf4 := ht4.fits_add (k := 1088) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record6Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def record7Env (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  E[%684 := .value (table.add 1120#64),
    %685 := .value (table.add 1152#64),
    %686 := .value (table.add 1184#64),
    %687 := .value (table.add 1216#64),
    %688 := .value (table.add 1248#64)]

theorem record7_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (record7Env E table) := by
  unfold record7Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem record7_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    runSlice (kernel.bb0 p) E 719 10 s = .value (record7Env E table, recordState s table v 7) := by
  have ht0 := ht
  have hg0 := ht0.gep (k := 1120) (by decide)
  have hf0 := ht0.fits_add (k := 1120) (count := 32) (by decide)
  have ht1 := ht0.storeAt (table.add 1120#64) (BitVec.packLanes (v 0))
  have hg1 := ht1.gep (k := 1152) (by decide)
  have hf1 := ht1.fits_add (k := 1152) (count := 32) (by decide)
  have ht2 := ht1.storeAt (table.add 1152#64) (BitVec.packLanes (v 1))
  have hg2 := ht2.gep (k := 1184) (by decide)
  have hf2 := ht2.fits_add (k := 1184) (count := 32) (by decide)
  have ht3 := ht2.storeAt (table.add 1184#64) (BitVec.packLanes (v 2))
  have hg3 := ht3.gep (k := 1216) (by decide)
  have hf3 := ht3.fits_add (k := 1216) (count := 32) (by decide)
  have ht4 := ht3.storeAt (table.add 1216#64) (BitVec.packLanes (v 3))
  have hg4 := ht4.gep (k := 1248) (by decide)
  have hf4 := ht4.fits_add (k := 1248) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  simp [runSlice, kernel.bb0, record7Env, recordState,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset,
    mlir_effect, mlir_env, throwUBIf, hr.ptr, hr.v0, hr.v1, hr.v2, hr.v3, hr.v4,
    hg0, hg1, hg2, hg3, hg4, hf0, hf1, hf2, hf3, hf4]

def resultEnv (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  (record7Env (record6Env (record5Env (record4Env (record3Env (record2Env (record1Env (record0Env E table) table) table) table) table) table) table) table)

theorem resultEnv_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 650 689 E (resultEnv E table) :=
  (((((((record0_frame E table).trans (record1_frame _ table)).trans (record2_frame _ table)).trans (record3_frame _ table)).trans (record4_frame _ table)).trans (record5_frame _ table)).trans (record6_frame _ table)).trans (record7_frame _ table)

theorem body_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (v : Blocks) (ht : SmallRange s.mem table 1280)
    (hr : Reads E table v) :
    (kernel.bb0 p).runBodyFrom E 650 s =
      (kernel.bb0 p).runBodyFrom (resultEnv E table) 729 (state s table v 40) := by
  let E1 := record0Env E table
  have hr1 : Reads E1 table v := hr.frame (record0_frame E table)
  let E2 := record1Env E1 table
  have hr2 : Reads E2 table v := hr1.frame (record1_frame E1 table)
  let E3 := record2Env E2 table
  have hr3 : Reads E3 table v := hr2.frame (record2_frame E2 table)
  let E4 := record3Env E3 table
  have hr4 : Reads E4 table v := hr3.frame (record3_frame E3 table)
  let E5 := record4Env E4 table
  have hr5 : Reads E5 table v := hr4.frame (record4_frame E4 table)
  let E6 := record5Env E5 table
  have hr6 : Reads E6 table v := hr5.frame (record5_frame E5 table)
  let E7 := record6Env E6 table
  have hr7 : Reads E7 table v := hr6.frame (record6_frame E6 table)
  let E8 := record7Env E7 table
  have hr8 : Reads E8 table v := hr7.frame (record7_frame E7 table)
  have h0 := record0_slice p E (state s table v 0) table v
    (memory_live ht table v 0) hr
  have hs0 : recordState (state s table v 0) table v 0 = state s table v 5 :=
    recordState_step s table v ⟨0,by decide⟩
  rw [hs0] at h0
  have h1 := record1_slice p E1 (state s table v 5) table v
    (memory_live ht table v 5) hr1
  have hs1 : recordState (state s table v 5) table v 1 = state s table v 10 :=
    recordState_step s table v ⟨1,by decide⟩
  rw [hs1] at h1
  have h2 := record2_slice p E2 (state s table v 10) table v
    (memory_live ht table v 10) hr2
  have hs2 : recordState (state s table v 10) table v 2 = state s table v 15 :=
    recordState_step s table v ⟨2,by decide⟩
  rw [hs2] at h2
  have h3 := record3_slice p E3 (state s table v 15) table v
    (memory_live ht table v 15) hr3
  have hs3 : recordState (state s table v 15) table v 3 = state s table v 20 :=
    recordState_step s table v ⟨3,by decide⟩
  rw [hs3] at h3
  have h4 := record4_slice p E4 (state s table v 20) table v
    (memory_live ht table v 20) hr4
  have hs4 : recordState (state s table v 20) table v 4 = state s table v 25 :=
    recordState_step s table v ⟨4,by decide⟩
  rw [hs4] at h4
  have h5 := record5_slice p E5 (state s table v 25) table v
    (memory_live ht table v 25) hr5
  have hs5 : recordState (state s table v 25) table v 5 = state s table v 30 :=
    recordState_step s table v ⟨5,by decide⟩
  rw [hs5] at h5
  have h6 := record6_slice p E6 (state s table v 30) table v
    (memory_live ht table v 30) hr6
  have hs6 : recordState (state s table v 30) table v 6 = state s table v 35 :=
    recordState_step s table v ⟨6,by decide⟩
  rw [hs6] at h6
  have h7 := record7_slice p E7 (state s table v 35) table v
    (memory_live ht table v 35) hr7
  have hs7 : recordState (state s table v 35) table v 7 = state s table v 40 :=
    recordState_step s table v ⟨7,by decide⟩
  rw [hs7] at h7
  calc
    _ = (kernel.bb0 p).runBodyFrom E1 659 (state s table v 5) :=
      runBodyFrom_slice _ E E1 650 9 (state s table v 0) (state s table v 5) h0
    _ = (kernel.bb0 p).runBodyFrom E2 669 (state s table v 10) :=
      runBodyFrom_slice _ E1 E2 659 10 (state s table v 5) (state s table v 10) h1
    _ = (kernel.bb0 p).runBodyFrom E3 679 (state s table v 15) :=
      runBodyFrom_slice _ E2 E3 669 10 (state s table v 10) (state s table v 15) h2
    _ = (kernel.bb0 p).runBodyFrom E4 689 (state s table v 20) :=
      runBodyFrom_slice _ E3 E4 679 10 (state s table v 15) (state s table v 20) h3
    _ = (kernel.bb0 p).runBodyFrom E5 699 (state s table v 25) :=
      runBodyFrom_slice _ E4 E5 689 10 (state s table v 20) (state s table v 25) h4
    _ = (kernel.bb0 p).runBodyFrom E6 709 (state s table v 30) :=
      runBodyFrom_slice _ E5 E6 699 10 (state s table v 25) (state s table v 30) h5
    _ = (kernel.bb0 p).runBodyFrom E7 719 (state s table v 35) :=
      runBodyFrom_slice _ E6 E7 709 10 (state s table v 30) (state s table v 35) h6
    _ = (kernel.bb0 p).runBodyFrom E8 729 (state s table v 40) :=
      runBodyFrom_slice _ E7 E8 719 10 (state s table v 35) (state s table v 40) h7

end Agave.Ed25519.Tables.Avx2Constructor.Broadcast

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.Broadcast.body_continue,
      `Agave.Ed25519.Tables.Avx2Constructor.Broadcast.resultEnv_frame,
      `Agave.Ed25519.Tables.Avx2Constructor.Broadcast.readback,
      `Agave.Ed25519.Tables.Avx2Constructor.Broadcast.memory_read_ne,
      `Agave.Ed25519.Tables.Avx2Constructor.Broadcast.memory_shape] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"

#print axioms Agave.Ed25519.Tables.Avx2Constructor.Broadcast.body_continue
