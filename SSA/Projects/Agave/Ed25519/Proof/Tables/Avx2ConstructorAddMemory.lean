import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddDefs
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMultiplication

/-! Exact positive-add intervals of the unchanged AVX2 table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Add
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice prepareConstants differenceConstants abdcVec)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

/-- The five actual stores following prepare; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem prepare_store_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%355) = .value r)
    (hv0 : E.read (%831) = Ty.wrap (v 0))
    (hp1 : E.read (%787) = .value (r.add 32#64))
    (hv1 : E.read (%832) = Ty.wrap (v 1))
    (hp2 : E.read (%788) = .value (r.add 64#64))
    (hv2 : E.read (%833) = Ty.wrap (v 2))
    (hp3 : E.read (%789) = .value (r.add 96#64))
    (hv3 : E.read (%834) = Ty.wrap (v 3))
    (hp4 : E.read (%790) = .value (r.add 128#64))
    (hv4 : E.read (%835) = Ty.wrap (v 4)) :
    runSlice (kernel.bb2 p) E 35 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb2, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem prepare_store_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%355) = .value r)
    (hv0 : E.read (%831) = Ty.wrap (v 0))
    (hp1 : E.read (%787) = .value (r.add 32#64))
    (hv1 : E.read (%832) = Ty.wrap (v 1))
    (hp2 : E.read (%788) = .value (r.add 64#64))
    (hv2 : E.read (%833) = Ty.wrap (v 2))
    (hp3 : E.read (%789) = .value (r.add 96#64))
    (hv3 : E.read (%834) = Ty.wrap (v 3))
    (hp4 : E.read (%790) = .value (r.add 128#64))
    (hv4 : E.read (%835) = Ty.wrap (v 4)) :
    (kernel.bb2 p).runBodyFrom E 35 s =
      (kernel.bb2 p).runBodyFrom E 40
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 35 5 s _
    (prepare_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following adda; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem adda_store_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%353) = .value r)
    (hv0 : E.read (%866) = Ty.wrap (v 0))
    (hp1 : E.read (%791) = .value (r.add 32#64))
    (hv1 : E.read (%867) = Ty.wrap (v 1))
    (hp2 : E.read (%792) = .value (r.add 64#64))
    (hv2 : E.read (%868) = Ty.wrap (v 2))
    (hp3 : E.read (%793) = .value (r.add 96#64))
    (hv3 : E.read (%869) = Ty.wrap (v 3))
    (hp4 : E.read (%794) = .value (r.add 128#64))
    (hv4 : E.read (%870) = Ty.wrap (v 4)) :
    runSlice (kernel.bb2 p) E 80 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb2, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem adda_store_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%353) = .value r)
    (hv0 : E.read (%866) = Ty.wrap (v 0))
    (hp1 : E.read (%791) = .value (r.add 32#64))
    (hv1 : E.read (%867) = Ty.wrap (v 1))
    (hp2 : E.read (%792) = .value (r.add 64#64))
    (hv2 : E.read (%868) = Ty.wrap (v 2))
    (hp3 : E.read (%793) = .value (r.add 96#64))
    (hv3 : E.read (%869) = Ty.wrap (v 3))
    (hp4 : E.read (%794) = .value (r.add 128#64))
    (hv4 : E.read (%870) = Ty.wrap (v 4)) :
    (kernel.bb2 p).runBodyFrom E 80 s =
      (kernel.bb2 p).runBodyFrom E 85
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 80 5 s _
    (adda_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following cbcb; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem cbcb_store_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%352) = .value r)
    (hv0 : E.read (%871) = Ty.wrap (v 0))
    (hp1 : E.read (%795) = .value (r.add 32#64))
    (hv1 : E.read (%872) = Ty.wrap (v 1))
    (hp2 : E.read (%796) = .value (r.add 64#64))
    (hv2 : E.read (%873) = Ty.wrap (v 2))
    (hp3 : E.read (%797) = .value (r.add 96#64))
    (hv3 : E.read (%874) = Ty.wrap (v 3))
    (hp4 : E.read (%798) = .value (r.add 128#64))
    (hv4 : E.read (%875) = Ty.wrap (v 4)) :
    runSlice (kernel.bb2 p) E 91 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb2, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem cbcb_store_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%352) = .value r)
    (hv0 : E.read (%871) = Ty.wrap (v 0))
    (hp1 : E.read (%795) = .value (r.add 32#64))
    (hv1 : E.read (%872) = Ty.wrap (v 1))
    (hp2 : E.read (%796) = .value (r.add 64#64))
    (hv2 : E.read (%873) = Ty.wrap (v 2))
    (hp3 : E.read (%797) = .value (r.add 96#64))
    (hv3 : E.read (%874) = Ty.wrap (v 3))
    (hp4 : E.read (%798) = .value (r.add 128#64))
    (hv4 : E.read (%875) = Ty.wrap (v 4)) :
    (kernel.bb2 p).runBodyFrom E 91 s =
      (kernel.bb2 p).runBodyFrom E 96
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 91 5 s _
    (cbcb_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The exact first-product copy. Its disjointness is an explicit
precondition supplied by the distinct scratch allocations in the caller. -/
theorem initialCopy_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%355) = .value dst)
    (hpsrc : E.read (%359) = .value src)
    (hlen : E.read (%195) = .value 160#64) :
    runSlice (kernel.bb2 p) E 4 1 s =
      .value (E, {s with mem := copyPointBytes s.mem dst src}) := by
  have hcopy := run_memcpy (s := s) (env := E) (len := 160#64) (n := 160)
    (by decide) hd hdst.fits hsrc.fits
  simp [runSlice, kernel.bb2, copyPointBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, hpdst, hpsrc, hlen, hcopy]

theorem initialCopy_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%355) = .value dst)
    (hpsrc : E.read (%359) = .value src)
    (hlen : E.read (%195) = .value 160#64) :
    (kernel.bb2 p).runBodyFrom E 4 s =
      (kernel.bb2 p).runBodyFrom E 5
        {s with mem := copyPointBytes s.mem dst src} := by
  exact runBodyFrom_slice _ E E 4 1 s _
    (initialCopy_slice p E s dst src hdst hsrc hd hpdst hpsrc hlen)

/-- The exact first-product copy. Its disjointness is an explicit
precondition supplied by the distinct scratch allocations in the caller. -/
theorem copy_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%355) = .value dst)
    (hpsrc : E.read (%354) = .value src)
    (hlen : E.read (%195) = .value 160#64) :
    runSlice (kernel.bb2 p) E 42 1 s =
      .value (E, {s with mem := copyPointBytes s.mem dst src}) := by
  have hcopy := run_memcpy (s := s) (env := E) (len := 160#64) (n := 160)
    (by decide) hd hdst.fits hsrc.fits
  simp [runSlice, kernel.bb2, copyPointBytes,
    List.foldlM_cons, List.foldlM_nil, Instr.run,
    EffectM.bind_eq, EffectM.pure_eq, hpdst, hpsrc, hlen, hcopy]

theorem copy_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (dst src : Pointer)
    (hdst : Reduce64.Execution.SmallRange s.mem dst 160)
    (hsrc : Reduce64.Execution.SmallRange s.mem src 160)
    (hd : (Range.of dst 1280).Disjoint (Range.of src 1280))
    (hpdst : E.read (%355) = .value dst)
    (hpsrc : E.read (%354) = .value src)
    (hlen : E.read (%195) = .value 160#64) :
    (kernel.bb2 p).runBodyFrom E 42 s =
      (kernel.bb2 p).runBodyFrom E 43
        {s with mem := copyPointBytes s.mem dst src} := by
  exact runBodyFrom_slice _ E E 42 1 s _
    (copy_slice p E s dst src hdst hsrc hd hpdst hpsrc hlen)

/-- The actual first field-helper call
instruction in bb2, with a packed point result and restored limb bounds. -/
theorem multiply_0_field (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call1)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%354) = .value r)
    (hpa : E.read (%355) = .value a)
    (hpb : E.read (%805) = .value b) :
    ∃ s' : GlobalState,
      runSlice (kernel.bb2 p) E 41 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call1 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply_0_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call1)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%354) = .value r)
    (hpa : E.read (%355) = .value a)
    (hpb : E.read (%805) = .value b) :
    runSlice (kernel.bb2 p) E 41 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call1 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual second field-helper call
instruction in bb2, with a packed point result and restored limb bounds. -/
theorem multiply_1_field (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call1)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%358) = .value r)
    (hpa : E.read (%353) = .value a)
    (hpb : E.read (%352) = .value b) :
    ∃ s' : GlobalState,
      runSlice (kernel.bb2 p) E 96 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call1 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply_1_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call1)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%358) = .value r)
    (hpa : E.read (%353) = .value a)
    (hpb : E.read (%352) = .value b) :
    runSlice (kernel.bb2 p) E 96 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call1 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load_product4Env (E : ⟪kernel.Γ⟫) (v : PointBlocks) : ⟪kernel.Γ⟫ :=
  E[%836 := Ty.wrap (v 0), %837 := Ty.wrap (v 1), %838 := Ty.wrap (v 2), %839 := Ty.wrap (v 3)]

theorem load_product4_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%355) = .value r)
    (hp1 : E.read (%787) = .value (r.add 32#64))
    (hp2 : E.read (%788) = .value (r.add 64#64))
    (hp3 : E.read (%789) = .value (r.add 96#64)) :
    runSlice (kernel.bb2 p) E 44 4 s =
      .value (load_product4Env E v, s) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 0#64) 256) =
      Ty.wrap (v 0) := packed_unflatten s.mem r v hv 0
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hv1 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 32#64) 256) =
      Ty.wrap (v 1) := packed_unflatten s.mem r v hv 1
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv1
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hv2 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 64#64) 256) =
      Ty.wrap (v 2) := packed_unflatten s.mem r v hv 2
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv2
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hv3 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 96#64) 256) =
      Ty.wrap (v 3) := packed_unflatten s.mem r v hv 3
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv3
  simp only [Pointer.add_zero] at hf0 hv0
  simp [runSlice, kernel.bb2, load_product4Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3]

theorem load_product4_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%355) = .value r)
    (hp1 : E.read (%787) = .value (r.add 32#64))
    (hp2 : E.read (%788) = .value (r.add 64#64))
    (hp3 : E.read (%789) = .value (r.add 96#64)) :
    (kernel.bb2 p).runBodyFrom E 44 s =
      (kernel.bb2 p).runBodyFrom (load_product4Env E v) 48 s := by
  exact runBodyFrom_slice _ E (load_product4Env E v) 44 4 s s
    (load_product4_slice p E s r v hr hv hp0 hp1 hp2 hp3)

theorem load_product4_reads (E : ⟪kernel.Γ⟫) (v : PointBlocks) :
    (load_product4Env E v).read (%836) = Ty.wrap (v 0) ∧
    (load_product4Env E v).read (%837) = Ty.wrap (v 1) ∧
    (load_product4Env E v).read (%838) = Ty.wrap (v 2) ∧
    (load_product4Env E v).read (%839) = Ty.wrap (v 3) := by
  simp [load_product4Env, mlir_env, -reduceShufflevector]

theorem load_product4_constants (E : ⟪kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load_product4Env E v) := by
  constructor <;> simp [load_product4Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN]

theorem load_product4_frame (E : ⟪kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 836 840 E (load_product4Env E v) := by
  unfold load_product4Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load_product1Env (E : ⟪kernel.Γ⟫) (v : PointBlocks) : ⟪kernel.Γ⟫ :=
  E[%844 := Ty.wrap (v 4)]

theorem load_product1_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%790) = .value (r.add 128#64)) :
    runSlice (kernel.bb2 p) E 52 1 s =
      .value (load_product1Env E v, s) := by
  have hf0 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (v 4) := packed_unflatten s.mem r v hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  simp [runSlice, kernel.bb2, load_product1Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0]

theorem load_product1_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%790) = .value (r.add 128#64)) :
    (kernel.bb2 p).runBodyFrom E 52 s =
      (kernel.bb2 p).runBodyFrom (load_product1Env E v) 53 s := by
  exact runBodyFrom_slice _ E (load_product1Env E v) 52 1 s s
    (load_product1_slice p E s r v hr hv hp0)

theorem load_product1_reads (E : ⟪kernel.Γ⟫) (v : PointBlocks) :
    (load_product1Env E v).read (%844) = Ty.wrap (v 4) := by
  simp [load_product1Env, mlir_env, -reduceShufflevector]

theorem load_product1_constants (E : ⟪kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load_product1Env E v) := by
  constructor <;> simp [load_product1Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN]

theorem load_product1_frame (E : ⟪kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 844 845 E (load_product1Env E v) := by
  unfold load_product1Env
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load_resultEnv (E : ⟪kernel.Γ⟫) (v : PointBlocks) : ⟪kernel.Γ⟫ :=
  E[%876 := Ty.wrap (v 0), %877 := Ty.wrap (v 1), %878 := Ty.wrap (v 2), %879 := Ty.wrap (v 3), %880 := Ty.wrap (v 4)]

theorem load_result_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%358) = .value r)
    (hp1 : E.read (%799) = .value (r.add 32#64))
    (hp2 : E.read (%800) = .value (r.add 64#64))
    (hp3 : E.read (%801) = .value (r.add 96#64))
    (hp4 : E.read (%802) = .value (r.add 128#64)) :
    runSlice (kernel.bb2 p) E 100 5 s =
      .value (load_resultEnv E v, s) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 0#64) 256) =
      Ty.wrap (v 0) := packed_unflatten s.mem r v hv 0
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hv1 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 32#64) 256) =
      Ty.wrap (v 1) := packed_unflatten s.mem r v hv 1
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv1
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hv2 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 64#64) 256) =
      Ty.wrap (v 2) := packed_unflatten s.mem r v hv 2
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv2
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hv3 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 96#64) 256) =
      Ty.wrap (v 3) := packed_unflatten s.mem r v hv 3
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv3
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv4 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (v 4) := packed_unflatten s.mem r v hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv4
  simp only [Pointer.add_zero] at hf0 hv0
  simp [runSlice, kernel.bb2, load_resultEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

theorem load_result_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%358) = .value r)
    (hp1 : E.read (%799) = .value (r.add 32#64))
    (hp2 : E.read (%800) = .value (r.add 64#64))
    (hp3 : E.read (%801) = .value (r.add 96#64))
    (hp4 : E.read (%802) = .value (r.add 128#64)) :
    (kernel.bb2 p).runBodyFrom E 100 s =
      (kernel.bb2 p).runBodyFrom (load_resultEnv E v) 105 s := by
  exact runBodyFrom_slice _ E (load_resultEnv E v) 100 5 s s
    (load_result_slice p E s r v hr hv hp0 hp1 hp2 hp3 hp4)

theorem load_result_reads (E : ⟪kernel.Γ⟫) (v : PointBlocks) :
    (load_resultEnv E v).read (%876) = Ty.wrap (v 0) ∧
    (load_resultEnv E v).read (%877) = Ty.wrap (v 1) ∧
    (load_resultEnv E v).read (%878) = Ty.wrap (v 2) ∧
    (load_resultEnv E v).read (%879) = Ty.wrap (v 3) ∧
    (load_resultEnv E v).read (%880) = Ty.wrap (v 4) := by
  simp [load_resultEnv, mlir_env, -reduceShufflevector]

theorem load_result_constants (E : ⟪kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load_resultEnv E v) := by
  constructor <;> simp [load_resultEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN]

theorem load_result_frame (E : ⟪kernel.Γ⟫) (v : PointBlocks) :
    RegisterFrame 876 881 E (load_resultEnv E v) := by
  unfold load_resultEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime_40_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 40 1 s = .value (E, s) := by
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime_40_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 40 s =
      (kernel.bb2 p).runBodyFrom E 41 s := by
  exact runBodyFrom_slice _ E E 40 1 s s (lifetime_40_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime_43_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 43 1 s = .value (E, s) := by
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime_43_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 43 s =
      (kernel.bb2 p).runBodyFrom E 44 s := by
  exact runBodyFrom_slice _ E E 43 1 s s (lifetime_43_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime_74_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 74 1 s = .value (E, s) := by
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime_74_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 74 s =
      (kernel.bb2 p).runBodyFrom E 75 s := by
  exact runBodyFrom_slice _ E E 74 1 s s (lifetime_74_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime_85_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 85 1 s = .value (E, s) := by
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime_85_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 85 s =
      (kernel.bb2 p).runBodyFrom E 86 s := by
  exact runBodyFrom_slice _ E E 85 1 s s (lifetime_85_slice p E s)

/-- The imported lifetime instructions have the identity RIR semantics. -/
theorem lifetime_97_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 97 3 s = .value (E, s) := by
  simp [runSlice, kernel.bb2, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq]

theorem lifetime_97_continue (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    (kernel.bb2 p).runBodyFrom E 97 s =
      (kernel.bb2 p).runBodyFrom E 100 s := by
  exact runBodyFrom_slice _ E E 97 3 s s (lifetime_97_slice p E s)


end Agave.Ed25519.Tables.Avx2Constructor.Add
