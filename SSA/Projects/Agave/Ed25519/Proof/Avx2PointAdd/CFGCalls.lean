import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMultiplication

/-! Generated source candidates: small exact instruction intervals from the
unchanged double-base CFG. Kernel checking, not this generator, establishes
each execution equality. Field contracts use explicit packed register reads. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

/-- The actual first field-helper call
instruction in bb22, with a packed point result and restored limb bounds. -/
theorem multiply22_0_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%252) = .value r)
    (hpa : E.read (%253) = .value a)
    (hpb : E.read (%254) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb22 p) E 63 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply22_0_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%252) = .value r)
    (hpa : E.read (%253) = .value a)
    (hpb : E.read (%254) = .value b) :
    runSlice (avx2Kernel.bb22 p) E 63 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual second field-helper call
instruction in bb22, with a packed point result and restored limb bounds. -/
theorem multiply22_1_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%261) = .value r)
    (hpa : E.read (%251) = .value a)
    (hpb : E.read (%250) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb22 p) E 118 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply22_1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%261) = .value r)
    (hpa : E.read (%251) = .value a)
    (hpb : E.read (%250) = .value b) :
    runSlice (avx2Kernel.bb22 p) E 118 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb22, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual first field-helper call
instruction in bb25, with a packed point result and restored limb bounds. -/
theorem multiply25_0_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%248) = .value r)
    (hpa : E.read (%249) = .value a)
    (hpb : E.read (%627) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb25 p) E 33 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply25_0_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%248) = .value r)
    (hpa : E.read (%249) = .value a)
    (hpb : E.read (%627) = .value b) :
    runSlice (avx2Kernel.bb25 p) E 33 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual second field-helper call
instruction in bb25, with a packed point result and restored limb bounds. -/
theorem multiply25_1_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%262) = .value r)
    (hpa : E.read (%247) = .value a)
    (hpb : E.read (%246) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb25 p) E 88 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply25_1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%262) = .value r)
    (hpa : E.read (%247) = .value a)
    (hpb : E.read (%246) = .value b) :
    runSlice (avx2Kernel.bb25 p) E 88 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb25, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual first field-helper call
instruction in bb29, with a packed point result and restored limb bounds. -/
theorem multiply29_0_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%243) = .value r)
    (hpa : E.read (%244) = .value a)
    (hpb : E.read (%245) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb29 p) E 63 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply29_0_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%243) = .value r)
    (hpa : E.read (%244) = .value a)
    (hpb : E.read (%245) = .value b) :
    runSlice (avx2Kernel.bb29 p) E 63 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual second field-helper call
instruction in bb29, with a packed point result and restored limb bounds. -/
theorem multiply29_1_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%259) = .value r)
    (hpa : E.read (%242) = .value a)
    (hpb : E.read (%241) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb29 p) E 118 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply29_1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%259) = .value r)
    (hpa : E.read (%242) = .value a)
    (hpb : E.read (%241) = .value b) :
    runSlice (avx2Kernel.bb29 p) E 118 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb29, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual first field-helper call
instruction in bb33, with a packed point result and restored limb bounds. -/
theorem multiply33_0_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%239) = .value r)
    (hpa : E.read (%240) = .value a)
    (hpb : E.read (%815) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb33 p) E 33 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply33_0_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%239) = .value r)
    (hpa : E.read (%240) = .value a)
    (hpb : E.read (%815) = .value b) :
    runSlice (avx2Kernel.bb33 p) E 33 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- The actual second field-helper call
instruction in bb33, with a packed point result and restored limb bounds. -/
theorem multiply33_1_field (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%260) = .value r)
    (hpa : E.read (%238) = .value a)
    (hpb : E.read (%237) = .value b) :
    ∃ s' : GlobalState,
      runSlice (avx2Kernel.bb33 p) E 88 1 s = .value (E, s') ∧
      Avx2FieldMul.Execution.readBlocks s'.mem r = packPoint (multiply P Q) ∧
      pointReduced (multiply P Q) ∧
      pointValue (Avx2PointAdd.Execution.readPoint s'.mem r) =
        laneMul (pointValue P) (pointValue Q) := by
  obtain ⟨s', hcall, hout, hred, hvalue⟩ := multiply_packed_of_contract p.call2 hmul
    r a b s P Q hwf hr ha hb hP hQ hA hB
  refine ⟨s', ?_, hout, hred, hvalue⟩
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]

/-- Exact state boundary for composing the caller's next memory phase. -/
theorem multiply33_1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r a b : Pointer) (P Q : Point)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2)
    (hwf : s.WF) (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (ha : Reduce64.Execution.SmallRange s.mem a 160)
    (hb : Reduce64.Execution.SmallRange s.mem b 160)
    (hP : pointWide P) (hQ : pointWide Q)
    (hA : Avx2FieldMul.Execution.readBlocks s.mem a = packPoint P)
    (hB : Avx2FieldMul.Execution.readBlocks s.mem b = packPoint Q)
    (hpr : E.read (%260) = .value r)
    (hpa : E.read (%238) = .value a)
    (hpb : E.read (%237) = .value b) :
    runSlice (avx2Kernel.bb33 p) E 88 1 s =
      .value (E, {s with mem := (Avx2FieldMul.Execution.storeBlocks s.mem r
        (packPoint (multiply P Q)))}) := by
  have hcall := multiply_packed_state p.call2 hmul r a b s P Q
    hwf hr ha hb hP hQ hA hB
  dsimp only [Avx2PointAdd.Execution.mulArgs] at hcall
  simp [runSlice, avx2Kernel.bb33, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpr, hpa, hpb, hcall]


end Agave.Ed25519.Avx2PointAdd.CFG
