import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMemory
import SSA.Projects.RIR.Run.Memory

/-! Generated source candidates: small exact instruction intervals from the
unchanged double-base CFG. Kernel checking, not this generator, establishes
each execution equality. Field contracts use explicit packed register reads. -/
namespace Agave.Ed25519.Avx2PointAdd.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR Phases

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

/-- The five actual stores following prepare22; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem prepare22_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%253) = .value r)
    (hv0 : E.read (%574) = Ty.wrap (v 0))
    (hp1 : E.read (%359) = .value (r.add 32#64))
    (hv1 : E.read (%575) = Ty.wrap (v 1))
    (hp2 : E.read (%360) = .value (r.add 64#64))
    (hv2 : E.read (%576) = Ty.wrap (v 2))
    (hp3 : E.read (%361) = .value (r.add 96#64))
    (hv3 : E.read (%577) = Ty.wrap (v 3))
    (hp4 : E.read (%362) = .value (r.add 128#64))
    (hv4 : E.read (%578) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb22 p) E 57 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb22, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem prepare22_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%253) = .value r)
    (hv0 : E.read (%574) = Ty.wrap (v 0))
    (hp1 : E.read (%359) = .value (r.add 32#64))
    (hv1 : E.read (%575) = Ty.wrap (v 1))
    (hp2 : E.read (%360) = .value (r.add 64#64))
    (hv2 : E.read (%576) = Ty.wrap (v 2))
    (hp3 : E.read (%361) = .value (r.add 96#64))
    (hv3 : E.read (%577) = Ty.wrap (v 3))
    (hp4 : E.read (%362) = .value (r.add 128#64))
    (hv4 : E.read (%578) = Ty.wrap (v 4)) :
    (avx2Kernel.bb22 p).runBodyFrom E 57 s =
      (avx2Kernel.bb22 p).runBodyFrom E 62
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 57 5 s _
    (prepare22_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following adda22; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem adda22_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%251) = .value r)
    (hv0 : E.read (%609) = Ty.wrap (v 0))
    (hp1 : E.read (%363) = .value (r.add 32#64))
    (hv1 : E.read (%610) = Ty.wrap (v 1))
    (hp2 : E.read (%364) = .value (r.add 64#64))
    (hv2 : E.read (%611) = Ty.wrap (v 2))
    (hp3 : E.read (%365) = .value (r.add 96#64))
    (hv3 : E.read (%612) = Ty.wrap (v 3))
    (hp4 : E.read (%366) = .value (r.add 128#64))
    (hv4 : E.read (%613) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb22 p) E 102 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb22, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem adda22_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%251) = .value r)
    (hv0 : E.read (%609) = Ty.wrap (v 0))
    (hp1 : E.read (%363) = .value (r.add 32#64))
    (hv1 : E.read (%610) = Ty.wrap (v 1))
    (hp2 : E.read (%364) = .value (r.add 64#64))
    (hv2 : E.read (%611) = Ty.wrap (v 2))
    (hp3 : E.read (%365) = .value (r.add 96#64))
    (hv3 : E.read (%612) = Ty.wrap (v 3))
    (hp4 : E.read (%366) = .value (r.add 128#64))
    (hv4 : E.read (%613) = Ty.wrap (v 4)) :
    (avx2Kernel.bb22 p).runBodyFrom E 102 s =
      (avx2Kernel.bb22 p).runBodyFrom E 107
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 102 5 s _
    (adda22_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following cbcb22; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem cbcb22_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%250) = .value r)
    (hv0 : E.read (%614) = Ty.wrap (v 0))
    (hp1 : E.read (%367) = .value (r.add 32#64))
    (hv1 : E.read (%615) = Ty.wrap (v 1))
    (hp2 : E.read (%368) = .value (r.add 64#64))
    (hv2 : E.read (%616) = Ty.wrap (v 2))
    (hp3 : E.read (%369) = .value (r.add 96#64))
    (hv3 : E.read (%617) = Ty.wrap (v 3))
    (hp4 : E.read (%370) = .value (r.add 128#64))
    (hv4 : E.read (%618) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb22 p) E 113 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb22, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem cbcb22_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%250) = .value r)
    (hv0 : E.read (%614) = Ty.wrap (v 0))
    (hp1 : E.read (%367) = .value (r.add 32#64))
    (hv1 : E.read (%615) = Ty.wrap (v 1))
    (hp2 : E.read (%368) = .value (r.add 64#64))
    (hv2 : E.read (%616) = Ty.wrap (v 2))
    (hp3 : E.read (%369) = .value (r.add 96#64))
    (hv3 : E.read (%617) = Ty.wrap (v 3))
    (hp4 : E.read (%370) = .value (r.add 128#64))
    (hv4 : E.read (%618) = Ty.wrap (v 4)) :
    (avx2Kernel.bb22 p).runBodyFrom E 113 s =
      (avx2Kernel.bb22 p).runBodyFrom E 118
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 113 5 s _
    (cbcb22_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following negate22; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem negate22_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%254) = .value r)
    (hv0 : E.read (%549) = Ty.wrap (v 0))
    (hp1 : E.read (%355) = .value (r.add 32#64))
    (hv1 : E.read (%550) = Ty.wrap (v 1))
    (hp2 : E.read (%356) = .value (r.add 64#64))
    (hv2 : E.read (%551) = Ty.wrap (v 2))
    (hp3 : E.read (%357) = .value (r.add 96#64))
    (hv3 : E.read (%552) = Ty.wrap (v 3))
    (hp4 : E.read (%358) = .value (r.add 128#64))
    (hv4 : E.read (%553) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb22 p) E 26 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb22, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem negate22_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%254) = .value r)
    (hv0 : E.read (%549) = Ty.wrap (v 0))
    (hp1 : E.read (%355) = .value (r.add 32#64))
    (hv1 : E.read (%550) = Ty.wrap (v 1))
    (hp2 : E.read (%356) = .value (r.add 64#64))
    (hv2 : E.read (%551) = Ty.wrap (v 2))
    (hp3 : E.read (%357) = .value (r.add 96#64))
    (hv3 : E.read (%552) = Ty.wrap (v 3))
    (hp4 : E.read (%358) = .value (r.add 128#64))
    (hv4 : E.read (%553) = Ty.wrap (v 4)) :
    (avx2Kernel.bb22 p).runBodyFrom E 26 s =
      (avx2Kernel.bb22 p).runBodyFrom E 31
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 26 5 s _
    (negate22_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following prepare25; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem prepare25_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%249) = .value r)
    (hv0 : E.read (%648) = Ty.wrap (v 0))
    (hp1 : E.read (%339) = .value (r.add 32#64))
    (hv1 : E.read (%649) = Ty.wrap (v 1))
    (hp2 : E.read (%340) = .value (r.add 64#64))
    (hv2 : E.read (%650) = Ty.wrap (v 2))
    (hp3 : E.read (%341) = .value (r.add 96#64))
    (hv3 : E.read (%651) = Ty.wrap (v 3))
    (hp4 : E.read (%342) = .value (r.add 128#64))
    (hv4 : E.read (%652) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb25 p) E 27 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb25, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem prepare25_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%249) = .value r)
    (hv0 : E.read (%648) = Ty.wrap (v 0))
    (hp1 : E.read (%339) = .value (r.add 32#64))
    (hv1 : E.read (%649) = Ty.wrap (v 1))
    (hp2 : E.read (%340) = .value (r.add 64#64))
    (hv2 : E.read (%650) = Ty.wrap (v 2))
    (hp3 : E.read (%341) = .value (r.add 96#64))
    (hv3 : E.read (%651) = Ty.wrap (v 3))
    (hp4 : E.read (%342) = .value (r.add 128#64))
    (hv4 : E.read (%652) = Ty.wrap (v 4)) :
    (avx2Kernel.bb25 p).runBodyFrom E 27 s =
      (avx2Kernel.bb25 p).runBodyFrom E 32
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 27 5 s _
    (prepare25_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following adda25; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem adda25_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%247) = .value r)
    (hv0 : E.read (%683) = Ty.wrap (v 0))
    (hp1 : E.read (%343) = .value (r.add 32#64))
    (hv1 : E.read (%684) = Ty.wrap (v 1))
    (hp2 : E.read (%344) = .value (r.add 64#64))
    (hv2 : E.read (%685) = Ty.wrap (v 2))
    (hp3 : E.read (%345) = .value (r.add 96#64))
    (hv3 : E.read (%686) = Ty.wrap (v 3))
    (hp4 : E.read (%346) = .value (r.add 128#64))
    (hv4 : E.read (%687) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb25 p) E 72 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb25, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem adda25_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%247) = .value r)
    (hv0 : E.read (%683) = Ty.wrap (v 0))
    (hp1 : E.read (%343) = .value (r.add 32#64))
    (hv1 : E.read (%684) = Ty.wrap (v 1))
    (hp2 : E.read (%344) = .value (r.add 64#64))
    (hv2 : E.read (%685) = Ty.wrap (v 2))
    (hp3 : E.read (%345) = .value (r.add 96#64))
    (hv3 : E.read (%686) = Ty.wrap (v 3))
    (hp4 : E.read (%346) = .value (r.add 128#64))
    (hv4 : E.read (%687) = Ty.wrap (v 4)) :
    (avx2Kernel.bb25 p).runBodyFrom E 72 s =
      (avx2Kernel.bb25 p).runBodyFrom E 77
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 72 5 s _
    (adda25_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following cbcb25; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem cbcb25_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%246) = .value r)
    (hv0 : E.read (%688) = Ty.wrap (v 0))
    (hp1 : E.read (%347) = .value (r.add 32#64))
    (hv1 : E.read (%689) = Ty.wrap (v 1))
    (hp2 : E.read (%348) = .value (r.add 64#64))
    (hv2 : E.read (%690) = Ty.wrap (v 2))
    (hp3 : E.read (%349) = .value (r.add 96#64))
    (hv3 : E.read (%691) = Ty.wrap (v 3))
    (hp4 : E.read (%350) = .value (r.add 128#64))
    (hv4 : E.read (%692) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb25 p) E 83 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb25, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem cbcb25_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%246) = .value r)
    (hv0 : E.read (%688) = Ty.wrap (v 0))
    (hp1 : E.read (%347) = .value (r.add 32#64))
    (hv1 : E.read (%689) = Ty.wrap (v 1))
    (hp2 : E.read (%348) = .value (r.add 64#64))
    (hv2 : E.read (%690) = Ty.wrap (v 2))
    (hp3 : E.read (%349) = .value (r.add 96#64))
    (hv3 : E.read (%691) = Ty.wrap (v 3))
    (hp4 : E.read (%350) = .value (r.add 128#64))
    (hv4 : E.read (%692) = Ty.wrap (v 4)) :
    (avx2Kernel.bb25 p).runBodyFrom E 83 s =
      (avx2Kernel.bb25 p).runBodyFrom E 88
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 83 5 s _
    (cbcb25_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following prepare29; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem prepare29_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%244) = .value r)
    (hv0 : E.read (%755) = Ty.wrap (v 0))
    (hp1 : E.read (%395) = .value (r.add 32#64))
    (hv1 : E.read (%756) = Ty.wrap (v 1))
    (hp2 : E.read (%396) = .value (r.add 64#64))
    (hv2 : E.read (%757) = Ty.wrap (v 2))
    (hp3 : E.read (%397) = .value (r.add 96#64))
    (hv3 : E.read (%758) = Ty.wrap (v 3))
    (hp4 : E.read (%398) = .value (r.add 128#64))
    (hv4 : E.read (%759) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb29 p) E 57 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb29, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem prepare29_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%244) = .value r)
    (hv0 : E.read (%755) = Ty.wrap (v 0))
    (hp1 : E.read (%395) = .value (r.add 32#64))
    (hv1 : E.read (%756) = Ty.wrap (v 1))
    (hp2 : E.read (%396) = .value (r.add 64#64))
    (hv2 : E.read (%757) = Ty.wrap (v 2))
    (hp3 : E.read (%397) = .value (r.add 96#64))
    (hv3 : E.read (%758) = Ty.wrap (v 3))
    (hp4 : E.read (%398) = .value (r.add 128#64))
    (hv4 : E.read (%759) = Ty.wrap (v 4)) :
    (avx2Kernel.bb29 p).runBodyFrom E 57 s =
      (avx2Kernel.bb29 p).runBodyFrom E 62
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 57 5 s _
    (prepare29_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following adda29; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem adda29_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%242) = .value r)
    (hv0 : E.read (%790) = Ty.wrap (v 0))
    (hp1 : E.read (%399) = .value (r.add 32#64))
    (hv1 : E.read (%791) = Ty.wrap (v 1))
    (hp2 : E.read (%400) = .value (r.add 64#64))
    (hv2 : E.read (%792) = Ty.wrap (v 2))
    (hp3 : E.read (%401) = .value (r.add 96#64))
    (hv3 : E.read (%793) = Ty.wrap (v 3))
    (hp4 : E.read (%402) = .value (r.add 128#64))
    (hv4 : E.read (%794) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb29 p) E 102 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb29, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem adda29_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%242) = .value r)
    (hv0 : E.read (%790) = Ty.wrap (v 0))
    (hp1 : E.read (%399) = .value (r.add 32#64))
    (hv1 : E.read (%791) = Ty.wrap (v 1))
    (hp2 : E.read (%400) = .value (r.add 64#64))
    (hv2 : E.read (%792) = Ty.wrap (v 2))
    (hp3 : E.read (%401) = .value (r.add 96#64))
    (hv3 : E.read (%793) = Ty.wrap (v 3))
    (hp4 : E.read (%402) = .value (r.add 128#64))
    (hv4 : E.read (%794) = Ty.wrap (v 4)) :
    (avx2Kernel.bb29 p).runBodyFrom E 102 s =
      (avx2Kernel.bb29 p).runBodyFrom E 107
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 102 5 s _
    (adda29_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following cbcb29; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem cbcb29_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%241) = .value r)
    (hv0 : E.read (%795) = Ty.wrap (v 0))
    (hp1 : E.read (%403) = .value (r.add 32#64))
    (hv1 : E.read (%796) = Ty.wrap (v 1))
    (hp2 : E.read (%404) = .value (r.add 64#64))
    (hv2 : E.read (%797) = Ty.wrap (v 2))
    (hp3 : E.read (%405) = .value (r.add 96#64))
    (hv3 : E.read (%798) = Ty.wrap (v 3))
    (hp4 : E.read (%406) = .value (r.add 128#64))
    (hv4 : E.read (%799) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb29 p) E 113 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb29, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem cbcb29_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%241) = .value r)
    (hv0 : E.read (%795) = Ty.wrap (v 0))
    (hp1 : E.read (%403) = .value (r.add 32#64))
    (hv1 : E.read (%796) = Ty.wrap (v 1))
    (hp2 : E.read (%404) = .value (r.add 64#64))
    (hv2 : E.read (%797) = Ty.wrap (v 2))
    (hp3 : E.read (%405) = .value (r.add 96#64))
    (hv3 : E.read (%798) = Ty.wrap (v 3))
    (hp4 : E.read (%406) = .value (r.add 128#64))
    (hv4 : E.read (%799) = Ty.wrap (v 4)) :
    (avx2Kernel.bb29 p).runBodyFrom E 113 s =
      (avx2Kernel.bb29 p).runBodyFrom E 118
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 113 5 s _
    (cbcb29_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following negate29; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem negate29_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%245) = .value r)
    (hv0 : E.read (%730) = Ty.wrap (v 0))
    (hp1 : E.read (%391) = .value (r.add 32#64))
    (hv1 : E.read (%731) = Ty.wrap (v 1))
    (hp2 : E.read (%392) = .value (r.add 64#64))
    (hv2 : E.read (%732) = Ty.wrap (v 2))
    (hp3 : E.read (%393) = .value (r.add 96#64))
    (hv3 : E.read (%733) = Ty.wrap (v 3))
    (hp4 : E.read (%394) = .value (r.add 128#64))
    (hv4 : E.read (%734) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb29 p) E 26 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb29, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem negate29_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%245) = .value r)
    (hv0 : E.read (%730) = Ty.wrap (v 0))
    (hp1 : E.read (%391) = .value (r.add 32#64))
    (hv1 : E.read (%731) = Ty.wrap (v 1))
    (hp2 : E.read (%392) = .value (r.add 64#64))
    (hv2 : E.read (%732) = Ty.wrap (v 2))
    (hp3 : E.read (%393) = .value (r.add 96#64))
    (hv3 : E.read (%733) = Ty.wrap (v 3))
    (hp4 : E.read (%394) = .value (r.add 128#64))
    (hv4 : E.read (%734) = Ty.wrap (v 4)) :
    (avx2Kernel.bb29 p).runBodyFrom E 26 s =
      (avx2Kernel.bb29 p).runBodyFrom E 31
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 26 5 s _
    (negate29_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following prepare33; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem prepare33_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%240) = .value r)
    (hv0 : E.read (%836) = Ty.wrap (v 0))
    (hp1 : E.read (%375) = .value (r.add 32#64))
    (hv1 : E.read (%837) = Ty.wrap (v 1))
    (hp2 : E.read (%376) = .value (r.add 64#64))
    (hv2 : E.read (%838) = Ty.wrap (v 2))
    (hp3 : E.read (%377) = .value (r.add 96#64))
    (hv3 : E.read (%839) = Ty.wrap (v 3))
    (hp4 : E.read (%378) = .value (r.add 128#64))
    (hv4 : E.read (%840) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb33 p) E 27 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb33, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem prepare33_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%240) = .value r)
    (hv0 : E.read (%836) = Ty.wrap (v 0))
    (hp1 : E.read (%375) = .value (r.add 32#64))
    (hv1 : E.read (%837) = Ty.wrap (v 1))
    (hp2 : E.read (%376) = .value (r.add 64#64))
    (hv2 : E.read (%838) = Ty.wrap (v 2))
    (hp3 : E.read (%377) = .value (r.add 96#64))
    (hv3 : E.read (%839) = Ty.wrap (v 3))
    (hp4 : E.read (%378) = .value (r.add 128#64))
    (hv4 : E.read (%840) = Ty.wrap (v 4)) :
    (avx2Kernel.bb33 p).runBodyFrom E 27 s =
      (avx2Kernel.bb33 p).runBodyFrom E 32
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 27 5 s _
    (prepare33_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following adda33; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem adda33_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%238) = .value r)
    (hv0 : E.read (%871) = Ty.wrap (v 0))
    (hp1 : E.read (%379) = .value (r.add 32#64))
    (hv1 : E.read (%872) = Ty.wrap (v 1))
    (hp2 : E.read (%380) = .value (r.add 64#64))
    (hv2 : E.read (%873) = Ty.wrap (v 2))
    (hp3 : E.read (%381) = .value (r.add 96#64))
    (hv3 : E.read (%874) = Ty.wrap (v 3))
    (hp4 : E.read (%382) = .value (r.add 128#64))
    (hv4 : E.read (%875) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb33 p) E 72 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb33, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem adda33_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%238) = .value r)
    (hv0 : E.read (%871) = Ty.wrap (v 0))
    (hp1 : E.read (%379) = .value (r.add 32#64))
    (hv1 : E.read (%872) = Ty.wrap (v 1))
    (hp2 : E.read (%380) = .value (r.add 64#64))
    (hv2 : E.read (%873) = Ty.wrap (v 2))
    (hp3 : E.read (%381) = .value (r.add 96#64))
    (hv3 : E.read (%874) = Ty.wrap (v 3))
    (hp4 : E.read (%382) = .value (r.add 128#64))
    (hv4 : E.read (%875) = Ty.wrap (v 4)) :
    (avx2Kernel.bb33 p).runBodyFrom E 72 s =
      (avx2Kernel.bb33 p).runBodyFrom E 77
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 72 5 s _
    (adda33_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)

/-- The five actual stores following cbcb33; their arguments are the
already-proved output vectors, without expanding the preceding arithmetic. -/
theorem cbcb33_store_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%237) = .value r)
    (hv0 : E.read (%876) = Ty.wrap (v 0))
    (hp1 : E.read (%383) = .value (r.add 32#64))
    (hv1 : E.read (%877) = Ty.wrap (v 1))
    (hp2 : E.read (%384) = .value (r.add 64#64))
    (hv2 : E.read (%878) = Ty.wrap (v 2))
    (hp3 : E.read (%385) = .value (r.add 96#64))
    (hv3 : E.read (%879) = Ty.wrap (v 3))
    (hp4 : E.read (%386) = .value (r.add 128#64))
    (hv4 : E.read (%880) = Ty.wrap (v 4)) :
    runSlice (avx2Kernel.bb33 p) E 83 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, avx2Kernel.bb33, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem cbcb33_store_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Phases.PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hp0 : E.read (%237) = .value r)
    (hv0 : E.read (%876) = Ty.wrap (v 0))
    (hp1 : E.read (%383) = .value (r.add 32#64))
    (hv1 : E.read (%877) = Ty.wrap (v 1))
    (hp2 : E.read (%384) = .value (r.add 64#64))
    (hv2 : E.read (%878) = Ty.wrap (v 2))
    (hp3 : E.read (%385) = .value (r.add 96#64))
    (hv3 : E.read (%879) = Ty.wrap (v 3))
    (hp4 : E.read (%386) = .value (r.add 128#64))
    (hv4 : E.read (%880) = Ty.wrap (v 4)) :
    (avx2Kernel.bb33 p).runBodyFrom E 83 s =
      (avx2Kernel.bb33 p).runBodyFrom E 88
        {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v} := by
  exact runBodyFrom_slice _ E E 83 5 s _
    (cbcb33_store_slice p E s r v hr hp0 hv0 hp1 hv1 hp2 hv2 hp3 hv3 hp4 hv4)


end Agave.Ed25519.Avx2PointAdd.CFG
