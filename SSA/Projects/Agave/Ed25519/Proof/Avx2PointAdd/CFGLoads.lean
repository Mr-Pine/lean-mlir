import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseTable
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

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load22_product4Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%579 := Ty.wrap (v 0), %580 := Ty.wrap (v 1), %581 := Ty.wrap (v 2), %582 := Ty.wrap (v 3)]

theorem load22_product4_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%253) = .value r)
    (hp1 : E.read (%359) = .value (r.add 32#64))
    (hp2 : E.read (%360) = .value (r.add 64#64))
    (hp3 : E.read (%361) = .value (r.add 96#64)) :
    runSlice (avx2Kernel.bb22 p) E 66 4 s =
      .value (load22_product4Env E v, s) := by
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
  simp [runSlice, avx2Kernel.bb22, load22_product4Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3]

theorem load22_product4_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%253) = .value r)
    (hp1 : E.read (%359) = .value (r.add 32#64))
    (hp2 : E.read (%360) = .value (r.add 64#64))
    (hp3 : E.read (%361) = .value (r.add 96#64)) :
    (avx2Kernel.bb22 p).runBodyFrom E 66 s =
      (avx2Kernel.bb22 p).runBodyFrom (load22_product4Env E v) 70 s := by
  exact runBodyFrom_slice _ E (load22_product4Env E v) 66 4 s s
    (load22_product4_slice p E s r v hr hv hp0 hp1 hp2 hp3)

theorem load22_product4_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load22_product4Env E v).read (%579) = Ty.wrap (v 0) ∧
    (load22_product4Env E v).read (%580) = Ty.wrap (v 1) ∧
    (load22_product4Env E v).read (%581) = Ty.wrap (v 2) ∧
    (load22_product4Env E v).read (%582) = Ty.wrap (v 3) := by
  simp [load22_product4Env, mlir_env]

theorem load22_product4_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load22_product4Env E v) := by
  constructor <;> simp [load22_product4Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load22_product1Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%587 := Ty.wrap (v 4)]

theorem load22_product1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%362) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb22 p) E 74 1 s =
      .value (load22_product1Env E v, s) := by
  have hf0 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (v 4) := packed_unflatten s.mem r v hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  simp [runSlice, avx2Kernel.bb22, load22_product1Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0]

theorem load22_product1_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%362) = .value (r.add 128#64)) :
    (avx2Kernel.bb22 p).runBodyFrom E 74 s =
      (avx2Kernel.bb22 p).runBodyFrom (load22_product1Env E v) 75 s := by
  exact runBodyFrom_slice _ E (load22_product1Env E v) 74 1 s s
    (load22_product1_slice p E s r v hr hv hp0)

theorem load22_product1_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load22_product1Env E v).read (%587) = Ty.wrap (v 4) := by
  simp [load22_product1Env, mlir_env]

theorem load22_product1_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load22_product1Env E v) := by
  constructor <;> simp [load22_product1Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load22_resultEnv (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%619 := Ty.wrap (v 0), %620 := Ty.wrap (v 1), %621 := Ty.wrap (v 2), %622 := Ty.wrap (v 3), %623 := Ty.wrap (v 4)]

theorem load22_result_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%261) = .value r)
    (hp1 : E.read (%371) = .value (r.add 32#64))
    (hp2 : E.read (%372) = .value (r.add 64#64))
    (hp3 : E.read (%373) = .value (r.add 96#64))
    (hp4 : E.read (%374) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb22 p) E 123 5 s =
      .value (load22_resultEnv E v, s) := by
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
  simp [runSlice, avx2Kernel.bb22, load22_resultEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

theorem load22_result_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%261) = .value r)
    (hp1 : E.read (%371) = .value (r.add 32#64))
    (hp2 : E.read (%372) = .value (r.add 64#64))
    (hp3 : E.read (%373) = .value (r.add 96#64))
    (hp4 : E.read (%374) = .value (r.add 128#64)) :
    (avx2Kernel.bb22 p).runBodyFrom E 123 s =
      (avx2Kernel.bb22 p).runBodyFrom (load22_resultEnv E v) 128 s := by
  exact runBodyFrom_slice _ E (load22_resultEnv E v) 123 5 s s
    (load22_result_slice p E s r v hr hv hp0 hp1 hp2 hp3 hp4)

theorem load22_result_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load22_resultEnv E v).read (%619) = Ty.wrap (v 0) ∧
    (load22_resultEnv E v).read (%620) = Ty.wrap (v 1) ∧
    (load22_resultEnv E v).read (%621) = Ty.wrap (v 2) ∧
    (load22_resultEnv E v).read (%622) = Ty.wrap (v 3) ∧
    (load22_resultEnv E v).read (%623) = Ty.wrap (v 4) := by
  simp [load22_resultEnv, mlir_env]

theorem load22_result_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load22_resultEnv E v) := by
  constructor <;> simp [load22_resultEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load25_product4Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%653 := Ty.wrap (v 0), %654 := Ty.wrap (v 1), %655 := Ty.wrap (v 2), %656 := Ty.wrap (v 3)]

theorem load25_product4_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%249) = .value r)
    (hp1 : E.read (%339) = .value (r.add 32#64))
    (hp2 : E.read (%340) = .value (r.add 64#64))
    (hp3 : E.read (%341) = .value (r.add 96#64)) :
    runSlice (avx2Kernel.bb25 p) E 36 4 s =
      .value (load25_product4Env E v, s) := by
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
  simp [runSlice, avx2Kernel.bb25, load25_product4Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3]

theorem load25_product4_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%249) = .value r)
    (hp1 : E.read (%339) = .value (r.add 32#64))
    (hp2 : E.read (%340) = .value (r.add 64#64))
    (hp3 : E.read (%341) = .value (r.add 96#64)) :
    (avx2Kernel.bb25 p).runBodyFrom E 36 s =
      (avx2Kernel.bb25 p).runBodyFrom (load25_product4Env E v) 40 s := by
  exact runBodyFrom_slice _ E (load25_product4Env E v) 36 4 s s
    (load25_product4_slice p E s r v hr hv hp0 hp1 hp2 hp3)

theorem load25_product4_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load25_product4Env E v).read (%653) = Ty.wrap (v 0) ∧
    (load25_product4Env E v).read (%654) = Ty.wrap (v 1) ∧
    (load25_product4Env E v).read (%655) = Ty.wrap (v 2) ∧
    (load25_product4Env E v).read (%656) = Ty.wrap (v 3) := by
  simp [load25_product4Env, mlir_env]

theorem load25_product4_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load25_product4Env E v) := by
  constructor <;> simp [load25_product4Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load25_product1Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%661 := Ty.wrap (v 4)]

theorem load25_product1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%342) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb25 p) E 44 1 s =
      .value (load25_product1Env E v, s) := by
  have hf0 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (v 4) := packed_unflatten s.mem r v hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  simp [runSlice, avx2Kernel.bb25, load25_product1Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0]

theorem load25_product1_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%342) = .value (r.add 128#64)) :
    (avx2Kernel.bb25 p).runBodyFrom E 44 s =
      (avx2Kernel.bb25 p).runBodyFrom (load25_product1Env E v) 45 s := by
  exact runBodyFrom_slice _ E (load25_product1Env E v) 44 1 s s
    (load25_product1_slice p E s r v hr hv hp0)

theorem load25_product1_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load25_product1Env E v).read (%661) = Ty.wrap (v 4) := by
  simp [load25_product1Env, mlir_env]

theorem load25_product1_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load25_product1Env E v) := by
  constructor <;> simp [load25_product1Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load25_resultEnv (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%693 := Ty.wrap (v 0), %694 := Ty.wrap (v 1), %695 := Ty.wrap (v 2), %696 := Ty.wrap (v 3), %697 := Ty.wrap (v 4)]

theorem load25_result_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%262) = .value r)
    (hp1 : E.read (%351) = .value (r.add 32#64))
    (hp2 : E.read (%352) = .value (r.add 64#64))
    (hp3 : E.read (%353) = .value (r.add 96#64))
    (hp4 : E.read (%354) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb25 p) E 92 5 s =
      .value (load25_resultEnv E v, s) := by
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
  simp [runSlice, avx2Kernel.bb25, load25_resultEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

theorem load25_result_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%262) = .value r)
    (hp1 : E.read (%351) = .value (r.add 32#64))
    (hp2 : E.read (%352) = .value (r.add 64#64))
    (hp3 : E.read (%353) = .value (r.add 96#64))
    (hp4 : E.read (%354) = .value (r.add 128#64)) :
    (avx2Kernel.bb25 p).runBodyFrom E 92 s =
      (avx2Kernel.bb25 p).runBodyFrom (load25_resultEnv E v) 97 s := by
  exact runBodyFrom_slice _ E (load25_resultEnv E v) 92 5 s s
    (load25_result_slice p E s r v hr hv hp0 hp1 hp2 hp3 hp4)

theorem load25_result_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load25_resultEnv E v).read (%693) = Ty.wrap (v 0) ∧
    (load25_resultEnv E v).read (%694) = Ty.wrap (v 1) ∧
    (load25_resultEnv E v).read (%695) = Ty.wrap (v 2) ∧
    (load25_resultEnv E v).read (%696) = Ty.wrap (v 3) ∧
    (load25_resultEnv E v).read (%697) = Ty.wrap (v 4) := by
  simp [load25_resultEnv, mlir_env]

theorem load25_result_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load25_resultEnv E v) := by
  constructor <;> simp [load25_resultEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load29_product4Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%760 := Ty.wrap (v 0), %761 := Ty.wrap (v 1), %762 := Ty.wrap (v 2), %763 := Ty.wrap (v 3)]

theorem load29_product4_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%244) = .value r)
    (hp1 : E.read (%395) = .value (r.add 32#64))
    (hp2 : E.read (%396) = .value (r.add 64#64))
    (hp3 : E.read (%397) = .value (r.add 96#64)) :
    runSlice (avx2Kernel.bb29 p) E 66 4 s =
      .value (load29_product4Env E v, s) := by
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
  simp [runSlice, avx2Kernel.bb29, load29_product4Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3]

theorem load29_product4_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%244) = .value r)
    (hp1 : E.read (%395) = .value (r.add 32#64))
    (hp2 : E.read (%396) = .value (r.add 64#64))
    (hp3 : E.read (%397) = .value (r.add 96#64)) :
    (avx2Kernel.bb29 p).runBodyFrom E 66 s =
      (avx2Kernel.bb29 p).runBodyFrom (load29_product4Env E v) 70 s := by
  exact runBodyFrom_slice _ E (load29_product4Env E v) 66 4 s s
    (load29_product4_slice p E s r v hr hv hp0 hp1 hp2 hp3)

theorem load29_product4_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load29_product4Env E v).read (%760) = Ty.wrap (v 0) ∧
    (load29_product4Env E v).read (%761) = Ty.wrap (v 1) ∧
    (load29_product4Env E v).read (%762) = Ty.wrap (v 2) ∧
    (load29_product4Env E v).read (%763) = Ty.wrap (v 3) := by
  simp [load29_product4Env, mlir_env]

theorem load29_product4_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load29_product4Env E v) := by
  constructor <;> simp [load29_product4Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load29_product1Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%768 := Ty.wrap (v 4)]

theorem load29_product1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%398) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb29 p) E 74 1 s =
      .value (load29_product1Env E v, s) := by
  have hf0 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (v 4) := packed_unflatten s.mem r v hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  simp [runSlice, avx2Kernel.bb29, load29_product1Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0]

theorem load29_product1_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%398) = .value (r.add 128#64)) :
    (avx2Kernel.bb29 p).runBodyFrom E 74 s =
      (avx2Kernel.bb29 p).runBodyFrom (load29_product1Env E v) 75 s := by
  exact runBodyFrom_slice _ E (load29_product1Env E v) 74 1 s s
    (load29_product1_slice p E s r v hr hv hp0)

theorem load29_product1_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load29_product1Env E v).read (%768) = Ty.wrap (v 4) := by
  simp [load29_product1Env, mlir_env]

theorem load29_product1_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load29_product1Env E v) := by
  constructor <;> simp [load29_product1Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load29_resultEnv (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%800 := Ty.wrap (v 0), %801 := Ty.wrap (v 1), %802 := Ty.wrap (v 2), %803 := Ty.wrap (v 3), %804 := Ty.wrap (v 4)]

theorem load29_result_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%259) = .value r)
    (hp1 : E.read (%407) = .value (r.add 32#64))
    (hp2 : E.read (%408) = .value (r.add 64#64))
    (hp3 : E.read (%409) = .value (r.add 96#64))
    (hp4 : E.read (%410) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb29 p) E 123 5 s =
      .value (load29_resultEnv E v, s) := by
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
  simp [runSlice, avx2Kernel.bb29, load29_resultEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

theorem load29_result_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%259) = .value r)
    (hp1 : E.read (%407) = .value (r.add 32#64))
    (hp2 : E.read (%408) = .value (r.add 64#64))
    (hp3 : E.read (%409) = .value (r.add 96#64))
    (hp4 : E.read (%410) = .value (r.add 128#64)) :
    (avx2Kernel.bb29 p).runBodyFrom E 123 s =
      (avx2Kernel.bb29 p).runBodyFrom (load29_resultEnv E v) 128 s := by
  exact runBodyFrom_slice _ E (load29_resultEnv E v) 123 5 s s
    (load29_result_slice p E s r v hr hv hp0 hp1 hp2 hp3 hp4)

theorem load29_result_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load29_resultEnv E v).read (%800) = Ty.wrap (v 0) ∧
    (load29_resultEnv E v).read (%801) = Ty.wrap (v 1) ∧
    (load29_resultEnv E v).read (%802) = Ty.wrap (v 2) ∧
    (load29_resultEnv E v).read (%803) = Ty.wrap (v 3) ∧
    (load29_resultEnv E v).read (%804) = Ty.wrap (v 4) := by
  simp [load29_resultEnv, mlir_env]

theorem load29_result_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load29_resultEnv E v) := by
  constructor <;> simp [load29_resultEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load33_product4Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%841 := Ty.wrap (v 0), %842 := Ty.wrap (v 1), %843 := Ty.wrap (v 2), %844 := Ty.wrap (v 3)]

theorem load33_product4_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%240) = .value r)
    (hp1 : E.read (%375) = .value (r.add 32#64))
    (hp2 : E.read (%376) = .value (r.add 64#64))
    (hp3 : E.read (%377) = .value (r.add 96#64)) :
    runSlice (avx2Kernel.bb33 p) E 36 4 s =
      .value (load33_product4Env E v, s) := by
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
  simp [runSlice, avx2Kernel.bb33, load33_product4Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3]

theorem load33_product4_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%240) = .value r)
    (hp1 : E.read (%375) = .value (r.add 32#64))
    (hp2 : E.read (%376) = .value (r.add 64#64))
    (hp3 : E.read (%377) = .value (r.add 96#64)) :
    (avx2Kernel.bb33 p).runBodyFrom E 36 s =
      (avx2Kernel.bb33 p).runBodyFrom (load33_product4Env E v) 40 s := by
  exact runBodyFrom_slice _ E (load33_product4Env E v) 36 4 s s
    (load33_product4_slice p E s r v hr hv hp0 hp1 hp2 hp3)

theorem load33_product4_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load33_product4Env E v).read (%841) = Ty.wrap (v 0) ∧
    (load33_product4Env E v).read (%842) = Ty.wrap (v 1) ∧
    (load33_product4Env E v).read (%843) = Ty.wrap (v 2) ∧
    (load33_product4Env E v).read (%844) = Ty.wrap (v 3) := by
  simp [load33_product4Env, mlir_env]

theorem load33_product4_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load33_product4Env E v) := by
  constructor <;> simp [load33_product4Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load33_product1Env (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%849 := Ty.wrap (v 4)]

theorem load33_product1_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%378) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb33 p) E 44 1 s =
      .value (load33_product1Env E v, s) := by
  have hf0 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv0 : (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) =
      Ty.wrap (v 4) := packed_unflatten s.mem r v hv 4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  simp [runSlice, avx2Kernel.bb33, load33_product1Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0]

theorem load33_product1_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%378) = .value (r.add 128#64)) :
    (avx2Kernel.bb33 p).runBodyFrom E 44 s =
      (avx2Kernel.bb33 p).runBodyFrom (load33_product1Env E v) 45 s := by
  exact runBodyFrom_slice _ E (load33_product1Env E v) 44 1 s s
    (load33_product1_slice p E s r v hr hv hp0)

theorem load33_product1_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load33_product1Env E v).read (%849) = Ty.wrap (v 4) := by
  simp [load33_product1Env, mlir_env]

theorem load33_product1_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load33_product1Env E v) := by
  constructor <;> simp [load33_product1Env, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]

/-- Packed reads in their original order. The fifth first-product load
is a separate interval because the imported CFG interleaves four shuffles. -/
def load33_resultEnv (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%881 := Ty.wrap (v 0), %882 := Ty.wrap (v 1), %883 := Ty.wrap (v 2), %884 := Ty.wrap (v 3), %885 := Ty.wrap (v 4)]

theorem load33_result_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%260) = .value r)
    (hp1 : E.read (%387) = .value (r.add 32#64))
    (hp2 : E.read (%388) = .value (r.add 64#64))
    (hp3 : E.read (%389) = .value (r.add 96#64))
    (hp4 : E.read (%390) = .value (r.add 128#64)) :
    runSlice (avx2Kernel.bb33 p) E 92 5 s =
      .value (load33_resultEnv E v, s) := by
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
  simp [runSlice, avx2Kernel.bb33, load33_resultEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env, throwUBIf,
    hp0, hf0, hv0, hp1, hf1, hv1, hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4]

theorem load33_result_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%260) = .value r)
    (hp1 : E.read (%387) = .value (r.add 32#64))
    (hp2 : E.read (%388) = .value (r.add 64#64))
    (hp3 : E.read (%389) = .value (r.add 96#64))
    (hp4 : E.read (%390) = .value (r.add 128#64)) :
    (avx2Kernel.bb33 p).runBodyFrom E 92 s =
      (avx2Kernel.bb33 p).runBodyFrom (load33_resultEnv E v) 97 s := by
  exact runBodyFrom_slice _ E (load33_resultEnv E v) 92 5 s s
    (load33_result_slice p E s r v hr hv hp0 hp1 hp2 hp3 hp4)

theorem load33_result_reads (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) :
    (load33_resultEnv E v).read (%881) = Ty.wrap (v 0) ∧
    (load33_resultEnv E v).read (%882) = Ty.wrap (v 1) ∧
    (load33_resultEnv E v).read (%883) = Ty.wrap (v 2) ∧
    (load33_resultEnv E v).read (%884) = Ty.wrap (v 3) ∧
    (load33_resultEnv E v).read (%885) = Ty.wrap (v 4) := by
  simp [load33_resultEnv, mlir_env]

theorem load33_result_constants (E : ⟪avx2Kernel.Γ⟫) (v : PointBlocks) (h : Constants E) :
    Constants (load33_resultEnv E v) := by
  constructor <;> simp [load33_resultEnv, mlir_env, h.poison, h.prepare0, h.prepareN,
    h.difference0, h.differenceN, h.negate0, h.negateN]


end Agave.Ed25519.Avx2PointAdd.CFG
