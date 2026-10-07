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

def row22Env (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    ⟪avx2Kernel.Γ⟫ := E[%529 := .value (tableRow table index)]

theorem row22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%264) = .value table)
    (hpi : E.read (%527) = .value (BitVec.ofNat 64 index.val)) :
    runSlice (avx2Kernel.bb22 p) E 0 1 s = .value (row22Env E table index, s) := by
  have hscale := tableIndex_scale index
  have hgep := ht.gep (k := 160 * index.val) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  simp [runSlice, avx2Kernel.bb22, row22Env, tableRow,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, hpt, hpi, hscale, hgep]

theorem row22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%264) = .value table)
    (hpi : E.read (%527) = .value (BitVec.ofNat 64 index.val)) :
    (avx2Kernel.bb22 p).runBodyFrom E 0 s =
      (avx2Kernel.bb22 p).runBodyFrom (row22Env E table index) 1 s := by
  exact runBodyFrom_slice _ E _ 0 1 s s
    (row22_slice p E s table index bytes ht hi hpt hpi)

/-- Five cached vectors and the four intervening inbounds byte GEPs. -/
def cached22Env (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%530 := Ty.wrap (v 0), %531 := .value (r.add 32#64), %532 := Ty.wrap (v 1), %533 := .value (r.add 64#64), %534 := Ty.wrap (v 2), %535 := .value (r.add 96#64), %536 := Ty.wrap (v 3), %537 := .value (r.add 128#64), %538 := Ty.wrap (v 4)]

theorem cached22_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hpr : E.read (%529) = .value r)
    (hc1 : E.read (%3) = .value 32#64)
    (hc2 : E.read (%20) = .value 64#64)
    (hc3 : E.read (%21) = .value 96#64)
    (hc4 : E.read (%22) = .value 128#64) :
    runSlice (avx2Kernel.bb22 p) E 1 9 s = .value (cached22Env E r v, s) := by
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
  have hg1 : Operation.gepInboundsLive s.mem (.value r) [.value (32 : Int)] =
      .value (r.add 32#64) := hr.gep (k := 32) (by decide)
  have hs1 : Operation.gepInboundsIndex 1 (.value 32#64) =
      .value (32 : Int) := by decide
  have hg2 : Operation.gepInboundsLive s.mem (.value r) [.value (64 : Int)] =
      .value (r.add 64#64) := hr.gep (k := 64) (by decide)
  have hs2 : Operation.gepInboundsIndex 1 (.value 64#64) =
      .value (64 : Int) := by decide
  have hg3 : Operation.gepInboundsLive s.mem (.value r) [.value (96 : Int)] =
      .value (r.add 96#64) := hr.gep (k := 96) (by decide)
  have hs3 : Operation.gepInboundsIndex 1 (.value 96#64) =
      .value (96 : Int) := by decide
  have hg4 : Operation.gepInboundsLive s.mem (.value r) [.value (128 : Int)] =
      .value (r.add 128#64) := hr.gep (k := 128) (by decide)
  have hs4 : Operation.gepInboundsIndex 1 (.value 128#64) =
      .value (128 : Int) := by decide
  simp [runSlice, avx2Kernel.bb22, cached22Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    Operation.load, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf, hpr, hf0, hv0, hf1, hv1, hf2, hv2, hf3, hv3, hf4, hv4, hc1, hg1, hs1, hc2, hg2, hs2, hc3, hg3, hs3, hc4, hg4, hs4]

theorem cached22_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hpr : E.read (%529) = .value r)
    (hc1 : E.read (%3) = .value 32#64)
    (hc2 : E.read (%20) = .value 64#64)
    (hc3 : E.read (%21) = .value 96#64)
    (hc4 : E.read (%22) = .value 128#64) :
    (avx2Kernel.bb22 p).runBodyFrom E 1 s =
      (avx2Kernel.bb22 p).runBodyFrom (cached22Env E r v) 10 s := by
  exact runBodyFrom_slice _ E _ 1 9 s s
    (cached22_slice p E s r v hr hv hpr hc1 hc2 hc3 hc4)

def row25Env (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    ⟪avx2Kernel.Γ⟫ := E[%627 := .value (tableRow table index)]

theorem row25_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%264) = .value table)
    (hpi : E.read (%625) = .value (BitVec.ofNat 64 index.val)) :
    runSlice (avx2Kernel.bb25 p) E 0 1 s = .value (row25Env E table index, s) := by
  have hscale := tableIndex_scale index
  have hgep := ht.gep (k := 160 * index.val) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  simp [runSlice, avx2Kernel.bb25, row25Env, tableRow,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, hpt, hpi, hscale, hgep]

theorem row25_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%264) = .value table)
    (hpi : E.read (%625) = .value (BitVec.ofNat 64 index.val)) :
    (avx2Kernel.bb25 p).runBodyFrom E 0 s =
      (avx2Kernel.bb25 p).runBodyFrom (row25Env E table index) 1 s := by
  exact runBodyFrom_slice _ E _ 0 1 s s
    (row25_slice p E s table index bytes ht hi hpt hpi)

def row29Env (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    ⟪avx2Kernel.Γ⟫ := E[%710 := .value (tableRow table index)]

theorem row29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%224) = .value table)
    (hpi : E.read (%708) = .value (BitVec.ofNat 64 index.val)) :
    runSlice (avx2Kernel.bb29 p) E 0 1 s = .value (row29Env E table index, s) := by
  have hscale := tableIndex_scale index
  have hgep := ht.gep (k := 160 * index.val) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  simp [runSlice, avx2Kernel.bb29, row29Env, tableRow,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, hpt, hpi, hscale, hgep]

theorem row29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%224) = .value table)
    (hpi : E.read (%708) = .value (BitVec.ofNat 64 index.val)) :
    (avx2Kernel.bb29 p).runBodyFrom E 0 s =
      (avx2Kernel.bb29 p).runBodyFrom (row29Env E table index) 1 s := by
  exact runBodyFrom_slice _ E _ 0 1 s s
    (row29_slice p E s table index bytes ht hi hpt hpi)

/-- Five cached vectors and the four intervening inbounds byte GEPs. -/
def cached29Env (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) (v : PointBlocks) : ⟪avx2Kernel.Γ⟫ :=
  E[%711 := Ty.wrap (v 0), %712 := .value (r.add 32#64), %713 := Ty.wrap (v 1), %714 := .value (r.add 64#64), %715 := Ty.wrap (v 2), %716 := .value (r.add 96#64), %717 := Ty.wrap (v 3), %718 := .value (r.add 128#64), %719 := Ty.wrap (v 4)]

theorem cached29_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hpr : E.read (%710) = .value r)
    (hc1 : E.read (%3) = .value 32#64)
    (hc2 : E.read (%20) = .value 64#64)
    (hc3 : E.read (%21) = .value 96#64)
    (hc4 : E.read (%22) = .value 128#64) :
    runSlice (avx2Kernel.bb29 p) E 1 9 s = .value (cached29Env E r v, s) := by
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
  have hg1 : Operation.gepInboundsLive s.mem (.value r) [.value (32 : Int)] =
      .value (r.add 32#64) := hr.gep (k := 32) (by decide)
  have hs1 : Operation.gepInboundsIndex 1 (.value 32#64) =
      .value (32 : Int) := by decide
  have hg2 : Operation.gepInboundsLive s.mem (.value r) [.value (64 : Int)] =
      .value (r.add 64#64) := hr.gep (k := 64) (by decide)
  have hs2 : Operation.gepInboundsIndex 1 (.value 64#64) =
      .value (64 : Int) := by decide
  have hg3 : Operation.gepInboundsLive s.mem (.value r) [.value (96 : Int)] =
      .value (r.add 96#64) := hr.gep (k := 96) (by decide)
  have hs3 : Operation.gepInboundsIndex 1 (.value 96#64) =
      .value (96 : Int) := by decide
  have hg4 : Operation.gepInboundsLive s.mem (.value r) [.value (128 : Int)] =
      .value (r.add 128#64) := hr.gep (k := 128) (by decide)
  have hs4 : Operation.gepInboundsIndex 1 (.value 128#64) =
      .value (128 : Int) := by decide
  simp [runSlice, avx2Kernel.bb29, cached29Env,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    Operation.load, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf, hpr, hf0, hv0, hf1, hv1, hf2, hv2, hf3, hv3, hf4, hv4, hc1, hg1, hs1, hc2, hg2, hs2, hc3, hg3, hs3, hc4, hg4, hs4]

theorem cached29_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : PointBlocks)
    (hr : Reduce64.Execution.SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hpr : E.read (%710) = .value r)
    (hc1 : E.read (%3) = .value 32#64)
    (hc2 : E.read (%20) = .value 64#64)
    (hc3 : E.read (%21) = .value 96#64)
    (hc4 : E.read (%22) = .value 128#64) :
    (avx2Kernel.bb29 p).runBodyFrom E 1 s =
      (avx2Kernel.bb29 p).runBodyFrom (cached29Env E r v) 10 s := by
  exact runBodyFrom_slice _ E _ 1 9 s s
    (cached29_slice p E s r v hr hv hpr hc1 hc2 hc3 hc4)

def row33Env (E : ⟪avx2Kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    ⟪avx2Kernel.Γ⟫ := E[%815 := .value (tableRow table index)]

theorem row33_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%224) = .value table)
    (hpi : E.read (%813) = .value (BitVec.ofNat 64 index.val)) :
    runSlice (avx2Kernel.bb33 p) E 0 1 s = .value (row33Env E table index, s) := by
  have hscale := tableIndex_scale index
  have hgep := ht.gep (k := 160 * index.val) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  simp [runSlice, avx2Kernel.bb33, row33Env, tableRow,
    List.foldlM_cons, List.foldlM_nil, Instr.run, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, hpt, hpi, hscale, hgep]

theorem row33_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%224) = .value table)
    (hpi : E.read (%813) = .value (BitVec.ofNat 64 index.val)) :
    (avx2Kernel.bb33 p).runBodyFrom E 0 s =
      (avx2Kernel.bb33 p).runBodyFrom (row33Env E table index) 1 s := by
  exact runBodyFrom_slice _ E _ 0 1 s s
    (row33_slice p E s table index bytes ht hi hpt hpi)


end Agave.Ed25519.Avx2PointAdd.CFG
