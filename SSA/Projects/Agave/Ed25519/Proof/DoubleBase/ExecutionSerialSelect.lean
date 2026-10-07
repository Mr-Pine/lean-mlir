import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.SerialProgram
import SSA.Projects.Agave.Ed25519.Proof.Tables.Memory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts
import SSA.Projects.RIR.Run.Tactic

/-!
# Actual serial table-selection call blocks

These four equations retain the imported scaled GEP, exact helper arguments,
and original successors. Their only effect premise is the selected *single*
helper invocation, intended to be supplied by `SerialContracts.Helpers`.
The index is finite; `dynamicIndex` and `baseIndex` construct it from a NAF
scalar without a digit-bounds assumption.
-/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)
open Reduce64.Execution (SmallRange)

set_option maxRecDepth 10000

def cached_subInput (E : ⟪serialKernel.Γ⟫) (out input table : Pointer)
    (k : Fin 8) : ⟪serialKernel.Γ⟫ :=
  E[%37 := .value out, %35 := .value input, %39 := .value table,
    %137 := .value (BitVec.ofNat 64 k.val)]

theorem serial_cached_sub_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 8)
    (s final : GlobalState) (htable : Buffer s.mem table 1280)
    (hcall : p.call3 (.cons (.value out) (.cons (.value input)
      (.cons (.value (table.add (BitVec.ofNat 64 (160 * k.val)))) .nil))) s =
      .value (.nil, final)) :
    (serialKernel.bb22 p).run serialKernel.blockParams
      (cached_subInput E out input table k) s =
      .value (((cached_subInput E out input table k)[%142 := .value (table.add (BitVec.ofNat 64 (160 * k.val)))],
        .inr 26), final) := by
  have hscale := Tables.Memory.dynamic_scale k
  have hgep := htable.gep (160 * k.val) (by have := k.isLt; omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hparams : serialKernel.blockParams 26 = .nil := rfl
  simp [hparams, BasicBlock.run, serialKernel.bb22,
    cached_subInput, List.foldlM_cons, List.foldlM_nil, Instr.run,
    GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hscale, hgep, hcall,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

def cached_addInput (E : ⟪serialKernel.Γ⟫) (out input table : Pointer)
    (k : Fin 8) : ⟪serialKernel.Γ⟫ :=
  E[%37 := .value out, %36 := .value input, %39 := .value table,
    %140 := .value (BitVec.ofNat 64 k.val)]

theorem serial_cached_add_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 8)
    (s final : GlobalState) (htable : Buffer s.mem table 1280)
    (hcall : p.call5 (.cons (.value out) (.cons (.value input)
      (.cons (.value (table.add (BitVec.ofNat 64 (160 * k.val)))) .nil))) s =
      .value (.nil, final)) :
    (serialKernel.bb24 p).run serialKernel.blockParams
      (cached_addInput E out input table k) s =
      .value (((cached_addInput E out input table k)[%143 := .value (table.add (BitVec.ofNat 64 (160 * k.val)))],
        .inr 26), final) := by
  have hscale := Tables.Memory.dynamic_scale k
  have hgep := htable.gep (160 * k.val) (by have := k.isLt; omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hparams : serialKernel.blockParams 26 = .nil := rfl
  simp [hparams, BasicBlock.run, serialKernel.bb24,
    cached_addInput, List.foldlM_cons, List.foldlM_nil, Instr.run,
    GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hscale, hgep, hcall,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

def affine_subInput (E : ⟪serialKernel.Γ⟫) (out input table : Pointer)
    (k : Fin 64) : ⟪serialKernel.Γ⟫ :=
  E[%37 := .value out, %33 := .value input, %29 := .value table,
    %149 := .value (BitVec.ofNat 64 k.val)]

theorem serial_affine_sub_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 64)
    (s final : GlobalState) (htable : Buffer s.mem table 7680)
    (hcall : p.call6 (.cons (.value out) (.cons (.value input)
      (.cons (.value (table.add (BitVec.ofNat 64 (120 * k.val)))) .nil))) s =
      .value (.nil, final)) :
    (serialKernel.bb30 p).run serialKernel.blockParams
      (affine_subInput E out input table k) s =
      .value (((affine_subInput E out input table k)[%155 := .value (table.add (BitVec.ofNat 64 (120 * k.val)))],
        .inr 28), final) := by
  have hscale := Tables.Memory.serial_base_scale k
  have hgep := htable.gep (120 * k.val) (by have := k.isLt; omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hparams : serialKernel.blockParams 28 = .nil := rfl
  simp [hparams, BasicBlock.run, serialKernel.bb30,
    affine_subInput, List.foldlM_cons, List.foldlM_nil, Instr.run,
    GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hscale, hgep, hcall,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

def affine_addInput (E : ⟪serialKernel.Γ⟫) (out input table : Pointer)
    (k : Fin 64) : ⟪serialKernel.Γ⟫ :=
  E[%37 := .value out, %34 := .value input, %29 := .value table,
    %153 := .value (BitVec.ofNat 64 k.val)]

theorem serial_affine_add_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 64)
    (s final : GlobalState) (htable : Buffer s.mem table 7680)
    (hcall : p.call7 (.cons (.value out) (.cons (.value input)
      (.cons (.value (table.add (BitVec.ofNat 64 (120 * k.val)))) .nil))) s =
      .value (.nil, final)) :
    (serialKernel.bb32 p).run serialKernel.blockParams
      (affine_addInput E out input table k) s =
      .value (((affine_addInput E out input table k)[%156 := .value (table.add (BitVec.ofNat 64 (120 * k.val)))],
        .inr 28), final) := by
  have hscale := Tables.Memory.serial_base_scale k
  have hgep := htable.gep (120 * k.val) (by have := k.isLt; omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hparams : serialKernel.blockParams 28 = .nil := rfl
  simp [hparams, BasicBlock.run, serialKernel.bb32,
    affine_addInput, List.foldlM_cons, List.foldlM_nil, Instr.run,
    GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hscale, hgep, hcall,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

/-- The imported selection block implements the stated field operation when its
single named helper satisfies the natural-limb contract. -/
theorem serial_cached_sub_refines (p : SerialCFG.Primitives)
    (hhelper : SerialContracts.BinaryPointContract p.call3 160
      SerialContracts.readCached SerialPoint.cachedSubCompleted)
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 8)
    (s : GlobalState) (hwf : s.WF) (htable : Buffer s.mem table 1280)
    (hout : SmallRange s.mem out 160) (hinput : SmallRange s.mem input 160)
    (hdisjointInput : SerialContracts.Disjoint out 160 input 160)
    (hdisjointRecord : SerialContracts.Disjoint out 160
      (table.add (BitVec.ofNat 64 (160 * k.val))) 160)
    (hP : SerialPoint.PointTight (SerialContracts.readPoint s input))
    (hC : SerialPoint.PointBounded (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * k.val))))) :
    ∃ final,
      (serialKernel.bb22 p).run serialKernel.blockParams
        (cached_subInput E out input table k) s =
        .value (((cached_subInput E out input table k)[%142 :=
          .value (table.add (BitVec.ofNat 64 (160 * k.val)))], .inr 26), final) ∧
      SerialContracts.WritesOnly out 160 s final ∧
      SerialPoint.pointValue (SerialPoint.asExtended (SerialContracts.readPoint final out)) =
        PointArithmetic.serialAddCached (SerialPoint.pointValue (SerialContracts.readPoint s input)) (PointArithmetic.negateCache (SerialPoint.pointValue (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * k.val)))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final out) := by
  have hrecord : SmallRange s.mem
      (table.add (BitVec.ofNat 64 (160 * k.val))) 160 :=
    htable.slice (160 * k.val) 160 (by have := k.isLt; omega)
  obtain ⟨final, hcall, hframe, hpoint, hbounded⟩ :=
    hhelper s out input _ hwf hout hinput hrecord hdisjointInput hdisjointRecord hP hC
  refine ⟨final, serial_cached_sub_block p E out input table k s final htable hcall,
    hframe, ?_, hbounded⟩
  rw [hpoint]
  exact SerialPoint.cachedSub_value _ _ hP hC

/-- The imported selection block implements the stated field operation when its
single named helper satisfies the natural-limb contract. -/
theorem serial_cached_add_refines (p : SerialCFG.Primitives)
    (hhelper : SerialContracts.BinaryPointContract p.call5 160
      SerialContracts.readCached SerialPoint.cachedAddCompleted)
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 8)
    (s : GlobalState) (hwf : s.WF) (htable : Buffer s.mem table 1280)
    (hout : SmallRange s.mem out 160) (hinput : SmallRange s.mem input 160)
    (hdisjointInput : SerialContracts.Disjoint out 160 input 160)
    (hdisjointRecord : SerialContracts.Disjoint out 160
      (table.add (BitVec.ofNat 64 (160 * k.val))) 160)
    (hP : SerialPoint.PointTight (SerialContracts.readPoint s input))
    (hC : SerialPoint.PointBounded (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * k.val))))) :
    ∃ final,
      (serialKernel.bb24 p).run serialKernel.blockParams
        (cached_addInput E out input table k) s =
        .value (((cached_addInput E out input table k)[%143 :=
          .value (table.add (BitVec.ofNat 64 (160 * k.val)))], .inr 26), final) ∧
      SerialContracts.WritesOnly out 160 s final ∧
      SerialPoint.pointValue (SerialPoint.asExtended (SerialContracts.readPoint final out)) =
        PointArithmetic.serialAddCached (SerialPoint.pointValue (SerialContracts.readPoint s input)) (SerialPoint.pointValue (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * k.val))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final out) := by
  have hrecord : SmallRange s.mem
      (table.add (BitVec.ofNat 64 (160 * k.val))) 160 :=
    htable.slice (160 * k.val) 160 (by have := k.isLt; omega)
  obtain ⟨final, hcall, hframe, hpoint, hbounded⟩ :=
    hhelper s out input _ hwf hout hinput hrecord hdisjointInput hdisjointRecord hP hC
  refine ⟨final, serial_cached_add_block p E out input table k s final htable hcall,
    hframe, ?_, hbounded⟩
  rw [hpoint]
  exact SerialPoint.cachedAdd_value _ _ hP hC

/-- The imported selection block implements the stated field operation when its
single named helper satisfies the natural-limb contract. -/
theorem serial_affine_sub_refines (p : SerialCFG.Primitives)
    (hhelper : SerialContracts.BinaryPointContract p.call6 120
      SerialContracts.readAffineCached (fun P C => SerialPoint.affineSubCompleted P C.X C.Y C.T))
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 64)
    (s : GlobalState) (hwf : s.WF) (htable : Buffer s.mem table 7680)
    (hout : SmallRange s.mem out 160) (hinput : SmallRange s.mem input 160)
    (hdisjointInput : SerialContracts.Disjoint out 160 input 160)
    (hdisjointRecord : SerialContracts.Disjoint out 160
      (table.add (BitVec.ofNat 64 (120 * k.val))) 120)
    (hP : SerialPoint.PointTight (SerialContracts.readPoint s input))
    (hC : SerialPoint.PointBounded (SerialContracts.readAffineCached s (table.add (BitVec.ofNat 64 (120 * k.val))))) :
    ∃ final,
      (serialKernel.bb30 p).run serialKernel.blockParams
        (affine_subInput E out input table k) s =
        .value (((affine_subInput E out input table k)[%155 :=
          .value (table.add (BitVec.ofNat 64 (120 * k.val)))], .inr 28), final) ∧
      SerialContracts.WritesOnly out 160 s final ∧
      SerialPoint.pointValue (SerialPoint.asExtended (SerialContracts.readPoint final out)) =
        PointArithmetic.serialAffineAddCached
          (SerialPoint.pointValue (SerialContracts.readPoint s input))
          (SerialPoint.pointValue (SerialContracts.readAffineCached s
            (table.add (BitVec.ofNat 64 (120 * k.val))))).Y
          (SerialPoint.pointValue (SerialContracts.readAffineCached s
            (table.add (BitVec.ofNat 64 (120 * k.val))))).X
          (-(SerialPoint.pointValue (SerialContracts.readAffineCached s
            (table.add (BitVec.ofNat 64 (120 * k.val))))).T) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final out) := by
  have hrecord : SmallRange s.mem
      (table.add (BitVec.ofNat 64 (120 * k.val))) 120 :=
    htable.slice (120 * k.val) 120 (by have := k.isLt; omega)
  obtain ⟨final, hcall, hframe, hpoint, hbounded⟩ :=
    hhelper s out input _ hwf hout hinput hrecord hdisjointInput hdisjointRecord hP hC
  refine ⟨final, serial_affine_sub_block p E out input table k s final htable hcall,
    hframe, ?_, hbounded⟩
  rw [hpoint]
  exact SerialPoint.affineSub_value _ _ _ _ hP hC.2.1 hC.2.2.2

/-- The imported selection block implements the stated field operation when its
single named helper satisfies the natural-limb contract. -/
theorem serial_affine_add_refines (p : SerialCFG.Primitives)
    (hhelper : SerialContracts.BinaryPointContract p.call7 120
      SerialContracts.readAffineCached (fun P C => SerialPoint.affineAddCompleted P C.X C.Y C.T))
    (E : ⟪serialKernel.Γ⟫) (out input table : Pointer) (k : Fin 64)
    (s : GlobalState) (hwf : s.WF) (htable : Buffer s.mem table 7680)
    (hout : SmallRange s.mem out 160) (hinput : SmallRange s.mem input 160)
    (hdisjointInput : SerialContracts.Disjoint out 160 input 160)
    (hdisjointRecord : SerialContracts.Disjoint out 160
      (table.add (BitVec.ofNat 64 (120 * k.val))) 120)
    (hP : SerialPoint.PointTight (SerialContracts.readPoint s input))
    (hC : SerialPoint.PointBounded (SerialContracts.readAffineCached s (table.add (BitVec.ofNat 64 (120 * k.val))))) :
    ∃ final,
      (serialKernel.bb32 p).run serialKernel.blockParams
        (affine_addInput E out input table k) s =
        .value (((affine_addInput E out input table k)[%156 :=
          .value (table.add (BitVec.ofNat 64 (120 * k.val)))], .inr 28), final) ∧
      SerialContracts.WritesOnly out 160 s final ∧
      SerialPoint.pointValue (SerialPoint.asExtended (SerialContracts.readPoint final out)) =
        PointArithmetic.serialAffineAddCached
          (SerialPoint.pointValue (SerialContracts.readPoint s input))
          (SerialPoint.pointValue (SerialContracts.readAffineCached s
            (table.add (BitVec.ofNat 64 (120 * k.val))))).X
          (SerialPoint.pointValue (SerialContracts.readAffineCached s
            (table.add (BitVec.ofNat 64 (120 * k.val))))).Y
          (SerialPoint.pointValue (SerialContracts.readAffineCached s
            (table.add (BitVec.ofNat 64 (120 * k.val))))).T ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final out) := by
  have hrecord : SmallRange s.mem
      (table.add (BitVec.ofNat 64 (120 * k.val))) 120 :=
    htable.slice (120 * k.val) 120 (by have := k.isLt; omega)
  obtain ⟨final, hcall, hframe, hpoint, hbounded⟩ :=
    hhelper s out input _ hwf hout hinput hrecord hdisjointInput hdisjointRecord hP hC
  refine ⟨final, serial_affine_add_block p E out input table k s final htable hcall,
    hframe, ?_, hbounded⟩
  rw [hpoint]
  exact SerialPoint.affineAdd_value _ _ _ _ hP hC.1 hC.2.2.2

end Agave.Ed25519.DoubleBase.RIR
