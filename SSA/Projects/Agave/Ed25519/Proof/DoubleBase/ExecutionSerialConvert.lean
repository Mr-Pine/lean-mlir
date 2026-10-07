import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialBlocks
import SSA.Projects.RIR.Run.Tactic

/-! The four actual completed-to-extended conversion blocks and their checked
index guards. The right side retains the four named field helper invocations;
no successful-run premise replaces any imported block. -/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR

set_option maxRecDepth 10000

private theorem emptyVals_eq (v : Vals []) : v = .nil := by cases v; rfl

/-- The exact four field-helper calls made by each completed conversion. -/
def completedCalls (mul : Vals [.ptr, .ptr, .ptr] → EffectM (Vals []))
    (out input : Pointer) : EffectM (Vals []) := do
  let _ ← mul (.cons (.value out) (.cons (.value input) (.cons (.value (input.add 120)) .nil)))
  let _ ← mul (.cons (.value (out.add 40)) (.cons (.value (input.add 40))
    (.cons (.value (input.add 80)) .nil)))
  let _ ← mul (.cons (.value (out.add 80)) (.cons (.value (input.add 80))
    (.cons (.value (input.add 120)) .nil)))
  mul (.cons (.value (out.add 120)) (.cons (.value input) (.cons (.value (input.add 40)) .nil)))

/-- The emitted arithmetic on every width-five magnitude, including zero. -/
theorem serial_index_arithmetic5 : ∀ magnitude : Fin 16,
    Operation.sub {} (.value 0#8) (.value (-BitVec.ofNat 8 magnitude.val)) =
      .value (BitVec.ofNat 8 magnitude.val) ∧
    Operation.sext (.value (BitVec.ofNat 8 magnitude.val)) =
      .value (BitVec.ofNat 64 magnitude.val) ∧
    Operation.lshr false (.value (BitVec.ofNat 64 magnitude.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (magnitude.val / 2)) ∧
    Operation.icmp .ult (.value (BitVec.ofNat 8 magnitude.val)) (.value 16#8) =
      .value 1#1 := by
  decide +kernel

/-- The width-eight sign guard is satisfied for every legal magnitude. -/
theorem serial_index_arithmetic8 : ∀ magnitude : Fin 128,
    Operation.sub {} (.value 0#8) (.value (-BitVec.ofNat 8 magnitude.val)) =
      .value (BitVec.ofNat 8 magnitude.val) ∧
    Operation.sext (.value (BitVec.ofNat 8 magnitude.val)) =
      .value (BitVec.ofNat 64 magnitude.val) ∧
    Operation.lshr false (.value (BitVec.ofNat 64 magnitude.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (magnitude.val / 2)) ∧
    Operation.icmp .sgt (.value (BitVec.ofNat 8 magnitude.val)) (.value 255#8) =
      .value 1#1 := by
  decide +kernel

def cached_subConvertInput (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 16) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8,
    %10 := .value 1#64,
    %24 := .value 16#8,
    %35 := .value out,
    %37 := .value input,
    %109 := .value (input.add 120),
    %110 := .value (input.add 40),
    %111 := .value (input.add 80),
    %115 := .value (out.add 40),
    %116 := .value (out.add 80),
    %117 := .value (out.add 120),
    %133 := .value (-BitVec.ofNat 8 magnitude.val)]

def cached_subConvertResult (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 16) : ⟪serialKernel.Γ⟫ :=
  (cached_subConvertInput E out input magnitude)[%135 := .value (BitVec.ofNat 8 magnitude.val),
    %136 := .value (BitVec.ofNat 64 magnitude.val),
    %137 := .value (BitVec.ofNat 64 (magnitude.val / 2)),
    %138 := .value (1#1)]

/-- Exact original block 20; its panic successor is excluded by the proved
finite magnitude range, while the four field invocations are retained. -/
theorem serial_cached_sub_convert_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 16)
    (s : GlobalState) :
    (serialKernel.bb20 p).run serialKernel.blockParams
      (cached_subConvertInput E out input magnitude) s =
      (do
        let _ ← completedCalls p.call2 out input
        pure (cached_subConvertResult E out input magnitude, Sum.inr 22)) s := by
  obtain ⟨hneg, hwide, hindex, hguard⟩ := serial_index_arithmetic5 magnitude
  simp [BasicBlock.run, serialKernel.bb20, cached_subConvertInput, cached_subConvertResult,
    completedCalls, List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hneg, hwide, hindex, hguard, emptyVals_eq, Exit.run, Jump.run,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

def cached_addConvertInput (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 16) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8,
    %10 := .value 1#64,
    %24 := .value 16#8,
    %36 := .value out,
    %37 := .value input,
    %109 := .value (input.add 120),
    %110 := .value (input.add 40),
    %111 := .value (input.add 80),
    %112 := .value (out.add 40),
    %113 := .value (out.add 80),
    %114 := .value (out.add 120),
    %133 := .value (BitVec.ofNat 8 magnitude.val)]

def cached_addConvertResult (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 16) : ⟪serialKernel.Γ⟫ :=
  (cached_addConvertInput E out input magnitude)[%139 := .value (BitVec.ofNat 64 magnitude.val),
    %140 := .value (BitVec.ofNat 64 (magnitude.val / 2)),
    %141 := .value (1#1)]

/-- Exact original block 21; its panic successor is excluded by the proved
finite magnitude range, while the four field invocations are retained. -/
theorem serial_cached_add_convert_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 16)
    (s : GlobalState) :
    (serialKernel.bb21 p).run serialKernel.blockParams
      (cached_addConvertInput E out input magnitude) s =
      (do
        let _ ← completedCalls p.call2 out input
        pure (cached_addConvertResult E out input magnitude, Sum.inr 24)) s := by
  obtain ⟨hneg, hwide, hindex, hguard⟩ := serial_index_arithmetic5 magnitude
  simp [BasicBlock.run, serialKernel.bb21, cached_addConvertInput, cached_addConvertResult,
    completedCalls, List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hneg, hwide, hindex, hguard, emptyVals_eq, Exit.run, Jump.run,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

def affine_subConvertInput (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 128) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8,
    %10 := .value 1#64,
    %26 := .value 255#8,
    %33 := .value out,
    %37 := .value input,
    %109 := .value (input.add 120),
    %110 := .value (input.add 40),
    %111 := .value (input.add 80),
    %121 := .value (out.add 40),
    %122 := .value (out.add 80),
    %123 := .value (out.add 120),
    %145 := .value (-BitVec.ofNat 8 magnitude.val)]

def affine_subConvertResult (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 128) : ⟪serialKernel.Γ⟫ :=
  (affine_subConvertInput E out input magnitude)[%147 := .value (BitVec.ofNat 8 magnitude.val),
    %148 := .value (BitVec.ofNat 64 magnitude.val),
    %149 := .value (BitVec.ofNat 64 (magnitude.val / 2)),
    %150 := .value (1#1)]

/-- Exact original block 27; its panic successor is excluded by the proved
finite magnitude range, while the four field invocations are retained. -/
theorem serial_affine_sub_convert_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 128)
    (s : GlobalState) :
    (serialKernel.bb27 p).run serialKernel.blockParams
      (affine_subConvertInput E out input magnitude) s =
      (do
        let _ ← completedCalls p.call2 out input
        pure (affine_subConvertResult E out input magnitude, Sum.inr 30)) s := by
  obtain ⟨hneg, hwide, hindex, hguard⟩ := serial_index_arithmetic8 magnitude
  simp [BasicBlock.run, serialKernel.bb27, affine_subConvertInput, affine_subConvertResult,
    completedCalls, List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hneg, hwide, hindex, hguard, emptyVals_eq, Exit.run, Jump.run,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

def affine_addConvertInput (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 128) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8,
    %10 := .value 1#64,
    %26 := .value 255#8,
    %34 := .value out,
    %37 := .value input,
    %109 := .value (input.add 120),
    %110 := .value (input.add 40),
    %111 := .value (input.add 80),
    %118 := .value (out.add 40),
    %119 := .value (out.add 80),
    %120 := .value (out.add 120),
    %145 := .value (BitVec.ofNat 8 magnitude.val)]

def affine_addConvertResult (E : ⟪serialKernel.Γ⟫) (out input : Pointer)
    (magnitude : Fin 128) : ⟪serialKernel.Γ⟫ :=
  (affine_addConvertInput E out input magnitude)[%152 := .value (BitVec.ofNat 64 magnitude.val),
    %153 := .value (BitVec.ofNat 64 (magnitude.val / 2)),
    %154 := .value (1#1)]

/-- Exact original block 29; its panic successor is excluded by the proved
finite magnitude range, while the four field invocations are retained. -/
theorem serial_affine_add_convert_block (p : SerialCFG.Primitives)
    (E : ⟪serialKernel.Γ⟫) (out input : Pointer) (magnitude : Fin 128)
    (s : GlobalState) :
    (serialKernel.bb29 p).run serialKernel.blockParams
      (affine_addConvertInput E out input magnitude) s =
      (do
        let _ ← completedCalls p.call2 out input
        pure (affine_addConvertResult E out input magnitude, Sum.inr 32)) s := by
  obtain ⟨hneg, hwide, hindex, hguard⟩ := serial_index_arithmetic8 magnitude
  simp [BasicBlock.run, serialKernel.bb29, affine_addConvertInput, affine_addConvertResult,
    completedCalls, List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hneg, hwide, hindex, hguard, emptyVals_eq, Exit.run, Jump.run,
    Regs.read_cons, Regs.read_nil, Env.writeMany_nil]

end Agave.Ed25519.DoubleBase.RIR
