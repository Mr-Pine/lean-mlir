import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.InitializerProgram
import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.XgetbvProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekCacheMemory
import SSA.Projects.RIR.Run.Tactic

/-!
The hardware boundary is instruction-local: CPUID and XGETBV return arbitrary
defined query results without changing sequential memory, and the monotonic
store writes exactly its byte. The imported CFG proves all remaining execution.
No CPUID feature-accuracy or concurrent atomic-event claim is made here.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
open LeanMLIR.RIR

abbrev CpuidTy : Ty := .struct [.bv 32, .bv 32, .bv 32, .bv 32]

/-- The assembly result order is EBX, EAX, ECX, EDX. -/
structure CpuidResult where
  ebx : BitVec 32
  eax : BitVec 32
  ecx : BitVec 32
  edx : BitVec 32

def CpuidResult.value (q : CpuidResult) : ⟦CpuidTy⟧ :=
  (.value q.ebx, .value q.eax, .value q.ecx, .value q.edx)

def cpuidArgs (leaf subleaf : BitVec 32) : Vals [.bv 32, .bv 32] :=
  .cons (.value leaf) (.cons (.value subleaf) .nil)

def storeArgs (byte : BitVec 8) (cache : Pointer) : Vals [.bv 8, .ptr] :=
  .cons (.value byte) (.cons (.value cache) .nil)

/-- The XGETBV wrapper has no residual whole-function execution assumption. -/
theorem xgetbv_call
    (instruction : Vals [.bv 32] → EffectM (Vals [.bv 64]))
    (state : GlobalState) (result : BitVec 64) (hwf : state.WF)
    (hinstruction : instruction (.cons (.value 0) .nil) state =
      .value (.cons (.value result) .nil, state)) :
    (xgetbv instruction).call .nil state =
      .value (.cons (.value result) .nil, state) := by
  simp only [BitVec.ofNat_eq_ofNat] at hinstruction
  rw [Func.call_eq_run_bind, Func.run_runFrom_eq, Func.runFrom_eq]
  simp [xgetbv, xgetbv.entry, BasicBlock.run,
    List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
    EffectM.pure_eq, mlir_effect, mlir_env, hinstruction, Exit.run,
    Env.writeMany_cons, Env.writeMany_nil, Func.continue, hwf.eraseFrom]

def osGate (q : CpuidResult) : Bool := decide (q.ecx &&& 201326592 = 201326592)

def selected (q1 q7 : CpuidResult) (xcr0 : BitVec 64) : Bool :=
  decide (q1.ecx &&& 268435456 ≠ 0) &&
    (decide (q7.ebx &&& 32 ≠ 0) &&
      (if osGate q1 then decide (xcr0 &&& 6 = 6) else false))

@[simp] theorem block_0 (p : Primitives) (cache : Pointer) :
    (initializer p cache).blocks 0 = initializer.bb0 p cache := rfl
@[simp] theorem block_1 (p : Primitives) (cache : Pointer) :
    (initializer p cache).blocks 1 = initializer.bb1 p := rfl
@[simp] theorem block_2 (p : Primitives) (cache : Pointer) :
    (initializer p cache).blocks 2 = initializer.bb2 p := rfl
@[simp] theorem params_1 : initializer.blockParams 1 = .cons (%15) .nil := rfl
@[simp] theorem params_2 : initializer.blockParams 2 = .nil := rfl

/-- Exact body execution from only per-instruction equations. The third CPUID
result is intentionally arbitrary and still must be executed successfully. -/
theorem initializer_run (p : Primitives) (cache : Pointer) (state : GlobalState)
    (q1 q7 q71 : CpuidResult) (xcr0 : BitVec 64)
    (h1 : p.cpuid (cpuidArgs 1 0) state = .value (.cons q1.value .nil, state))
    (h7 : p.cpuid (cpuidArgs 7 0) state = .value (.cons q7.value .nil, state))
    (h71 : p.cpuid (cpuidArgs 7 1) state = .value (.cons q71.value .nil, state))
    (hx : osGate q1 = true →
      p.xgetbv .nil state = .value (.cons (.value xcr0) .nil, state))
    (hstore : ∀ enabled : Bool,
      p.storeMonotonic (storeArgs (choiceByte enabled) cache) state =
        .value (.nil, stored state cache enabled)) :
    (initializer p cache).run .nil state =
      .value (.cons (.value (BitVec.ofBool (selected q1 q7 xcr0))) .nil,
        stored state cache (selected q1 q7 xcr0)) := by
  simp [cpuidArgs, CpuidResult.value] at h1 h7 h71
  have hstore0 := hstore false
  have hstore1 := hstore true
  simp [storeArgs, choiceByte] at hstore0 hstore1
  by_cases hg : osGate q1 = true
  · have hx' := hx hg
    simp only [osGate, decide_eq_true_eq, BitVec.ofNat_eq_ofNat] at hg
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    simp [initializer.bb0, BasicBlock.run,
      List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
      EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
      Exit.run, Jump.run, h1, h7, h71, Env.writeMany_cons, Env.writeMany_nil,
      AggregatePath.get, FieldIndex.get, Func.continue, ofBool_eq_one_iff, beq_iff_eq, hg]
    rw [Func.runFrom_eq]
    change ((initializer.bb2 p).run initializer.blockParams _ state >>= _) = _
    simp [initializer.bb2, BasicBlock.run,
      List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
      EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
      Exit.run, Jump.run, hx', Env.writeMany_cons, Env.writeMany_nil,
      AggregatePath.get, FieldIndex.get, Func.continue]
    rw [Func.runFrom_eq]
    change ((initializer.bb1 p).run initializer.blockParams _ state >>= _) = _
    by_cases hs : q1.ecx &&& 268435456#32 = 0#32 <;>
      by_cases hb : q7.ebx &&& 32#32 = 0#32 <;>
      by_cases hxcr : xcr0 &&& 6#64 = 6#64 <;>
      simp [initializer.bb1, BasicBlock.run,
        List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
        EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
        Exit.run, Jump.run, Env.writeMany_cons, Env.writeMany_nil,
        AggregatePath.get, FieldIndex.get, Func.continue, hstore0, hstore1,
        selected, osGate, hg, hs, hb, hxcr, Ty.wrap, bne, Bool.beq_eq_decide_eq]
  · simp only [osGate, decide_eq_true_eq, BitVec.ofNat_eq_ofNat] at hg
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    simp [initializer.bb0, BasicBlock.run,
      List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
      EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
      Exit.run, Jump.run, h1, h7, h71, Env.writeMany_cons, Env.writeMany_nil,
      AggregatePath.get, FieldIndex.get, Func.continue, ofBool_eq_one_iff, beq_iff_eq, hg]
    rw [Func.runFrom_eq]
    change ((initializer.bb1 p).run initializer.blockParams _ state >>= _) = _
    by_cases hs : q1.ecx &&& 268435456#32 = 0#32 <;>
      by_cases hb : q7.ebx &&& 32#32 = 0#32 <;>
      simp [initializer.bb1, BasicBlock.run,
        List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
        EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
        Exit.run, Jump.run, Env.writeMany_cons, Env.writeMany_nil,
        AggregatePath.get, FieldIndex.get, Func.continue, hstore0, hstore1,
        selected, osGate, hg, hs, hb, Ty.wrap, bne, Bool.beq_eq_decide_eq]

end Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
