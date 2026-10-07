import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.Contract

/-! Invocation-local instruction observations for the actual imported cache CFG.
Only the two consumed CPUID fields need defined values. Unused fields, including
the complete third query result, may contain poison. Every query must still
return successfully and preserve the modeled state. The store equation concerns
only the flag computed in this invocation. These are explicit instruction
semantics premises, not a replacement implementation or an x86 semantics proof. -/

namespace Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def gate (ecx : BitVec 32) : Bool := decide (ecx &&& 201326592 = 201326592)

def flag (ecx ebx : BitVec 32) (xcr0 : BitVec 64) : Bool :=
  decide (ecx &&& 268435456 ≠ 0) &&
    (decide (ebx &&& 32 ≠ 0) &&
      (if gate ecx then decide (xcr0 &&& 6 = 6) else false))

/-- One invocation's observable instruction results. The intrinsic is required
only on the taken branch, at index zero. No relation to hardware feature names
or laws for any other state, query, store address, or stored byte is assumed. -/
def Invocation (h : HardwareInstructions) (cache : Pointer) (state : GlobalState) : Prop :=
  ∃ (q1 q7 q71 : ⟦CpuidTy⟧) (ecx ebx : BitVec 32) (xcr0 : BitVec 64),
    q1.2.2.1 = .value ecx ∧ q7.1 = .value ebx ∧
    h.cpuid (cpuidArgs 1 0) state = .value (.cons q1 .nil, state) ∧
    h.cpuid (cpuidArgs 7 0) state = .value (.cons q7 .nil, state) ∧
    h.cpuid (cpuidArgs 7 1) state = .value (.cons q71 .nil, state) ∧
    (gate ecx = true → h.xgetbvIntrinsic (.cons (.value 0) .nil) state =
      .value (.cons (.value xcr0) .nil, state)) ∧
    h.storeMonotonic (storeArgs (choiceByte (flag ecx ebx xcr0)) cache) state =
      .value (.nil, stored state cache (flag ecx ebx xcr0))

/-- Execute the unchanged initializer CFG from the local observations. In
particular, the otherwise unused third query cannot be dropped or assumed not
to trap, and no definedness assertion is made about its returned aggregate. -/
theorem initializer_run (p : Primitives) (cache : Pointer) (state : GlobalState)
    (q1 q7 q71 : ⟦CpuidTy⟧) (ecx ebx : BitVec 32) (xcr0 : BitVec 64)
    (hecx : q1.2.2.1 = .value ecx) (hebx : q7.1 = .value ebx)
    (h1 : p.cpuid (cpuidArgs 1 0) state = .value (.cons q1 .nil, state))
    (h7 : p.cpuid (cpuidArgs 7 0) state = .value (.cons q7 .nil, state))
    (h71 : p.cpuid (cpuidArgs 7 1) state = .value (.cons q71 .nil, state))
    (hx : gate ecx = true →
      p.xgetbv .nil state = .value (.cons (.value xcr0) .nil, state))
    (hstore : p.storeMonotonic (storeArgs (choiceByte (flag ecx ebx xcr0)) cache) state =
      .value (.nil, stored state cache (flag ecx ebx xcr0))) :
    (initializer p cache).run .nil state =
      .value (.cons (.value (BitVec.ofBool (flag ecx ebx xcr0))) .nil,
        stored state cache (flag ecx ebx xcr0)) := by
  simp [cpuidArgs] at h1 h7 h71
  by_cases hg : gate ecx = true
  · have hx' := hx hg
    simp only [gate, decide_eq_true_eq, BitVec.ofNat_eq_ofNat] at hg
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    simp [initializer.bb0, BasicBlock.run,
      List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
      EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
      Exit.run, Jump.run, h1, h7, h71, Env.writeMany_cons, Env.writeMany_nil,
      AggregatePath.get, FieldIndex.get, hecx, hebx, Func.continue,
      ofBool_eq_one_iff, beq_iff_eq, hg]
    rw [Func.runFrom_eq]
    change ((initializer.bb2 p).run initializer.blockParams _ state >>= _) = _
    simp [initializer.bb2, BasicBlock.run,
      List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
      EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
      Exit.run, Jump.run, hx', Env.writeMany_cons, Env.writeMany_nil,
      AggregatePath.get, FieldIndex.get, Func.continue]
    rw [Func.runFrom_eq]
    change ((initializer.bb1 p).run initializer.blockParams _ state >>= _) = _
    by_cases hs : ecx &&& 268435456#32 = 0#32 <;>
      by_cases hb : ebx &&& 32#32 = 0#32 <;>
      by_cases hxcr : xcr0 &&& 6#64 = 6#64 <;>
      simp [storeArgs, choiceByte, flag, gate, hg, hs, hb, hxcr] at hstore <;>
      simp [initializer.bb1, BasicBlock.run,
        List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
        EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
        Exit.run, Jump.run, Env.writeMany_cons, Env.writeMany_nil,
        AggregatePath.get, FieldIndex.get, hecx, hebx, Func.continue, hstore,
        flag, gate, hg, hs, hb, hxcr, Ty.wrap, bne, Bool.beq_eq_decide_eq]
  · simp only [gate, decide_eq_true_eq, BitVec.ofNat_eq_ofNat] at hg
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    simp [initializer.bb0, BasicBlock.run,
      List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
      EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
      Exit.run, Jump.run, h1, h7, h71, Env.writeMany_cons, Env.writeMany_nil,
      AggregatePath.get, FieldIndex.get, hecx, hebx, Func.continue,
      ofBool_eq_one_iff, beq_iff_eq, hg]
    rw [Func.runFrom_eq]
    change ((initializer.bb1 p).run initializer.blockParams _ state >>= _) = _
    by_cases hs : ecx &&& 268435456#32 = 0#32 <;>
      by_cases hb : ebx &&& 32#32 = 0#32 <;>
      simp [storeArgs, choiceByte, flag, gate, hg, hs, hb] at hstore <;>
      simp [initializer.bb1, BasicBlock.run,
        List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.bind_eq,
        EffectM.pure_eq, mlir_effect, mlir_env, UnOp.compute, BinOp.compute, mlir_operation,
        Exit.run, Jump.run, Env.writeMany_cons, Env.writeMany_nil,
        AggregatePath.get, FieldIndex.get, hecx, hebx, Func.continue, hstore,
        flag, gate, hg, hs, hb, Ty.wrap, bne, Bool.beq_eq_decide_eq]

/-- The original instruction laws imply the weaker local observations. -/
theorem of_instructionContracts (h : HardwareInstructions) (laws : InstructionContracts h)
    (cache : Pointer) (state : GlobalState) (hwf : state.WF)
    (hlive : SmallRange state.mem cache 1) : Invocation h cache state := by
  obtain ⟨q1, h1⟩ := laws.cpuid state hwf 1 0 (by simp [QueriedLeaf])
  obtain ⟨q7, h7⟩ := laws.cpuid state hwf 7 0 (by simp [QueriedLeaf])
  obtain ⟨q71, h71⟩ := laws.cpuid state hwf 7 1 (by simp [QueriedLeaf])
  have hx : ∃ value : BitVec 64, gate q1.ecx = true →
      h.xgetbvIntrinsic (.cons (.value 0) .nil) state =
        .value (.cons (.value value) .nil, state) := by
    by_cases hg : gate q1.ecx = true
    · obtain ⟨value, hv⟩ := laws.xgetbv state hwf q1 h1 hg
      exact ⟨value, fun _ => hv⟩
    · exact ⟨0, fun hg' => False.elim (hg hg')⟩
  obtain ⟨value, hv⟩ := hx
  exact ⟨q1.value, q7.value, q71.value, q1.ecx, q7.ebx, value,
    rfl, rfl, h1, h7, h71, hv,
    laws.storeMonotonic state hwf cache hlive (flag q1.ecx q7.ebx value)⟩

/-- Exact complete call from only this invocation's instruction observations. -/
theorem initializer_call (h : HardwareInstructions) (cache : Pointer) (state : GlobalState)
    (hwf : state.WF) (hlocal : Invocation h cache state) :
    ∃ enabled : Bool,
      (initializer h.link cache).call .nil state =
        .value (.cons (.value (if enabled then 1 else 0)) .nil,
          stored state cache enabled) := by
  obtain ⟨q1, q7, q71, ecx, ebx, xcr0, hecx, hebx, h1, h7, h71, hx, hstore⟩ := hlocal
  have hx' : gate ecx = true → h.link.xgetbv .nil state =
      .value (.cons (.value xcr0) .nil, state) :=
    fun hg => xgetbv_call h.xgetbvIntrinsic state xcr0 hwf (hx hg)
  have hrun := initializer_run h.link cache state q1 q7 q71 ecx ebx xcr0
    hecx hebx h1 h7 h71 hx' hstore
  have hcall := Func.call_of_run hrun
  have herase : (stored state cache (flag ecx ebx xcr0)).mem.eraseFrom state.alloc.nextFreeBlock =
      (stored state cache (flag ecx ebx xcr0)).mem := hwf.storeAt.eraseFrom
  refine ⟨flag ecx ebx xcr0, ?_⟩
  have hbit : BitVec.ofBool (flag ecx ebx xcr0) =
      (if flag ecx ebx xcr0 then 1 else 0) := by cases flag ecx ebx xcr0 <;> rfl
  simpa only [herase, hbit] using hcall

/-- Local return, caller frame and normalized stored byte. No instruction law
for another state, another store value, or unused CPUID fields is needed. -/
theorem initializer_call_framed (h : HardwareInstructions) (cache : Pointer)
    (state : GlobalState) (hwf : state.WF) (hlive : SmallRange state.mem cache 1)
    (hlocal : Invocation h cache state) :
    ∃ (enabled : Bool) (after : GlobalState),
      (initializer h.link cache).call .nil state =
        .value (.cons (.value (if enabled then 1 else 0)) .nil, after) ∧
      OutputFrame state after cache 1 ∧
      ReadBytes after cache 1 (choiceByte enabled) ∧ after.alloc = state.alloc := by
  obtain ⟨enabled, hcall⟩ := initializer_call h cache state hwf hlocal
  exact ⟨enabled, stored state cache enabled, hcall, stored_frame state cache enabled hwf,
    stored_read state cache enabled hlive, rfl⟩

/-- The existing universal caller interface needs local witnesses only at its
actual cold-cache inputs; it does not require universal instruction contracts. -/
theorem cache_contract (h : HardwareInstructions) (cache : Pointer)
    (hlocal : ∀ state : GlobalState, state.WF → ReadBytes state cache 1 255 →
      Invocation h cache state) : CacheContract (initializer h.link cache).call cache := by
  intro state hwf hcache
  obtain ⟨enabled, after, hcall, hframe, _, _⟩ :=
    initializer_call_framed h cache state hwf hcache.1 (hlocal state hwf hcache)
  exact ⟨after, (if enabled then 1 else 0), hcall, hframe⟩

end Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions.Local
