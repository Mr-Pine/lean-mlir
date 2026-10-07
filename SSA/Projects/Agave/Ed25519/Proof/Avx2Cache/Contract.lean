import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.Execution

/-! The remaining assumptions concern three unsupported instruction kinds,
never the initializer or XGETBV wrapper as a whole. -/

namespace Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

structure HardwareInstructions where
  cpuid : Vals [.bv 32, .bv 32] → EffectM (Vals [CpuidTy])
  xgetbvIntrinsic : Vals [.bv 32] → EffectM (Vals [.bv 64])
  storeMonotonic : Vals [.bv 8, .ptr] → EffectM (Vals [])

/-- Link the actual imported XGETBV wrapper, rather than assuming its call. -/
noncomputable def HardwareInstructions.link (h : HardwareInstructions) : Primitives where
  cpuid := h.cpuid
  xgetbv := (xgetbv h.xgetbvIntrinsic).call
  storeMonotonic := h.storeMonotonic

/-- Exactly the three CPUID argument pairs used by the source body. -/
def QueriedLeaf (leaf subleaf : BitVec 32) : Prop :=
  (leaf = 1 ∧ subleaf = 0) ∨ (leaf = 7 ∧ (subleaf = 0 ∨ subleaf = 1))

/-- External instruction semantics absent from RIR. Results are arbitrary;
feature accuracy is deliberately not assumed. XGETBV legality/termination is
required only when the source's OSXSAVE/XSAVE gate permits executing it. Atomic
store semantics describe an exclusive sequential execution, not concurrency. -/
structure InstructionContracts (h : HardwareInstructions) : Prop where
  cpuid : ∀ (state : GlobalState), state.WF → ∀ leaf subleaf,
    QueriedLeaf leaf subleaf → ∃ q : CpuidResult,
      h.cpuid (cpuidArgs leaf subleaf) state = .value (.cons q.value .nil, state)
  xgetbv : ∀ (state : GlobalState), state.WF → ∀ q : CpuidResult,
    h.cpuid (cpuidArgs 1 0) state = .value (.cons q.value .nil, state) →
    osGate q = true → ∃ value : BitVec 64,
      h.xgetbvIntrinsic (.cons (.value 0) .nil) state =
        .value (.cons (.value value) .nil, state)
  storeMonotonic : ∀ (state : GlobalState), state.WF → ∀ cache,
    SmallRange state.mem cache 1 → ∀ enabled : Bool,
      h.storeMonotonic (storeArgs (choiceByte enabled) cache) state =
        .value (.nil, stored state cache enabled)

/-- The full imported call, including frame reclamation, has exactly one
caller-visible byte store and returns that byte's Boolean value. -/
theorem initializer_call_of_instructions (h : HardwareInstructions)
    (laws : InstructionContracts h) (cache : Pointer) (state : GlobalState)
    (hwf : state.WF) (hlive : SmallRange state.mem cache 1) :
    ∃ enabled : Bool,
      (initializer h.link cache).call .nil state =
        .value (.cons (.value (if enabled then 1 else 0)) .nil,
          stored state cache enabled) := by
  obtain ⟨q1, h1⟩ := laws.cpuid state hwf 1 0 (by simp [QueriedLeaf])
  obtain ⟨q7, h7⟩ := laws.cpuid state hwf 7 0 (by simp [QueriedLeaf])
  obtain ⟨q71, h71⟩ := laws.cpuid state hwf 7 1 (by simp [QueriedLeaf])
  have hx : ∃ value : BitVec 64, osGate q1 = true →
      h.link.xgetbv .nil state = .value (.cons (.value value) .nil, state) := by
    by_cases hg : osGate q1 = true
    · obtain ⟨value, hv⟩ := laws.xgetbv state hwf q1 h1 hg
      exact ⟨value, fun _ => xgetbv_call h.xgetbvIntrinsic state value hwf hv⟩
    · exact ⟨0, fun hg' => False.elim (hg hg')⟩
  obtain ⟨value, hx⟩ := hx
  let enabled := selected q1 q7 value
  have hrun := initializer_run h.link cache state q1 q7 q71 value h1 h7 h71 hx
    (laws.storeMonotonic state hwf cache hlive)
  have hcall := Func.call_of_run hrun
  have hwf' : (stored state cache enabled).WF := hwf.storeAt
  have herase : (stored state cache enabled).mem.eraseFrom state.alloc.nextFreeBlock =
      (stored state cache enabled).mem := hwf'.eraseFrom
  refine ⟨enabled, ?_⟩
  have hbit : BitVec.ofBool enabled = (if enabled then 1 else 0) := by
    cases enabled <;> rfl
  dsimp only [enabled] at herase hbit ⊢
  simpa only [herase, hbit] using hcall

/-- Replace the former whole-call `CacheStoreExecution` boundary with local
instruction obligations. This theorem also works for an already warm byte. -/
theorem cache_store_execution (h : HardwareInstructions) (laws : InstructionContracts h)
    (cache : Pointer) : CacheStoreExecution (initializer h.link cache).call cache := by
  intro state hwf hcache
  exact initializer_call_of_instructions h laws cache state hwf hcache.1

/-- Exact caller-visible contract consumed by the Dalek verifier. -/
theorem cache_contract (h : HardwareInstructions) (laws : InstructionContracts h)
    (cache : Pointer) : CacheContract (initializer h.link cache).call cache :=
  contract_of_store_execution _ cache (cache_store_execution h laws cache)

/-- In addition to the caller's frame, prove the normalized byte and exact
allocation effect. No private allocation occurs in either imported body. -/
theorem cache_call_normalized (h : HardwareInstructions) (laws : InstructionContracts h)
    (cache : Pointer) (state : GlobalState) (hwf : state.WF)
    (hlive : SmallRange state.mem cache 1) :
    ∃ (enabled : Bool) (after : GlobalState),
      (initializer h.link cache).call .nil state =
        .value (.cons (.value (if enabled then 1 else 0)) .nil, after) ∧
      OutputFrame state after cache 1 ∧
      ReadBytes after cache 1 (choiceByte enabled) ∧ after.alloc = state.alloc := by
  obtain ⟨enabled, hcall⟩ := initializer_call_of_instructions h laws cache state hwf hlive
  exact ⟨enabled, stored state cache enabled, hcall, stored_frame state cache enabled hwf,
    stored_read state cache enabled hlive, rfl⟩

end Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
