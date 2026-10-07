import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSqrtPrefixBridge

/-! Exact caller allocation records for the linked decoder. The completed
semantic prefix suffices to expose the actual public stores on either branch;
no allocation-preservation property is inferred from a range-only frame. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge
open LeanMLIR.RIR
open Verifier.Execution.Dalek (args2)
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
attribute [local irreducible] wordStep1 step1 Valid.decode

/-- The real linked call leaves exactly the public rejection or success stores. -/
theorem call_memory_of_prefix (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hprefix : Semantic.PrefixBoundary dg sg out input entry bytes)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after)) :
    after.mem = (rejectionState entry out).mem ∨
      ∃ payload : BitVec 1280, after.mem = (successState entry out payload).mem := by
  change (program (decodePrimitives sg) dg).call (args2 out input) entry = .value (.nil,after) at hcall
  obtain ⟨E,s,flag,hentry,hdecision,hflag,hbranch⟩ := hprefix
  by_cases hz : flag = 0#8
  · have hpublic : Semantic.PrefixPublic entry s := by simpa only [ite_eq_left hz] using hbranch
    subst flag
    have hc := Semantic.linked_call_rejection dg sg out input entry s E hentry hdecision hpublic
    have he := congrArg (fun x => x.2.mem) (PoisonOr.value_inj.mp (hcall.symm.trans hc))
    exact Or.inl he
  · have hvalue := congrArg Prod.fst (wordStep1_value bytes)
    change (wordStep1 bytes).1 = (step1 bytes).1 at hvalue
    have hvalid : (step1 bytes).1 = true := by
      rw [← hvalue]
      have hn : ¬(wordStep1 bytes).1 = false := fun hb => hz (hflag.mpr hb)
      cases hb : (wordStep1 bytes).1 <;> simp_all
    simp only [ite_eq_right hz] at hbranch
    obtain ⟨F,t,d,hsuccess,hready,hpublic,hprivate,hwords⟩ := hbranch
    have hc := Semantic.linked_call_success dg sg out input entry s t E F flag d bytes hvalid
      hentry hdecision hz hsuccess hready hwords hpublic hprivate
    have he := congrArg (fun x => x.2.mem) (PoisonOr.value_inj.mp (hcall.symm.trans hc))
    exact Or.inr ⟨(Valid.point bytes hvalid).bytes,he⟩

theorem call_allocation_of_prefix (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hprefix : Semantic.PrefixBoundary dg sg out input entry bytes)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (id : BlockId) (hi : id ≠ out.id) : after.mem[id]? = entry.mem[id]? := by
  rcases call_memory_of_prefix dg sg out input entry after bytes hprefix hcall with h | ⟨payload,h⟩
  · rw [h]
    exact MemoryState.getElem?_storeAt_ne (q := ⟨id,0⟩) hi
  · rw [h]
    simp only [successState]
    rw [MemoryState.getElem?_storeAt_ne (q := ⟨id,0⟩) (p := out) hi,
      MemoryState.getElem?_storeAt_ne (q := ⟨id,0⟩) (p := out.add 8#64) hi]

theorem call_shape_of_prefix (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hprefix : Semantic.PrefixBoundary dg sg out input entry bytes)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (id : BlockId) : (after.mem[id]?).map MemoryBlock.length =
      (entry.mem[id]?).map MemoryBlock.length := by
  rcases call_memory_of_prefix dg sg out input entry after bytes hprefix hcall with h | ⟨payload,h⟩
  · rw [h]
    exact SerialPoint.Execution.storeAt_allocationShape _ _ _ _
  · rw [h]
    simp only [successState, SerialPoint.Execution.storeAt_allocationShape]

/-- A fresh output preserves every block older than its chosen allocation mark. -/
theorem call_callerBlocks_of_prefix (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hprefix : Semantic.PrefixBoundary dg sg out input entry bytes)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (mark : Nat) (hout : mark ≤ out.id.id) :
    ∀ id : BlockId, id.id < mark → after.mem[id]? = entry.mem[id]? := by
  intro id hi
  apply call_allocation_of_prefix dg sg out input entry after bytes hprefix hcall id
  intro he
  have := congrArg BlockId.id he
  omega

theorem call_present_of_prefix (dg : Globals) (sg : SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : BitVec 256)
    (hprefix : Semantic.PrefixBoundary dg sg out input entry bytes)
    (hcall : (linkedProgram dg sg).call (args2 out input) entry = .value (.nil,after))
    (global : ByteGlobal) (id : BlockId) (hi : id ≠ out.id) (hg : global.Present id entry.mem) :
    global.Present id after.mem :=
  (call_allocation_of_prefix dg sg out input entry after bytes hprefix hcall id hi).trans hg

end Agave.Ed25519.Encoding.Decompress.Execution.Decode.SqrtPrefixBridge
