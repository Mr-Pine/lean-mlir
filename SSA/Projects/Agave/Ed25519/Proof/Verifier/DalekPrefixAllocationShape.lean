import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLinked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityCall
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Execution
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekBytePrimitives
import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.Contract

/-! Exact allocation-length preservation for the concrete verifier prefix
callees. These facts strengthen ordinary byte/range frames and permit transport
of loaded globals whose specifications include their complete block lengths. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000

/-- Returning linked helpers preserve every allocation's presence and length. -/
def AllocationShape (before after : GlobalState) : Prop :=
  ∀ id : BlockId,
    (after.mem[id]?).map MemoryBlock.length = (before.mem[id]?).map MemoryBlock.length

namespace AllocationShape

theorem refl (s : GlobalState) : AllocationShape s s := fun _ => rfl

theorem trans (h : AllocationShape a b) (k : AllocationShape b c) : AllocationShape a c :=
  fun id => (k id).trans (h id)

theorem of_mem (h : after.mem = before.mem) : AllocationShape before after := by
  intro id
  rw [h]

theorem storeAt (s : GlobalState) (p : Pointer) (v : BitVec w) :
    AllocationShape s {s with mem := s.mem.storeAt p v} :=
  SerialPoint.Execution.storeAt_allocationShape s.mem p v

/-- Shape plus the full byte read determines an entire existing global block. -/
theorem blockAt {before after : GlobalState} (id : BlockId)
    (hs : (after.mem[id]?).map MemoryBlock.length = (before.mem[id]?).map MemoryBlock.length)
    (hread : ∀ width, after.mem.readAt ⟨id, 0⟩ width = before.mem.readAt ⟨id, 0⟩ width) :
    after.mem[id]? = before.mem[id]? := by
  cases hb : before.mem[id]? with
  | none =>
      rw [hb] at hs
      cases ha : after.mem[id]? with
      | none => rfl
      | some b => simp [ha] at hs
  | some b =>
      cases ha : after.mem[id]? with
      | none => simp [ha, hb] at hs
      | some c =>
          have hl : c.length = b.length := by simpa [ha, hb] using hs
          cases b with
          | mk n bytes =>
              cases c with
              | mk m value =>
                  dsimp at hl
                  subst m
                  have hr := hread (8*n)
                  have hv : value = bytes := by
                    simpa [MemoryState.readAt, ha, hb, Pointer.offsetInBits] using hr
                  subst value
                  rfl

/-- Full shape preservation supplies the single-block observation. -/
theorem block {before after : GlobalState} (hshape : AllocationShape before after)
    (id : BlockId)
    (hread : ∀ width, after.mem.readAt ⟨id, 0⟩ width = before.mem.readAt ⟨id, 0⟩ width) :
    after.mem[id]? = before.mem[id]? := blockAt id (hshape id) hread

end AllocationShape

theorem returnedState_eq_of_call {α : Type} {a b : α} {after expected : GlobalState}
    {call : LeanMLIR.RIR.PoisonOr (α × GlobalState)}
    (h : call = .value (a, after)) (k : call = .value (b, expected)) : after = expected :=
  congrArg Prod.snd (LeanMLIR.RIR.PoisonOr.value_inj.mp (h.symm.trans k))

theorem blackBox_allocationShape (value returned : BitVec 8) (before after : GlobalState)
    (hwf : before.WF)
    (hcall : Encoding.Decompress.Execution.BlackBox.program.call (.cons (.value value) .nil) before =
      .value (.cons (.value returned) .nil, after)) : AllocationShape before after := by
  have hs := returnedState_eq_of_call hcall (Encoding.Decompress.Execution.BlackBox.program_call value before hwf)
  subst after
  exact AllocationShape.of_mem rfl

theorem bytesEq_allocationShape (left right : Pointer) (before after : GlobalState)
    (returned : BitVec 8) (hwf : before.WF)
    (hl : SmallRange before.mem left 32) (hr : SmallRange before.mem right 32)
    (hcall : (Encoding.Decompress.Execution.BytesEq.program
      Encoding.Decompress.Execution.bytesEqPrimitives).call (args2 left right) before =
      .value (.cons (.value returned) .nil, after)) : AllocationShape before after := by
  have hs := returnedState_eq_of_call hcall (Encoding.Decompress.Execution.BytesEq.program_exact
    left right before hwf hl hr)
  subst after
  exact AllocationShape.of_mem rfl

theorem pointEq_allocationShape (left right : Pointer) (before after : GlobalState)
    (returned : BitVec 8) (hwf : before.WF)
    (hl : SmallRange before.mem left 160) (hr : SmallRange before.mem right 160)
    (hcall : SmallOrder.Execution.equalityProgram.call (args2 left right) before =
      .value (.cons (.value returned) .nil, after)) : AllocationShape before after := by
  have hs := returnedState_eq_of_call hcall (SmallOrder.Execution.EqualityCall.call_exact before left right hwf hl hr)
  subst after
  exact AllocationShape.of_mem rfl

theorem scalarReduce_allocationShape (out input : Pointer) (before after : GlobalState)
    (bits : Bytes32) (hwf : before.WF) (hout : SmallRange before.mem out 32)
    (hin : ReadBytes before input 32 bits)
    (hcall : ScalarReduce32.Execution.program.call (args2 out input) before = .value (.nil, after)) :
    AllocationShape before after := by
  have hs := returnedState_eq_of_call hcall (ScalarReduce32.Execution.call out input before bits hwf hout hin)
  subst after
  intro id
  simp only [ScalarReduce32.Execution.resultState, ScalarReduce32.Execution.storeBytes,
    SerialPoint.Execution.storeAt_allocationShape]

theorem cofactor_allocationShape (out input : Pointer) (before after : GlobalState)
    (hwf : before.WF) (hout : SmallRange before.mem out 160) (hin : SmallRange before.mem input 120)
    (hcall : SmallOrder.Execution.cofactorProgram.call
      (.cons (.value out) (.cons (.value input) (.cons (.value 3#32) .nil))) before = .value (.nil, after)) :
    AllocationShape before after := by
  have hs := returnedState_eq_of_call hcall (SmallOrder.Execution.cofactor_call_three_normal out input before hwf hout hin)
  subst after
  exact SerialPoint.Execution.storePointWords_allocationShape _ _ _

theorem cache_allocationShape (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware) (cache : Pointer)
    (before after : GlobalState) (returned : BitVec 1)
    (hwf : before.WF) (hcache : SmallRange before.mem cache 1)
    (hcall : (Avx2Cache.Instructions.initializer hardware.link cache).call .nil before =
      .value (.cons (.value returned) .nil, after)) : AllocationShape before after := by
  obtain ⟨enabled, he⟩ := Avx2Cache.Instructions.initializer_call_of_instructions hardware laws cache before hwf hcache
  have hs := returnedState_eq_of_call hcall he
  subst after
  exact AllocationShape.storeAt before cache _

end Agave.Ed25519.Verifier.Execution.Dalek
