import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekPrefixAllocationShape
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialDalekContract

/-! Loaded serial globals are initial-state data. Exact allocation shape,
combined with ordinary byte frames, transports those data through actual calls. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR

/-- The successful public-key constructor and both wrapper copies preserve the
three complete serial global blocks already present in the caller state. -/
theorem serialGlobals_afterSignature
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (initial decoded : GlobalState) (i : Invocation) (x t : Key.Words) (valid : Bool)
    (hwf : initial.WF)
    (hblocks : ColdInput.CallerBlocks (Wrapper.allocated initial) decoded)
    (hserial : DoubleBase.SerialContracts.GlobalsReady g initial)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 initial) :
    DoubleBase.SerialContracts.GlobalsReady g (LinkedLeaves.afterSignature i initial decoded x t valid) ∧
    Tables.SerialConstructorContext.GlobalsReady d2 (LinkedLeaves.afterSignature i initial decoded x t valid) := by
  have hf := ColdInput.afterSignature_blocks (i := i) (x := x) (t := t) (valid := valid) hwf hblocks
  exact ⟨⟨hserial.identityOffset, hf.present hwf hserial.identity,
    hserial.baseOffset, hf.present hwf hserial.base⟩,
    ⟨hd2.offsetZero, hf.present hwf hd2.present⟩⟩

/-- An output frame with exact lengths preserves any global in another block. -/
theorem AllocationShape.outputBlock (hs : AllocationShape before after)
    (hf : OutputFrame before after out bytes) (id : BlockId) (hne : id ≠ out.id) :
    after.mem[id]? = before.mem[id]? :=
  hs.block id (fun width => hf.read ⟨id, 0⟩ width (Range.disjoint_of_id_ne hne))

/-- Read-only bytes and exact lengths together preserve complete blocks. -/
theorem AllocationShape.readOnlyBlock (hs : AllocationShape before after)
    (hf : ReadOnlyFrame before after) (id : BlockId) :
    after.mem[id]? = before.mem[id]? :=
  hs.block id (fun width => hf.read ⟨id, 0⟩ width)

theorem serialGlobals_output
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (hserial : DoubleBase.SerialContracts.GlobalsReady g before)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 before)
    (hs : AllocationShape before after) (hf : OutputFrame before after out bytes)
    (hid : g.address0.id ≠ out.id) (hbase : g.address3.id ≠ out.id) (hd : d2.address0.id ≠ out.id) :
    DoubleBase.SerialContracts.GlobalsReady g after ∧ Tables.SerialConstructorContext.GlobalsReady d2 after := by
  exact ⟨⟨hserial.identityOffset, (hs.outputBlock hf _ hid).trans hserial.identity,
    hserial.baseOffset, (hs.outputBlock hf _ hbase).trans hserial.base⟩,
    ⟨hd2.offsetZero, (hs.outputBlock hf _ hd).trans hd2.present⟩⟩

theorem serialGlobals_readOnly
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (hserial : DoubleBase.SerialContracts.GlobalsReady g before)
    (hd2 : Tables.SerialConstructorContext.GlobalsReady d2 before)
    (hs : AllocationShape before after) (hf : ReadOnlyFrame before after) :
    DoubleBase.SerialContracts.GlobalsReady g after ∧ Tables.SerialConstructorContext.GlobalsReady d2 after := by
  exact ⟨⟨hserial.identityOffset, (hs.readOnlyBlock hf _).trans hserial.identity,
    hserial.baseOffset, (hs.readOnlyBlock hf _).trans hserial.base⟩,
    ⟨hd2.offsetZero, (hs.readOnlyBlock hf _).trans hd2.present⟩⟩

end Agave.Ed25519.Verifier.Execution.Dalek
