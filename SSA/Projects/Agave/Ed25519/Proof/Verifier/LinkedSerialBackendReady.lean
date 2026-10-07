import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialColdReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeavesUnder
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputPackage

/-! Derive the serial half of backend readiness from original caller memory.
The remaining shape obligations mention only this invocation's challenge and
R decoder; AVX2 input representation remains a separate local boundary. -/
namespace Agave.Ed25519.Verifier.Execution
open LeanMLIR.RIR
open Dalek.SerialBackendReadiness
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem Dalek.ColdBackendsReady.combine {p : Dalek.Primitives}
    {sr ar : Dalek.BackendReadyPredicate} {scg : SHA512Finalization.CompressionGlobals}
    {dg : Dalek.Globals} {initial : GlobalState} {key signature message : Pointer}
    {length : Nat} {bytes : Bytes32}
    (hs : ColdBackendsReady p sr noAvx scg dg initial key signature message length bytes)
    (ha : ColdBackendsReady p noAvx ar scg dg initial key signature message length bytes) :
    ColdBackendsReady p sr ar scg dg initial key signature message length bytes := by
  intro challenged multiplied compared trace hc hm he decoded hdcall hd checked ht hp after hst hf
  have ss := hs challenged multiplied compared trace hc hm he decoded hdcall hd checked ht hp after hst hf
  have aa := ha challenged multiplied compared trace hc hm he decoded hdcall hd checked ht hp after hst hf
  exact ⟨⟨ss.1.1, aa.1.2⟩, fun next returned hcall frame =>
    ⟨(ss.2 next returned hcall frame).1, (aa.2 next returned hcall frame).2⟩⟩

theorem LinkedColdLeavesUnder.BackendInputs.combine
    (hs : BackendInputs kp dp dg scg sr noAvx decode i initial a s message)
    (ha : BackendInputs kp dp dg scg noAvx ar decode i initial a s message) :
    BackendInputs kp dp dg scg sr ar decode i initial a s message :=
  fun decoded x t hd A hA => Dalek.ColdBackendsReady.combine (hs decoded x t hd A hA) (ha decoded x t hd A hA)

/-- Shape preservation is restricted to the actual successful key continuation. -/
def LinkedColdLeavesUnder.PrefixShape
    (kp : Key.Primitives) (dp : Dalek.Primitives) (g : DoubleBase.SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (decode : Bytes32 → Option ValidPoint)
    (i : Invocation) (initial : GlobalState) (a : Bytes32) (message : List (BitVec 8)) : Prop :=
  ∀ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (decode a).isSome →
    ∀ A, decode a = some A →
    ShapeAt dp g d2 (LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message message.length

/-- Exact loader allocation sizes separate serial constants from the SHA cache. -/
theorem LinkedColdLeavesUnder.serialShaSeparate
    (hr : Ready g d2 initial) (hc : SHA512Finalization.CompressionReady scg initial) :
    g.address0.id ≠ scg.cache ∧ g.address3.id ≠ scg.cache ∧ d2.address0.id ≠ scg.cache := by
  obtain ⟨value, _, hcache⟩ := hc.cache
  have different {global : ByteGlobal} {id : BlockId}
      (hp : global.Present id initial.mem) (hn : global.length ≠ 1) : id ≠ scg.cache := by
    intro hi
    rw [hi] at hp
    have he := congrArg (fun block : Option MemoryBlock => block.map MemoryBlock.length)
      (hp.symm.trans hcache)
    exact hn (Option.some.inj he)
  exact ⟨different hr.1.identity (by decide), different hr.1.base (by decide),
    different hr.2.present (by decide)⟩

/-- Initial loaded serial globals and exact prefix shape supply serial readiness;
there is no backend-result or backend-execution hypothesis. -/
theorem LinkedColdLeavesUnder.serialBackendInputs
    (dp : Dalek.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (laws : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
    (hlink : LinkedPrefix dp hardware dg.address1)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (hdecode : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (ValidPoint.layout timesEight) (ValidPoint.shared decode))
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hcaller : ColdInput.CallerMemory i initial a r s message)
    (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
    (hframe : ∀ decoded,
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
        (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
        ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded) →
      ColdInput.CallerBlocks (Wrapper.allocated initial) decoded)
    (hserial : Ready g d2 initial)
    (hseparate : Separate g d2 dg.address1)
    (hshape : PrefixShape (LinkedColdLeaves.keyPrimitives ddg dsg) dp g d2 decode i initial a message) :
    BackendInputs (LinkedColdLeaves.keyPrimitives ddg dsg) dp dg scg
      (DoubleBase.RIR.serialLinkedReady g d2) noAvx decode i initial a s message := by
  obtain ⟨known, hk⟩ := ColdInput.decoderResult_of_contract ddg dsg decode timesEight hdecode
    initial i a hcaller.wellFormed hcaller.publicKey hglobals.decoder hframe
  intro decoded x t hd A hA
  have heq : decoded = known := Dalek.returnedState_eq_of_call hd.call hk.call
  subst known
  have hwf := ColdInput.afterSignature_wf (initial := initial) (i := i) (x := x) (t := t)
    (valid := (decode a).isSome) hk.wellFormed
  have hb := ColdInput.afterSignature_blocks (i := i) (x := x) (t := t)
    (valid := (decode a).isSome) hcaller.wellFormed hk.callerBlocks
  have hc := ColdInput.coldReady (i := i) (x := x) (t := t) (valid := (decode a).isSome)
    hglobals hcaller.wellFormed hk.wellFormed hk.callerBlocks
  have hkey := ColdInput.afterSignature_range (i := i) (x := x) (t := t) (valid := (decode a).isSome)
    (hk.callerBlocks.range (ColdInput.allocated_wf hcaller.wellFormed) (ColdInput.allocated_key initial))
    (ColdInput.key_lt initial)
  have hsig := ColdInput.afterSignature_range (i := i) (x := x) (t := t) (valid := (decode a).isSome)
    (hk.callerBlocks.range (ColdInput.allocated_wf hcaller.wellFormed) (ColdInput.allocated_signature hcaller.wellFormed))
    (ColdInput.signature_lt initial)
  exact coldReady dp hardware laws dg hlink g d2 scg _ _ _ _ _ s hwf hkey hsig
    (hb.range hcaller.wellFormed hglobals.dalekCache)
    (Dalek.serialGlobals_afterSignature g d2 initial decoded i x t _
      hcaller.wellFormed hk.callerBlocks hserial.1 hserial.2)
    hseparate (serialShaSeparate hserial hglobals.compression) (hc.stackCache hwf) hc.keyCache hc.signatureCache hc.dalekCache
    (hshape decoded x t hd A hA)

end Agave.Ed25519.Verifier.Execution
