import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialColdReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeaves
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdLinked
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSemantic

/-! Allocation shape for the two exact calls named by SerialBackendReadiness.ShapeAt.
The challenge field follows from the proved cold challenge effect. Decoder shape
follows from its existing finite-prefix boundary and actual returned state; this
module does not assert that initialized globals alone establish that boundary.
-/
namespace Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- A cache-aware challenge effect preserves allocation length at every block
other than the concrete SHA cache, including either backend's immutable table. -/
theorem allocationShape_at_of_cacheOutputEffect
    (scg : SHA512Finalization.CompressionGlobals) (before after : GlobalState)
    (out : Pointer) (value : BitVec w)
    (h : SHA512Finalization.CacheOutputEffect scg before after out value)
    (id : BlockId) (hi : id ≠ scg.cache) :
    (after.mem[id]?).map MemoryBlock.length = (before.mem[id]?).map MemoryBlock.length := by
  rw [h.memory.blocks id hi]
  exact SerialPoint.Execution.storeAt_allocationShape before.mem out value id

/-- The cold challenge effect retains whole blocks away from the SHA cache.
Unlike a byte-only output frame, it therefore preserves allocation lengths. -/
theorem globalShape_of_cacheOutputEffect
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (scg : SHA512Finalization.CompressionGlobals) (before after : GlobalState)
    (out : Pointer) (value : BitVec w)
    (h : SHA512Finalization.CacheOutputEffect scg before after out value)
    (hsep : g.address0.id ≠ scg.cache ∧ g.address3.id ≠ scg.cache ∧ d2.address0.id ≠ scg.cache) :
    GlobalShape g d2 before after := by
  exact ⟨allocationShape_at_of_cacheOutputEffect scg before after out value h _ hsep.1,
    allocationShape_at_of_cacheOutputEffect scg before after out value h _ hsep.2.1,
    allocationShape_at_of_cacheOutputEffect scg before after out value h _ hsep.2.2⟩

section Decoder
open Encoding.Decompress.Execution
open Encoding.Decompress.Execution.Decode
open Encoding.Decompress.Execution.Decode.Semantic

/-- Actual decoder return preserves allocation presence and length once its
finite source-prefix boundary is supplied. No assumption about the complete
decoder output, its allocation shape, or its final memory is used. -/
theorem decoder_allocationShape_of_prefix
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (out input : Pointer) (entry after : GlobalState) (bytes : Bytes32)
    (hprefix : Encoding.Decompress.Execution.Decode.Semantic.PrefixBoundary
      ddg dsg out input entry bytes)
    (hcall : (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (args2 out input) entry = .value (.nil, after)) :
    AllocationShape entry after := by
  obtain ⟨E, s, flag, hentry, hdecision, hflag, hbranch⟩ := hprefix
  change (Encoding.Decompress.Execution.Decode.program (decodePrimitives dsg) ddg).call (args2 out input) entry =
    .value (.nil, after) at hcall
  by_cases hz : flag = 0#8
  · have hpublic : PrefixPublic entry s := by simpa only [ite_eq_left hz] using hbranch
    subst flag
    have heq := returnedState_eq_of_call hcall
      (linked_call_rejection ddg dsg out input entry s E hentry hdecision hpublic)
    subst after
    intro id
    simp only [rejectionState, SerialPoint.Execution.storeAt_allocationShape]
  · have hvalue := congrArg Prod.fst (Encoding.Decompress.Execution.Decode.wordStep1_value bytes)
    change (Encoding.Decompress.Execution.Decode.wordStep1 bytes).1 = (Encoding.Decompress.step1 bytes).1 at hvalue
    have hvalid : (Encoding.Decompress.step1 bytes).1 = true := by
      rw [← hvalue]
      have hnot : ¬(Encoding.Decompress.Execution.Decode.wordStep1 bytes).1 = false := fun h => hz (hflag.mpr h)
      cases hb : (Encoding.Decompress.Execution.Decode.wordStep1 bytes).1 <;> simp_all
    simp only [ite_eq_right hz] at hbranch
    obtain ⟨F, t, d, hsuccess, hready, hpublic, hprivate, hwords⟩ := hbranch
    have heq := returnedState_eq_of_call hcall
      (linked_call_success ddg dsg out input entry s t E F flag d bytes hvalid
        hentry hdecision hz hsuccess hready hwords hpublic hprivate)
    subst after
    intro id
    simp only [successState, SerialPoint.Execution.storeAt_allocationShape]

end Decoder

/-- The exact linked challenge at Dalek block zero supplies its ShapeAt field.
Every range, byte, and initialized-global fact comes from this invocation's
existing entry packages; scalar-wide execution is supplied by its proved call. -/
theorem challenge_allocationShape_at
    (p : Primitives) (dg : Globals)
    (id : BlockId)
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compression : Agave.Ed25519.SHA512.Compression)
    (cg : Challenge.Globals) (sg : ScalarWide.Globals)
    (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (cofactor : ValidPoint → ValidPoint)
    (hlink : p.challengeScalar =
      (Challenge.program (LinkedColdLeaves.challengePrimitives compressCall sg) cg).call)
    (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : ValidPoint) (msg : List (BitVec 8))
    (hm : EntryMemory dg cg (ValidPoint.layout cofactor) initial key signature message
      a r bytes minusA msg)
    (hready : ColdEntryReady scg sg dg ddg dsg initial key signature message)
    (hsep : id ≠ scg.cache)
    (challenged : GlobalState)
    (hcall : p.challengeScalar
      (.cons (.value (stackSlot initial 12)) (.cons (.value key)
        (.cons (.value signature) (.cons (.value message)
          (.cons (.value (BitVec.ofNat 64 msg.length)) .nil)))))
      (allocated initial) = .value (.nil, challenged)) :
    (challenged.mem[id]?).map MemoryBlock.length =
      ((allocated initial).mem[id]?).map MemoryBlock.length := by
  let cp := LinkedColdLeaves.challengePrimitives compressCall sg
  let sha := Agave.Ed25519.SHA512.model compression
  have hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg
      cp.scalarFromSha512 compression :=
    Challenge.coldLinked_finalizer_contract_proved scg sg compression compressCall hcompress
  have hmessage : ∀ (i : Nat) (hi : i < msg.length),
      (allocated initial).mem.readAt (message.add (BitVec.ofNat 64 i)) 8 = msg[i] := by
    intro i hi
    exact (stackState_read initial hm.wellFormed 13
      (smallRange_add hm.messageRange (k := i) (count := 1) (by omega)) 8).trans
      (hm.messageBytes i hi)
  obtain ⟨after, hrun, heffect, _, _⟩ :=
    challenge_call_of_sha_contracts_cold scg sg cp cg compression hcompress hscalar
      (ValidPoint.layout cofactor) (ResidualLeaves.scalarChallenge sha)
      (ResidualLeaves.scalarChallenge_encoding sha) (stackSlot initial 12)
      key signature message (allocated initial) a r msg
      (stackState_wf initial hm.wellFormed 13) (hready.challenge hm.wellFormed)
      (stackSlot_live initial hm.wellFormed 12 13 (by decide))
      (stackState_live initial hm.wellFormed 13 hm.keyRange)
      (stackState_live initial hm.wellFormed 13 hm.signatureRange)
      (stackState_live initial hm.wellFormed 13 hm.messageRange)
      ((stackState_read initial hm.wellFormed 13 hm.keyRange 256).trans hm.publicKey)
      ((stackState_read initial hm.wellFormed 13 hm.signatureRange 256).trans hm.signatureR)
      hmessage hm.lengthBound (stackState_readBytes initial hm.wellFormed 13 hm.shaIV)
      (stackSlot_disjoint_caller initial hm.wellFormed 12 hm.keyRange 256 1536)
      (stackSlot_disjoint_caller initial hm.wellFormed 12 hm.signatureRange 256 512)
      (stackSlot_disjoint_caller initial hm.wellFormed 12 hm.messageRange 256 (8 * msg.length))
  have hrun' : p.challengeScalar
      (.cons (.value (stackSlot initial 12)) (.cons (.value key)
        (.cons (.value signature) (.cons (.value message)
          (.cons (.value (BitVec.ofNat 64 msg.length)) .nil)))))
      (allocated initial) = .value (.nil, after) := by
    rw [hlink]
    exact hrun
  have heq := returnedState_eq_of_call hcall hrun'
  subst challenged
  exact allocationShape_at_of_cacheOutputEffect scg _ _ _ _ heffect id hsep

section Invocation
variable (p : Primitives) (dg : Globals)
variable (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (cofactor : ValidPoint → ValidPoint)
variable (hlink : p.challengeScalar =
  (Challenge.program (LinkedColdLeaves.challengePrimitives compressCall sg) cg).call)
variable (hdecodeLink : p.decompress = (Encoding.Decompress.Execution.linkedProgram ddg dsg).call)
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (initial : GlobalState) (key signature message : Pointer)
variable (a r bytes : Bytes32) (minusA : ValidPoint) (msg : List (BitVec 8))
variable (hm : EntryMemory dg cg (ValidPoint.layout cofactor) initial key signature message
  a r bytes minusA msg)
variable (hready : ColdEntryReady scg sg dg ddg dsg initial key signature message)
variable (hsep : g.address0.id ≠ scg.cache ∧ g.address3.id ≠ scg.cache ∧ d2.address0.id ≠ scg.cache)
variable (hprefix : ∀ challenged multiplied compared,
  ColdCallTrace p initial key signature message msg.length challenged multiplied compared →
  Encoding.Decompress.Execution.Decode.Semantic.PrefixBoundary ddg dsg
    (stackSlot initial 8) signature compared r)

include hlink hdecodeLink hcompress hm hready hsep hprefix

/-- Replace both allocation-shape assumptions with the proved challenge effect
and the exact reached decoder's finite-prefix boundary. The decoder premise is
restricted to this invocation's actual cold-prefix trace. -/
theorem shapeAt_of_decoder_prefix :
    ShapeAt p g d2 initial key signature message msg.length := by
  constructor
  · intro challenged hcall
    have hs (id : BlockId) := challenge_allocationShape_at p dg id compressCall compression cg sg scg ddg dsg
      cofactor hlink hcompress initial key signature message a r bytes minusA msg hm hready
    exact ⟨hs g.address0.id hsep.1 challenged hcall,
      hs g.address3.id hsep.2.1 challenged hcall,
      hs d2.address0.id hsep.2.2 challenged hcall⟩
  · intro challenged multiplied compared htrace decoded hcall
    rw [hdecodeLink] at hcall
    have hs := decoder_allocationShape_of_prefix ddg dsg (stackSlot initial 8) signature
      compared decoded r (hprefix challenged multiplied compared htrace) hcall
    exact ⟨hs _, hs _, hs _⟩

/-- Initial serial globals reach the actual backend without either explicit
ShapeAt field. The remaining prefix premise is finite decoder execution at the
reached R-decoding call, not readiness in arbitrary machine states. -/
theorem coldReady_of_decoder_prefix
    (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (hlinked : LinkedPrefix p hardware dg.address1)
    (hserial : Ready g d2 initial) (hsepCache : Separate g d2 dg.address1) :
    ColdBackendsReady p (DoubleBase.RIR.serialLinkedReady g d2) noAvx scg dg
      initial key signature message msg.length bytes := by
  apply coldReady p hardware laws dg hlinked g d2 scg initial key signature message
    msg.length bytes hm.wellFormed hm.keyRange hm.signatureRange hm.cache hserial
    hsepCache hsep (hready.stackCache hm.wellFormed) hready.keyCache
    hready.signatureCache hready.dalekCache
  exact shapeAt_of_decoder_prefix p dg g d2 compressCall compression cg sg scg ddg dsg
    cofactor hlink hdecodeLink hcompress initial key signature message a r bytes minusA msg
    hm hready hsep hprefix

end Invocation

end Agave.Ed25519.Verifier.Execution.Dalek.SerialBackendReadiness
