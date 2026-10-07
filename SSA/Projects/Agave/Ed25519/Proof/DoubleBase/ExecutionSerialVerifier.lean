import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialClosed
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialColdReady

/-! The closed serial backend at the actual verifier callsite. Fixed-table
readiness is transported from initial loaded globals through the real prefix;
it is not assumed in arbitrary states. -/
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open DoubleBase.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000

/-- Execute the verifier's actual serial call block and retain its complete
160-byte result contract at the common compression continuation. -/
theorem serial_block_verified (p : Primitives) (dg : Globals)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (panic : SerialPanic) (hlink : p.serialDoubleBase = (serialLinkedKernel g d2 panic).call)
    (cofactor : ValidPoint → ValidPoint) (q : TailPointers) (E : Env program.Γ)
    (state : GlobalState) (h s : Verifier.CanonicalScalar) (a : ValidPoint) (r : Bytes32)
    (hready : SerialBackendReadiness.Ready g d2 state)
    (hregs : TailRegisters q E) (hmem : TailMemory q state (ValidPoint.layout cofactor) h s a r) :
    ∃ after encoded,
      (program p dg).runFrom E 8 state = (program p dg).runFrom E 10 after ∧
      OutputFrame state after q.output 160 ∧ ReadBytes after q.output 160 encoded ∧
      ValidPoint.ResultRepresents (ValidPoint.doubleBase h a s) encoded := by
  obtain ⟨after, encoded, hcall, hf, hb, hp⟩ := serialLinked_dalek_call_closed g d2 panic
    q.output q.challenge q.point q.scalar state h s a hmem.wellFormed hmem.output
    hmem.challenge hmem.point hmem.scalar hready.2 hready.1
  rw [← hlink] at hcall
  exact ⟨after, encoded, serial_block p dg E state after q.output q.challenge q.point q.scalar
    hregs.output hregs.challenge hregs.point hregs.scalar hcall, hf, hb, hp⟩

/-- The concrete serial call and ordinary compression/comparison tail produce
the verifier's exact return code. No double-base execution premise remains. -/
theorem serial_tail_verified (p : Primitives) (dg : Globals)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (panic : SerialPanic) (hlink : p.serialDoubleBase = (serialLinkedKernel g d2 panic).call)
    (cofactor : ValidPoint → ValidPoint) (compress : Bridge.CurvePoint → Bytes32)
    (hcompress : CompressContract p.compressPoint (ValidPoint.layout cofactor) compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h s : Verifier.CanonicalScalar) (a : ValidPoint) (r : Bytes32)
    (hready : SerialBackendReadiness.Ready g d2 state)
    (hregs : TailRegisters q E) (hmem : TailMemory q state (ValidPoint.layout cofactor) h s a r) :
    ∃ after, (program p dg).runFrom E 8 state =
      .value (.cons (.value (code (decide (compress (ValidPoint.doubleBase h a s) = r)))) .nil,
        after) := by
  obtain ⟨middle, encoded, hblock, hf, hb, hp⟩ :=
    serial_block_verified p dg g d2 panic hlink cofactor q E state h s a r hready hregs hmem
  have hr : ReadBytes middle q.signature 32 r :=
    ⟨hf.live q.signature 32 hmem.signature.1,
      (hf.read q.signature 256 hmem.signatureOutput).trans hmem.signature.2⟩
  obtain ⟨after, hsuffix⟩ := compression_tail_of_contracts p dg (ValidPoint.layout cofactor) compress
    hcompress hcompare E middle q.compressed q.output q.signature
    (ValidPoint.doubleBase h a s) r encoded hregs.compressed hregs.output hregs.signature
    hregs.length hregs.zero hregs.ok hregs.error hf.wellFormed
    (hf.live q.compressed 32 hmem.compressed) hb hp hr
    hmem.compressedOutput hmem.signatureCompressed
  exact ⟨after, hblock.trans hsuffix⟩

/-- Initial serial globals supply readiness at each actual backend call after
the verifier's challenge, point checks, scalar checks and optional cache write.
Only challenge/decoder allocation shape remains a prefix-local premise; the
backend contract itself is completely discharged. -/
theorem serial_cold_context (p : Primitives)
    (hardware : Avx2Cache.Instructions.HardwareInstructions)
    (laws : Avx2Cache.Instructions.InstructionContracts hardware)
    (dg : Globals) (hprefix : SerialBackendReadiness.LinkedPrefix p hardware dg.address1)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (panic : SerialPanic) (hserial : p.serialDoubleBase = (serialLinkedKernel g d2 panic).call)
    (cofactor : ValidPoint → ValidPoint) (scg : SHA512Finalization.CompressionGlobals)
    (initial : GlobalState) (key signature message : Pointer) (length : Nat) (bytes : Bytes32)
    (hwf : initial.WF) (hkey : SmallRange initial.mem key 192)
    (hsig : SmallRange initial.mem signature 64) (hcache : SmallRange initial.mem dg.address1 1)
    (hready : SerialBackendReadiness.Ready g d2 initial)
    (hsepCache : SerialBackendReadiness.Separate g d2 dg.address1)
    (hsepSha : g.address0.id ≠ scg.cache ∧ g.address3.id ≠ scg.cache ∧ d2.address0.id ≠ scg.cache)
    (hstackCache : ∀ i, (stackSlot initial i).id ≠ scg.cache)
    (hkeyCache : key.id ≠ scg.cache) (hsigCache : signature.id ≠ scg.cache)
    (hcacheCache : dg.address1.id ≠ scg.cache)
    (hshape : SerialBackendReadiness.ShapeAt p g d2 initial key signature message length) :
    DoubleBaseContractUnder (serialLinkedReady g d2) p.serialDoubleBase
      (ValidPoint.layout cofactor) ValidPoint.doubleBase ∧
    ColdBackendsReady p (serialLinkedReady g d2) SerialBackendReadiness.noAvx scg dg
      initial key signature message length bytes := by
  constructor
  · rw [hserial]
    exact serialLinked_doubleBaseContractUnder_closed g d2 panic cofactor
  · exact SerialBackendReadiness.coldReady p hardware laws dg hprefix g d2 scg initial
      key signature message length bytes hwf hkey hsig hcache hready hsepCache hsepSha
      hstackCache hkeyCache hsigCache hcacheCache hshape

end Agave.Ed25519.Verifier.Execution.Dalek
