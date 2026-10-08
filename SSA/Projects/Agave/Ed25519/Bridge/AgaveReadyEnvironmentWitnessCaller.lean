import SSA.Projects.Agave.Ed25519.Bridge.AgaveReadyEnvironmentWitness
import SSA.Projects.Agave.Ed25519.Bridge.AgaveBcmpOnly

/-! Add arbitrary caller bytes to the explicit literal-global environment.
`ByteGlobal.install` is used solely as a pre-execution memory loader, including
for caller-owned mutable buffers; no immutability property is assumed. -/
namespace Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness
open LeanMLIR.RIR
open Verifier Verifier.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

def messageObject (message : List (BitVec 8)) : ByteGlobal :=
  ⟨"caller.message", message.length, BitVec.packLanes (Vector.ofFn (fun i : Fin message.length => message[i])), 1, by decide⟩
def keyObject (a : Bytes32) : ByteGlobal := ⟨"caller.key", 32, a, 1, by decide⟩
def signatureObject (r s : Bytes32) : ByteGlobal := ⟨"caller.signature", 64, s ++ r, 1, by decide⟩

def callerState (a r s : Bytes32) (message : List (BitVec 8)) : GlobalState :=
  (signatureObject r s).install ((keyObject a).install ((messageObject message).install initial))

def invocation (message : List (BitVec 8)) : Invocation :=
  ⟨ptr 13, ptr 14, ptr 12, BitVec.ofNat 64 message.length⟩

@[simp] theorem initial_next : initial.alloc.nextFreeBlock = 12 := rfl

theorem caller_wf (a r s : Bytes32) (message : List (BitVec 8)) :
    (callerState a r s message).WF :=
  ByteGlobal.wf_install _ (ByteGlobal.wf_install _ (ByteGlobal.wf_install _ initial_wf))

theorem caller_frame (a r s : Bytes32) (message : List (BitVec 8)) :
    ColdInput.CallerBlocks initial (callerState a r s message) := by
  intro id hi
  have h12 : (⟨12⟩ : BlockId) ≠ id := by intro h; cases h; simp at hi
  have h13 : (⟨13⟩ : BlockId) ≠ id := by intro h; cases h; simp at hi
  have h14 : (⟨14⟩ : BlockId) ≠ id := by intro h; cases h; simp at hi
  simp [callerState, ByteGlobal.install, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_insert, h12, h13, h14]

theorem caller_key_present (a r s : Bytes32) (message : List (BitVec 8)) :
    (keyObject a).Present ⟨13⟩ (callerState a r s message).mem := by
  simp [callerState, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem_insert]

theorem caller_signature_present (a r s : Bytes32) (message : List (BitVec 8)) :
    (signatureObject r s).Present ⟨14⟩ (callerState a r s message).mem := by
  simp [callerState, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq]

theorem caller_message_present (a r s : Bytes32) (message : List (BitVec 8)) :
    (messageObject message).Present ⟨12⟩ (callerState a r s message).mem := by
  simp [callerState, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem_insert]

theorem caller_memory (a r s : Bytes32) (message : List (BitVec 8))
    (hlen : message.length < 2^63) :
    ColdInput.CallerMemory (invocation message) (callerState a r s message) a r s message := by
  have hk := readBytes_of_present (keyObject a) ⟨13⟩ (caller_key_present a r s message) (by change 32 < 2^63; decide)
  have hs := readBytes_of_present (signatureObject r s) ⟨14⟩ (caller_signature_present a r s message) (by change 64 < 2^63; decide)
  have hm := readBytes_of_present (messageObject message) ⟨12⟩ (caller_message_present a r s message) hlen
  refine ⟨caller_wf a r s message, hk, hs.1, ?_, ?_, hm.1, ?_, rfl, hlen⟩
  · have hr := MemoryState.readAt_add_of_readAt (off := 0#64) hs.1.fits
      (by change ¬(0#64).uaddOverflow 0#64 = true; decide)
      (by change 0 * 8 + 256 ≤ 512; decide) hs.2 (w := 256)
    have hr' := hr.trans (BitVec.extractLsb'_append_eq_right (a := s) (b := r))
    simpa only [Pointer.add_zero, ByteGlobal.address, invocation, ptr] using hr'
  · have hr := MemoryState.readAt_add_of_readAt (off := 32#64) hs.1.fits
      (by change ¬(0#64).uaddOverflow 32#64 = true; decide)
      (by change 32 * 8 + 256 ≤ 512; decide) hs.2 (w := 256)
    exact hr.trans (BitVec.extractLsb'_append_eq_left (a := s) (b := r))
  · intro n hn
    have hn64 : n < 2^64 := by omega
    have hv : (BitVec.ofNat 64 n).toNat = n := by
      change n % 2^64 = n
      exact Nat.mod_eq_of_lt hn64
    have hr := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 n) hm.1.fits
      (by
        change ¬(0#64).uaddOverflow (BitVec.ofNat 64 n) = true
        simp [BitVec.uaddOverflow, hv]
        omega)
      (by simp only [hv, messageObject]; omega) hm.2 (w := 8)
    simpa [messageObject, ByteGlobal.address, invocation, ptr, hv,
      BitVec.extractLsb'_packLanes, hn] using hr


theorem caller_initialized (a r s : Bytes32) (message : List (BitVec 8)) :
    ColdInput.InitializedGlobals dg cg sg scg ddg dsg (callerState a r s message)
      (invocation message).message := by
  have hf := caller_frame a r s message
  exact ⟨hf.readBytes initial_wf initialized.identity,
    hf.range initial_wf initialized.dalekCache,
    hf.readBytes initial_wf initialized.shaIV,
    hf.compressionReady initial_wf initialized.compression,
    hf.reductionGlobals initial_wf initialized.reduction,
    hf.decoderReady initial_wf initialized.decoder,
    initialized.messageCache, initialized.reduceRCache, initialized.reduceRRCache,
    initialized.identityCache, initialized.dalekCacheCache, initialized.curveDCache,
    initialized.sqrtM1Cache⟩

theorem caller_serial_ready (a r s : Bytes32) (message : List (BitVec 8)) :
    Dalek.SerialBackendReadiness.Ready serial d2 (callerState a r s message) := by
  have hf := caller_frame a r s message
  exact ⟨⟨rfl, hf.present initial_wf present0, rfl, hf.present initial_wf present9⟩,
    ⟨rfl, hf.present initial_wf present10⟩⟩

theorem caller_avx_ready (a r s : Bytes32) (message : List (BitVec 8)) :
    DoubleBase.ExecutionAvx2.GlobalsReady avx (callerState a r s message) :=
  ⟨rfl, (caller_frame a r s message).present initial_wf present11⟩

/-- All memory premises of the actual Agave wrapper coexist for every byte
input and every message shorter than `2^63` bytes, including malformed keys/signatures and
the empty message. The constants and addresses are fixed above, independent of
caller contents. Hardware and bcmp contracts are not memory premises. -/
theorem environment_jointly_satisfiable (a r s : Bytes32) (message : List (BitVec 8))
    (hlen : message.length < 2^63) :
    ∃ (state : GlobalState) (i : Invocation),
      ColdInput.CallerMemory i state a r s message ∧
      ColdInput.InitializedGlobals dg cg sg scg ddg dsg state i.message ∧
      Dalek.SerialBackendReadiness.Ready serial d2 state ∧
      DoubleBase.ExecutionAvx2.GlobalsReady avx state ∧
      Dalek.SerialBackendReadiness.Separate serial d2 dg.address1 ∧
      avx.address2.id ≠ dg.address1.id :=
  ⟨callerState a r s message, invocation message, caller_memory a r s message hlen,
    caller_initialized a r s message, caller_serial_ready a r s message,
    caller_avx_ready a r s message, serial_separate, avx_separate⟩

/-- The closed wrapper runs in the explicit loaded environment for arbitrary
caller bytes. All caller-memory, global-readiness, and separation premises are
discharged by construction. The only remaining contracts concern the external
comparator and hardware instructions; no signature-acceptance premise is used. -/
theorem call_strict_loaded
    (compareCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [.bv 32]))
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (panic : DoubleBase.RIR.SerialPanic)
    (avx2Panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals []))
    (hhardware : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
    (hbcmp : Dalek.CompareContract compareCall)
    (a r s : Bytes32) (message : List (BitVec 8))
    (hlen : message.length < 2^63) :
    ∃ finalState, (Wrapper.program (wrapper (bcmpOnly compareCall) dg hardware
      serial d2 panic avx2Panic avx cg sg scg ddg dsg)).call
      (invocation message).args (callerState a r s message) =
        .value (Wrapper.boolResult (strictVerify a r s message), finalState) :=
  call_strict_bcmp compareCall dg hardware serial d2 panic avx2Panic avx cg sg scg ddg dsg
    hhardware hbcmp (invocation message) (callerState a r s message) a r s message
    (caller_memory a r s message hlen) (caller_initialized a r s message)
    (caller_serial_ready a r s message) (caller_avx_ready a r s message)
    serial_separate avx_separate

end Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness
