import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.DigestObservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendLinked
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionSource

/-! Memory observations needed to compose the actual five SHA calls. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem init_writes (m : MemoryState) (p : Pointer) :
    Append.BlockWrites p.id m (Init.memory m p) := by
  exact (Append.BlockWrites.refl m).store (p.add 128#64) (7640891576956012808#64) rfl
    |>.store (p.add 136#64) (13503953896175478587#64) rfl
    |>.store (p.add 144#64) (4354685564936845355#64) rfl
    |>.store (p.add 152#64) (11912009170470909681#64) rfl
    |>.store (p.add 160#64) (5840696475078001361#64) rfl
    |>.store (p.add 168#64) (11170449401992604703#64) rfl
    |>.store (p.add 176#64) (2270897969802886507#64) rfl
    |>.store (p.add 184#64) (6620516959819538809#64) rfl
    |>.store (p.add 200#64) (0#192) rfl

theorem writes_readAt {id : BlockId} {m n : MemoryState}
    (h : Append.BlockWrites id m n) (p : Pointer) (bits : Nat) (hp : p.id ≠ id) :
    n.readAt p bits = m.readAt p bits := by
  unfold MemoryState.readAt
  rw [h.other p.id hp]

theorem writes_readBytes {id : BlockId} {m n : MemoryState}
    (h : Append.BlockWrites id m n) (p : Pointer) (bytes : Nat) (hp : p.id ≠ id) :
    readBytes n p bytes = readBytes m p bytes := by
  unfold readBytes
  congr 1
  funext i
  exact writes_readAt h _ _ hp

theorem bytesOf_injective {n : Nat} {x y : BitVec (n * 8)}
    (h : bytesOf x = bytesOf y) : x = y := by
  apply BitVec.eq_of_toNat_eq
  simpa only [decodeLE_bytesOf] using congrArg decodeLE h

theorem readAt_of_readBytes (m : MemoryState) (p : Pointer) (bytes : Nat)
    (x : BitVec (bytes * 8)) (hr : SmallRange m p bytes)
    (h : readBytes m p bytes = bytesOf x) : m.readAt p (bytes * 8) = x := by
  rw [readBytes_eq_bytesOf _ _ _ hr] at h
  exact bytesOf_injective h

theorem finishState_output_live (s : GlobalState) (context output kp : Pointer)
    (used : Nat) (lo hi : BitVec 64) (h : Finish.Ready s context output kp) :
    SmallRange (Finish.finishState s context output used lo hi).mem output 64 := by
  have hp := (h.preOutput used lo hi).outputLive
  unfold Finish.finishState Finish.finalOutputState Finish.outputMemory
  exact hp.storeAt _ _ |>.storeAt _ _ |>.storeAt _ _ |>.storeAt _ _
    |>.storeAt _ _ |>.storeAt _ _ |>.storeAt _ _ |>.storeAt _ _

/-- Strengthen the source finalizer endpoint with output liveness. This is
derived from its exact checked state, not inferred from the digest bytes. -/
theorem finish_source_live (id : BlockId) (context output : Pointer) (s : GlobalState)
    (completed pending : Bytes) (hwf : s.WF)
    (hp : ContextRepresents s.mem context completed pending)
    (ho : SmallRange s.mem output 64) (hk : constantsGlobal.Present id s.mem)
    (hck : context.id ≠ id) (hoc : output.id ≠ context.id) :
    ∃ after,
      (finishProgram (constantsGlobal.address id)).call
        (Finish.program.args (.value context) (.value output)) s =
        .value (.cons (.value output) .nil, after) ∧
      Finish.Result s after context output completed pending ∧
      SmallRange after.mem output 64 := by
  obtain ⟨after, hcall, hresult⟩ := Finish.call_digest_source id context output s
    completed pending hwf hp ho hk hck hoc
  have hr : Finish.Ready s context output (constantsGlobal.address id) :=
    ⟨hwf, hp.live, ho, Finish.constantsReady_source s id hk, hck, hoc⟩
  have hexact := Finish.call (constantsGlobal.address id) context output s pending.length
    (s.mem.readAt (context.add 208#64) 64) (s.mem.readAt (context.add 216#64) 64)
    hr hp.pendingBound hp.pendingCount rfl rfl
  rw [hcall] at hexact
  have heq : after = Finish.finishState s context output pending.length
      (s.mem.readAt (context.add 208#64) 64) (s.mem.readAt (context.add 216#64) 64) := by
    cases hexact
    rfl
  refine ⟨after, hcall, hresult, ?_⟩
  rw [heq]
  exact finishState_output_live _ _ _ _ _ _ _ hr

end Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
