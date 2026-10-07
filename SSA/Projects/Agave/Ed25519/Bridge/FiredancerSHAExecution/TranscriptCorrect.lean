import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrectComposition
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendSemantic
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrectPrepare

/-! Concrete SHA correctness for the actual imported Firedancer transcript
calls. The only assumptions describe the initial memory and original input
bytes; no append, compression, finalization, or digest equation is assumed. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge Agave.Ed25519.SHA512
open Agave.Ed25519.Verifier.Execution.Challenge

theorem append_preserves : AppendPreserves :=
  Append.Semantic.result_represents_exists

/-- The verifier's actual imported five-call sequence returns a defined
64-byte digest of R || A || M and preserves the rest of the caller's memory. -/
theorem execution (v : TranscriptInvocation) (id : BlockId)
    (r a : BitVec 256) (message : HashBytes) (h : Ready v id)
    (hr : readBytes v.initial.mem v.signature 32 = bytesOf (n := 32) r)
    (ha : readBytes v.initial.mem v.publicKey 32 = bytesOf (n := 32) a)
    (hm : readBytes v.initial.mem v.message v.size.toNat = message) :
    ∃ after, ExecutionResult v after r a message :=
  execution_of_append_semantics append_preserves v id r a message h hr ha hm

theorem correct (v : TranscriptInvocation) (id : BlockId)
    (r a : BitVec 256) (message : HashBytes) (h : Ready v id)
    (hr : readBytes v.initial.mem v.signature 32 = bytesOf (n := 32) r)
    (ha : readBytes v.initial.mem v.publicKey 32 = bytesOf (n := 32) a)
    (hm : readBytes v.initial.mem v.message v.size.toNat = message) :
    v.Correct r a message :=
  correct_of_append_semantics append_preserves v id r a message h hr ha hm

/-- Read the original signature, public key, and message directly from the
invocation. This version requires no input-value equality premises. -/
theorem execution_reads (v : TranscriptInvocation) (id : BlockId) (h : Ready v id) :
    ∃ after, ExecutionResult v after
      (v.initial.mem.readAt v.signature 256) (v.initial.mem.readAt v.publicKey 256)
      (readBytes v.initial.mem v.message v.size.toNat) :=
  execution v id _ _ _ h (readBytes_eq_bytesOf _ _ _ h.signatureLive)
    (readBytes_eq_bytesOf _ _ _ h.publicKeyLive) rfl

theorem correct_reads (v : TranscriptInvocation) (id : BlockId) (h : Ready v id) :
    v.Correct (v.initial.mem.readAt v.signature 256)
      (v.initial.mem.readAt v.publicKey 256)
      (readBytes v.initial.mem v.message v.size.toNat) := by
  obtain ⟨after, hafter⟩ := execution_reads v id h
  exact hafter.correct

/-- A concrete fresh context discharges all separation premises and preserves
the caller's original input observations through allocation. -/
theorem fresh_execution (s : GlobalState) (id : BlockId) (signature publicKey message : Pointer)
    (size : BitVec 64) (output : Pointer) (hwf : s.WF)
    (hk : constantsGlobal.Present id s.mem)
    (hr : SmallRange s.mem signature 32) (ha : SmallRange s.mem publicKey 32)
    (hm : size ≠ 0#64 → SmallRange s.mem message size.toNat)
    (ho : SmallRange s.mem output 64) :
    ∃ after, ExecutionResult (fresh s id signature publicKey message size output) after
      (s.mem.readAt signature 256) (s.mem.readAt publicKey 256)
      (readBytes s.mem message size.toNat) :=
  execution _ id _ _ _ (fresh_ready s id signature publicKey message size output hwf hk hr ha hm ho)
    ((readBytes_alloca s signature 224 32 hwf hr).trans (readBytes_eq_bytesOf _ _ _ hr))
    ((readBytes_alloca s publicKey 224 32 hwf ha).trans (readBytes_eq_bytesOf _ _ _ ha))
    (fresh_message s id signature publicKey message size output hwf hm)

theorem fresh_correct (s : GlobalState) (id : BlockId) (signature publicKey message : Pointer)
    (size : BitVec 64) (output : Pointer) (hwf : s.WF)
    (hk : constantsGlobal.Present id s.mem)
    (hr : SmallRange s.mem signature 32) (ha : SmallRange s.mem publicKey 32)
    (hm : size ≠ 0#64 → SmallRange s.mem message size.toNat)
    (ho : SmallRange s.mem output 64) :
    (fresh s id signature publicKey message size output).Correct
      (s.mem.readAt signature 256) (s.mem.readAt publicKey 256)
      (readBytes s.mem message size.toNat) := by
  obtain ⟨after, hafter⟩ := fresh_execution s id signature publicKey message size output hwf hk hr ha hm ho
  exact hafter.correct

/-- Machine-size representability follows from the actual input observation;
it is not an extra premise restricting the transcript's accumulated length. -/
theorem message_length_lt (v : TranscriptInvocation) (message : HashBytes)
    (hm : readBytes v.initial.mem v.message v.size.toNat = message) :
    message.length < 2 ^ 64 := by
  rw [← hm, readBytes_length]
  exact v.size.isLt

end Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
