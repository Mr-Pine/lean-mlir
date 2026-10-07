import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptCorrectState

/-! A fresh private context establishes every invocation-separation premise.
This constructor leaves input and output allocations chosen by the caller. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge

def fresh (s : GlobalState) (id : BlockId) (signature publicKey message : Pointer)
    (size : BitVec 64) (output : Pointer) : TranscriptInvocation where
  initial := s.alloca 224
  constants := constantsGlobal.address id
  context := s.allocaPtr
  signature := signature
  publicKey := publicKey
  message := message
  size := size
  output := output

/-- Allocation freshness discharges all separation conditions. No message
allocation is needed when its size is zero. Input and output may alias. -/
theorem fresh_ready (s : GlobalState) (id : BlockId) (signature publicKey message : Pointer)
    (size : BitVec 64) (output : Pointer) (hwf : s.WF)
    (hk : constantsGlobal.Present id s.mem)
    (hr : SmallRange s.mem signature 32) (ha : SmallRange s.mem publicKey 32)
    (hm : size ≠ 0#64 → SmallRange s.mem message size.toNat)
    (ho : SmallRange s.mem output 64) :
    Ready (fresh s id signature publicKey message size output) id := by
  refine ⟨⟨hwf.alloca, hk.alloca hwf, smallRange_alloca_self s 224 (by decide),
    smallRange_alloca hwf hr, smallRange_alloca hwf ha,
    (fun hn => smallRange_alloca hwf (hm hn)), smallRange_alloca hwf ho⟩,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf hk.fits)
  · exact Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf hr.fits)
  · exact Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf ha.fits)
  · intro hn
    exact Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf (hm hn).fits)
  · exact GlobalState.ne_allocaPtr_of_fits hwf ho.fits

theorem fresh_message (s : GlobalState) (id : BlockId) (signature publicKey message : Pointer)
    (size : BitVec 64) (output : Pointer) (hwf : s.WF)
    (hm : size ≠ 0#64 → SmallRange s.mem message size.toNat) :
    readBytes (fresh s id signature publicKey message size output).initial.mem message size.toNat =
      readBytes s.mem message size.toNat := by
  by_cases hz : size = 0#64
  · simp [hz, readBytes]
  · exact readBytes_alloca s message 224 size.toNat hwf (hm hz)

end Agave.Ed25519.Bridge.FiredancerSHAExecution.TranscriptInvocation
