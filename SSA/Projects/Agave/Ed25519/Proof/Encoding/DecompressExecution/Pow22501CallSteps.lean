import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501Memory
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501WordShape
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2k

/-! Each primitive advances the abstract memory history by one proved store.
The instruction trace and all other calls remain outside these local proofs. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

theorem callState_pow2k_call (initial : GlobalState) (out : Pointer)
    (values : Nat → Words) (hwf : initial.WF) (hout : SmallRange initial.mem out 40)
    (n count : Nat) (hpos : 0 < count) (hcount : count < 2 ^ 32)
    (input : Pointer) (hin : SmallRange (scratchState initial 20).mem input 40)
    (hvalue : values n = Pow2k.iterateSquare count
      (readLimbs (callState initial out values n) input)) :
    pow22501Primitives.pow2k
      (.cons (.value (destination initial out n))
        (.cons (.value input) (.cons (.value (BitVec.ofNat 32 count)) .nil)))
      (callState initial out values n) =
        .value (.nil, callState initial out values (n + 1)) := by
  change Pow2k.program.call (Pow2k.program.args (.value (destination initial out n))
    (.value input) (.value (BitVec.ofNat 32 count))) (callState initial out values n) =
      .value (.nil, {callState initial out values n with mem := storeLimbs (callState initial out values n).mem (destination initial out n) (values n)})
  rw [hvalue]
  exact Pow2k.program_call count hpos hcount _ input _
    (callState_wf initial out values hwf n)
    (callState_live initial out values (destination_live hwf hout n) n)
    (callState_live initial out values hin n)

theorem callState_mul_call (initial : GlobalState) (out : Pointer)
    (values : Nat → Words) (hwf : initial.WF) (hout : SmallRange initial.mem out 40)
    (n : Nat) (a b : Pointer)
    (ha : SmallRange (scratchState initial 20).mem a 40)
    (hb : SmallRange (scratchState initial 20).mem b 40)
    (hvalue : values n = machine (readLimbs (callState initial out values n) a)
      (readLimbs (callState initial out values n) b)) :
    pow22501Primitives.mul
      (.cons (.value (destination initial out n)) (.cons (.value a) (.cons (.value b) .nil)))
      (callState initial out values n) =
        .value (.nil, callState initial out values (n + 1)) := by
  change kernel.call (kernel.args (.value (destination initial out n)) (.value a) (.value b))
    (callState initial out values n) =
      .value (.nil, {callState initial out values n with mem := storeLimbs (callState initial out values n).mem (destination initial out n) (values n)})
  rw [hvalue]
  exact kernel_call _ a b _ (callState_wf initial out values hwf n)
    (callState_live initial out values (destination_live hwf hout n) n)
    (callState_live initial out values ha n) (callState_live initial out values hb n)

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
