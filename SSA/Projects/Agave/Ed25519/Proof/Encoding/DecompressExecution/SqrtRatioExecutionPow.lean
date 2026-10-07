import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2k
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow22501
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LinkedCalls
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.LimbMemory

/-! The two sqrt-ratio call boundaries missing from `LinkedCalls`. The two-square
call uses the checked imported Pow2k body. The addition-chain contract is stated
at its actual lower-call boundary so its proof can be supplied independently. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

def sqrtPow22501State (s : GlobalState) (r a : Pointer) : GlobalState :=
  { alloc := ⟨s.alloc.nextFreeBlock + 20⟩,
    mem := (storeLimbs s.mem r (Pow22501.rawWordChain (readLimbs s a)).1).storeAt
      (r.add 40#64) (limbBytes (Pow22501.rawWordChain (readLimbs s a)).2) }

/-- Exactly the imported addition-chain call interface, including both output
fields and the twenty private allocations. This is a premise, not an axiom. -/
def SqrtPow22501Call : Prop :=
  ∀ (r a : Pointer) (s : GlobalState), s.WF →
    SmallRange s.mem r 80 → SmallRange s.mem a 40 →
    (Pow22501.program pow22501Primitives).call
        (Pow22501.program.args (.value r) (.value a)) s =
      .value (.nil, sqrtPow22501State s r a)

theorem sqrtratio_pow22501_0_100 (hpow : SqrtPow22501Call)
    (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 80) (ha : SmallRange s.mem a 40)
    (hout : E.read (%69) = .value r) (hin : E.read (%76) = .value a) :
    Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 100 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 101 E
        (sqrtPow22501State s r a) := by
  apply SqrtRatio.call_0_100 sqrtRatioPrimitives g E s _ r a hout hin
  simpa only [sqrtRatioPrimitives, Pow22501.program.args] using hpow r a s hwf hr ha

theorem sqrtratio_pow2k_0_105 (g : SqrtRatio.Globals) (E : ⟪SqrtRatio.program.Γ⟫)
    (s : GlobalState) (r a : Pointer) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hout : E.read (%68) = .value r) (hin : E.read (%70) = .value a)
    (hcount : E.read (%2) = .value 2#32) :
    Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 105 E s =
      Cutpoint.resume (SqrtRatio.program sqrtRatioPrimitives g) 0 106 E
        {s with mem := storeLimbs s.mem r (Pow2k.iterateSquare 2 (readLimbs s a))} := by
  apply SqrtRatio.call_0_105 sqrtRatioPrimitives g E s _ r a 2#32 hout hin hcount
  simpa only [sqrtRatioPrimitives, Pow2k.program.args] using
    Pow2k.program_call 2 (by decide) (by decide) r a s hwf hr ha

end Agave.Ed25519.Encoding.Decompress.Execution
