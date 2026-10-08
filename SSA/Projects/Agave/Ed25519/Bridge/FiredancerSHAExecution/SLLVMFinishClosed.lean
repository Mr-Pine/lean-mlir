import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishAdapter
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreCorrect

/-! Closed actual-source finalizer endpoints. The local compression dependency
is discharged by the proved imported scalar core, not assumed by callers. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer Firedancer.Common
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
namespace FinishCorrect
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem call_digest_source (s : GlobalState) (p o kp : Pointer) (completed pending : Bytes)
    (h : Ready s p o kp) (hp : ContextRepresents s.mem p completed pending) :
    ∃ after, StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, after) ∧ Post s after p o (completed ++ pending) :=
  call_digest Core.executes s p o kp completed pending h hp

theorem call_digest_constants_source (s : GlobalState) (p o : Pointer) (completed pending : Bytes)
    (hw : s.WF) (hc : Core.SmallRange s.mem p 224) (ho : Core.SmallRange s.mem o 64)
    (hne : o.id ≠ p.id) (hp : ContextRepresents s.mem p completed pending)
    (hk : Sha512KHolds s p constantsBytes)
    (hs : ∀ q, GlobalPtr s "fd_sha512_core_ref.K" q →
      ∀ b, s.mem.live? q.id = some b → b.length < 2^63) :
    ∃ after, StateT.run (runFunction (finish.denote
        (.cons (.value o) (Ctxt.Valuation.singleton (.value p))))) s =
      .value ([.value o]ₕ, after) ∧ Post s after p o (completed ++ pending) :=
  call_digest_constants Core.executes s p o completed pending hw hc ho hne hp hk hs

theorem reachable_finish_source (block : LiveBlock) (off : BitVec 64) (completed pending : Bytes)
    (hsmall : block.length < 2^63) (hrep : BlockRepresents block off completed pending) :
    Agave.Ed25519.Bridge.FiredancerReachableFinish programs constantsBytes (some block) off
      (digest Spec.compression (completed ++ pending)) :=
  reachable_finish Core.executes block off completed pending hsmall hrep

end FinishCorrect
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
