import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendMessageExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreCorrect

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
namespace MessageExecution
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] append core

/-- Closed actual execution theorem for the third append at pending count 64.
There is no core, append, or digest execution hypothesis. -/
theorem executes (s : GlobalState) (p data kp : Pointer) (n : BitVec 64)
    (h : Ready s p data kp n)
    (hcount : sourceRead s.mem (p.withOffset 200#64) 64 = 64#64) :
    ∃ after : GlobalState,
      StateT.run (runFunction (append.denote
        (Ctxt.Valuation.ofHVector [.value n, .value data, .value p]ₕ))) s =
        .value ([.value p]ₕ, after) ∧
      after.WF ∧ after.alloc = s.alloc ∧ after.globals = s.globals ∧
      (∀ q, after.mem.live? q = (resultState s p data n).mem.live? q) ∧
      (∀ q, q ≠ p.id → after.mem.live? q = s.mem.live? q) :=
  call Core.executes s p data kp n h hcount

end MessageExecution
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
