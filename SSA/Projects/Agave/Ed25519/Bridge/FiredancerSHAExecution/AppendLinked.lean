import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreBulkCall

/-! Concrete C append endpoint. Its compression calls execute the imported
scalar core proved in CoreBulkCall; no SHA call equation is assumed. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

noncomputable def linkedCore (id : BlockId) : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []) :=
  (Core.program (constantsGlobal.address id)).call

theorem linked_core_contract (id : BlockId) : CoreCallContract (linkedCore id) id := by
  intro s chain data count hwf hc hd hk hn hck hdis
  exact Core.core_call_blocks_source id chain data s count hwf hc hd hk hn hck hdis

/-- Any finite input fitting its live source allocation, any valid pending
count, and arbitrary chaining/counter bytes. The caller need not have started
from SHA's IV. Size-zero execution has the still weaker zero_call endpoint. -/
theorem linked_call (id : BlockId) (s : GlobalState) (context data : Pointer) (size : Word)
    (hr : Resources id s context data size)
    (hused : (s.mem.readAt (context.add 200#64) 64).toNat < 128) :
    (program (linkedCore id)).call (program.args (.value context) (.value data) (.value size)) s =
      .value (.cons (.value context) .nil, resultState s context data size) :=
  call (linkedCore id) id (linked_core_contract id) s context data size hr hused

/-- The return is defined and exact, and all unrelated allocations are
unchanged, including the source and the pinned constants. -/
theorem linked_call_frame (id : BlockId) (s : GlobalState) (context data : Pointer) (size : Word)
    (hr : Resources id s context data size)
    (hused : (s.mem.readAt (context.add 200#64) 64).toNat < 128) :
    ∃ after,
      (program (linkedCore id)).call (program.args (.value context) (.value data) (.value size)) s =
        .value (.cons (.value context) .nil, after) ∧
      after = resultState s context data size ∧ after.WF ∧
      (∀ j : BlockId, j ≠ context.id → after.mem[j]? = s.mem[j]?) ∧
      constantsGlobal.Present id after.mem := by
  exact ⟨_, linked_call id s context data size hr hused, rfl,
    result_wf s context data size hr.wf,
    fun j hj => (result_writes s context data size).other j hj,
    (result_writes s context data size).present constantsGlobal id (Ne.symm hr.immutable) hr.constants⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
