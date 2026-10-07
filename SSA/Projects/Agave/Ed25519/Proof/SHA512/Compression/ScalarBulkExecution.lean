import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkLoop
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkPrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkZeroMemory

/-! Arbitrary-count refinement of the imported warm scalar dispatcher. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open ScalarFull

/-- Exact full scalar execution for every live count, including zero. The
source keeps all intermediate chaining words in registers, so the entire
execution changes only the final 64-byte chaining-state store. -/
theorem warm_scalar_bulk (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hkr : SmallRange state.mem g.address1 640) (hbr : SmallRange state.mem g.address0 1)
    (hk : KRead state.mem g.address1) (hb : state.mem.readAt g.address0 8 = 0#8)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    (program p g).runFrom E 0 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * count.toNat)))}) := by
  cases hn : count.toNat with
  | zero =>
    have hz : count = 0#64 := BitVec.eq_of_toNat_eq hn
    subst count
    have hzrun := warm_zero_runFrom p g E state data hkr hbr hb (by simpa using hd) hdata hcount
    simpa [Spec.compression, readBytes, Spec.run_empty, store_read_self] using hzrun
  | succ n =>
    have hz : count ≠ 0#64 := by intro hz; subst count; simp at hn
    rw [warm_positive_runFrom p g E state chain data count hz hkr hbr hb hc hd hchain hdata hcount]
    have hcur := body_cursor E g state chain data count
    have hloop := scalar_loop_positive p g state chain g.address1 hc hk n
      (bodyEnv E g state chain data count) data (scalarChainState state.mem chain)
      (by simpa only [hn] using hd)
      (body_initial E g state chain data count) (body_store E g state chain data count hchain)
      (body_constants E g state chain data count) hcur.1 (by simpa only [hn] using hcur.2)
    simpa only [Spec.compression, hn, scalarChainState_eq_unpack state.mem chain hc,
      Spec.pack_unpack] using hloop

theorem warm_scalar_bulk_of_ready (p : Primitives) (cg : CompressionGlobals)
    (E : Env program.Γ) (state : GlobalState) (chain data : Pointer) (count : BitVec 64)
    (hg : CompressionReady cg state)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hb : state.mem.readAt cg.cachePtr 8 = 0#8)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    (program p (readyGlobals cg)).runFrom E 0 state = .value (.nil,
      {state with mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * count.toNat)))}) :=
  warm_scalar_bulk p (readyGlobals cg) E state chain data count hc hd hg.constants_range hg.cache_range
    (constants_read cg state hg) hb hchain hdata hcount

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
