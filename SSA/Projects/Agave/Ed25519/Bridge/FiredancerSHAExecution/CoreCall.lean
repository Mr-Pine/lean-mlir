import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreOne
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreOuterMemory

/-! Complete one-block C core call contract: the caller-visible change is exactly
one native packed chaining-state store, and the private ring is erased. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def coreCallState (state : GlobalState) (chain data : Pointer) (initial : State) : GlobalState :=
  {alloc := ⟨state.alloc.nextFreeBlock + 1⟩,
   mem := state.mem.storeAt chain (pack (compressBlock initial (readBytes state.mem data 128)))}

/-- No core-execution premise is assumed. Entry, all eighty rounds, feedforward,
return, and frame erasure are proved from the actual imported basic blocks. -/
theorem core_call_one (kp chain data : Pointer) (state : GlobalState) (initial : State)
    (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data 128) (hk : SmallRange state.mem kp 640)
    (hm : ChainMemory state.mem chain initial)
    (htable : ∀ j, j < 80 → state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    (program kp).call (program.args (.value chain) (.value data) (.value 1#64)) state =
      .value (.nil, coreCallState state chain data initial) := by
  simpa only [feedforwardMemory_eq state.mem chain hc, coreCallState] using
    core_call_one_stores kp chain data state initial hwf hc hd hk hm htable

theorem core_call_one_packed (kp chain data : Pointer) (state : GlobalState) (initial : State)
    (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data 128) (hk : SmallRange state.mem kp 640)
    (hm : state.mem.readAt chain 512 = pack initial)
    (htable : ∀ j, j < 80 → state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    (program kp).call (program.args (.value chain) (.value data) (.value 1#64)) state =
      .value (.nil, coreCallState state chain data initial) :=
  core_call_one kp chain data state initial hwf hc hd hk
    (chainMemory_of_packed state.mem chain hc initial hm) htable

theorem coreCallState_wf (state : GlobalState) (chain data : Pointer) (initial : State)
    (hwf : state.WF) : (coreCallState state chain data initial).WF := by
  exact hwf.add_blocks.storeAt

theorem coreCallState_live (state : GlobalState) (chain data p : Pointer) (initial : State)
    (bytes : Nat) (h : SmallRange state.mem p bytes) :
    SmallRange (coreCallState state chain data initial).mem p bytes := h.storeAt _ _

theorem coreCallState_read (state : GlobalState) (chain data : Pointer) (initial : State)
    (hc : SmallRange state.mem chain 64) :
    (coreCallState state chain data initial).mem.readAt chain 512 =
      pack (compressBlock initial (readBytes state.mem data 128)) :=
  MemoryState.readAt_storeAt_self hc.fits _

/-- Every other allocation is exactly unchanged, including all caller buffers
and installed constants that do not share the chaining-state allocation. -/
theorem coreCallState_other_block (state : GlobalState) (chain data : Pointer) (initial : State)
    (id : BlockId) (hne : id ≠ chain.id) :
    (coreCallState state chain data initial).mem[id]? = state.mem[id]? :=
  MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hne

/-- The finer caller frame also covers disjoint byte ranges in the same allocation. -/
theorem coreCallState_readAt_frame (state : GlobalState) (chain data p : Pointer)
    (initial : State) (bits : Nat)
    (h : (Range.of chain 512).Disjoint (Range.of p bits)) :
    (coreCallState state chain data initial).mem.readAt p bits = state.mem.readAt p bits :=
  MemoryState.readAt_storeAt_disjoint h _

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
