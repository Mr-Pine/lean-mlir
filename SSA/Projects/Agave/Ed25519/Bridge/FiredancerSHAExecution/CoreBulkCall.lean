import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreMultiBlocks
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreConstants

/-! Full actual scalar core call over any positive number of live input blocks,
including the sole private ring allocation and caller-visible frame. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def coreBulkState (state : GlobalState) (chain data : Pointer) (n : Nat) : GlobalState :=
  {alloc := ⟨state.alloc.nextFreeBlock + 1⟩,
   mem := state.mem.storeAt chain (Spec.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * n)))}

theorem core_call_blocks_succ (kp chain data : Pointer) (state : GlobalState)
    (initial : State) (n : Nat) (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data (128 * (n + 1))) (hk : SmallRange state.mem kp 640)
    (hm : state.mem.readAt chain 512 = pack initial) (hck : chain.id ≠ kp.id)
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * (n + 1)))))
    (htable : ∀ j, j < 80 → state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    (program kp).call (program.args (.value chain) (.value data) (.value (BitVec.ofNat 64 (n + 1)))) state =
      .value (.nil, coreBulkState state chain data (n + 1)) := by
  let E := Env.init (program.args (.value chain) (.value data) (.value (BitVec.ofNat 64 (n + 1)))).get
  let F := outerNextEnv (coreEntryEnv E kp chain state.allocaPtr initial) initial data (n + 1)
  have hc' : SmallRange (state.alloca 128).mem chain 64 := smallRange_alloca hwf hc
  have hd' : SmallRange (state.alloca 128).mem data (128 * (n + 1)) := smallRange_alloca hwf hd
  have hk' : SmallRange (state.alloca 128).mem kp 640 := smallRange_alloca hwf hk
  have ht' : ∀ j, j < 80 → (state.alloca 128).mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0 := by
    intro j hj
    rw [MemoryState.readAt_alloca hwf (hk.fits_add (k := 8 * j) (count := 8) (by omega))]
    exact htable j hj
  obtain ⟨after, hr, _, ha, he⟩ := core_outer_blocks n kp chain state.allocaPtr data F
    (state.alloca 128) initial state.alloc.nextFreeBlock hwf.alloca (Nat.le_refl _)
    (outerNext_ready _ _ _ _)
    (coreEntry_outerPointers E kp chain state.allocaPtr data initial (n + 1) rfl)
    (coreEntry_firstReady E kp chain state.allocaPtr data initial (n + 1))
    hc' (coreEntry_live state hwf) hd' hk'
    (Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf hk.fits))
    (Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf hd.fits)) hck hdis ht'
  have hrun : (program kp).run
      (program.args (.value chain) (.value data) (.value (BitVec.ofNat 64 (n + 1)))) state =
      .value (.nil, after) := by
    rw [Func.run_runFrom_eq, Func.runFrom_eq]
    change ((program.bb0 kp).run program.blockParams E state >>= _) = _
    rw [coreEntry_block E state kp chain data (n + 1) initial hwf rfl rfl rfl hc
      (chainMemory_of_packed state.mem chain hc initial hm)]
    exact hr
  have hbytes := readBytes_alloca state data 128 (128 * (n + 1)) hwf hd
  rw [coreEntry_frame state hwf, hbytes, ← hm] at he
  have hcall := Func.call_of_run hrun
  simpa only [he, ha, GlobalState.alloca, coreBulkState] using hcall

/-- Bitvector-ABI endpoint. The live input bound supplies the safety bound for
all flagged count and pointer arithmetic; no extra machine execution premise occurs. -/
theorem core_call_blocks (kp chain data : Pointer) (state : GlobalState) (count : Word)
    (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data (128 * count.toNat)) (hk : SmallRange state.mem kp 640)
    (hn : 0 < count.toNat) (hck : chain.id ≠ kp.id)
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))))
    (htable : ∀ j, j < 80 → state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    (program kp).call (program.args (.value chain) (.value data) (.value count)) state =
      .value (.nil, coreBulkState state chain data count.toNat) := by
  obtain ⟨n, hn'⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : count.toNat ≠ 0)
  have h := core_call_blocks_succ kp chain data state (unpack (state.mem.readAt chain 512)) n
    hwf hc (by simpa [hn'] using hd) hk (pack_unpack _).symm hck (by simpa [hn'] using hdis) htable
  simpa [← hn'] using h

theorem core_call_blocks_source (id : BlockId) (chain data : Pointer) (state : GlobalState)
    (count : Word) (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data (128 * count.toNat))
    (hk : constantsGlobal.Present id state.mem) (hn : 0 < count.toNat)
    (hck : chain.id ≠ id)
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat)))) :
    (program (constantsGlobal.address id)).call
      (program.args (.value chain) (.value data) (.value count)) state =
      .value (.nil, coreBulkState state chain data count.toNat) :=
  core_call_blocks _ chain data state count hwf hc hd (constants_present_range state id hk)
    hn hck hdis (constants_present_word state id hk)

theorem coreBulkState_effect (state : GlobalState) (chain data : Pointer) (n : Nat) :
    StoreEffect state (coreBulkState state chain data n) chain
      (Spec.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * n))) :=
  ⟨rfl, Nat.le_succ _⟩

theorem coreBulkState_wf (state : GlobalState) (chain data : Pointer) (n : Nat)
    (hwf : state.WF) : (coreBulkState state chain data n).WF :=
  (coreBulkState_effect state chain data n).wellFormed hwf

theorem coreBulkState_live (state : GlobalState) (chain data p : Pointer) (n bytes : Nat)
    (h : SmallRange state.mem p bytes) :
    SmallRange (coreBulkState state chain data n).mem p bytes := h.storeAt _ _

theorem coreBulkState_read (state : GlobalState) (chain data : Pointer) (n : Nat)
    (hc : SmallRange state.mem chain 64) :
    (coreBulkState state chain data n).mem.readAt chain 512 =
      Spec.run (state.mem.readAt chain 512) (readBytes state.mem data (128 * n)) :=
  MemoryState.readAt_storeAt_self hc.fits _

theorem coreBulkState_readAt_frame (state : GlobalState) (chain data p : Pointer)
    (n bits : Nat) (h : (Range.of chain 512).Disjoint (Range.of p bits)) :
    (coreBulkState state chain data n).mem.readAt p bits = state.mem.readAt p bits :=
  MemoryState.readAt_storeAt_disjoint h _

theorem coreBulkState_constants (id : BlockId) (chain data : Pointer) (state : GlobalState)
    (n : Nat) (hk : constantsGlobal.Present id state.mem) (hne : id ≠ chain.id) :
    constantsGlobal.Present id (coreBulkState state chain data n).mem := hk.storeAt hne

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
