import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreEntry
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreEightyRounds

/-! Composition of entry, eighty actual rounds, feedforward, return, and private
frame cleanup for one scalar C compression call. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem LoopFrame.outerState {E F : Env program.Γ} (h : LoopFrame E F)
    {s : State} (ho : OuterStateReady E s) : OuterStateReady F s := by
  constructor
  · exact (h.read_val _ (by decide) rfl).trans ho.a
  · exact (h.read_val _ (by decide) rfl).trans ho.b
  · exact (h.read_val _ (by decide) rfl).trans ho.c
  · exact (h.read_val _ (by decide) rfl).trans ho.d
  · exact (h.read_val _ (by decide) rfl).trans ho.e
  · exact (h.read_val _ (by decide) rfl).trans ho.f
  · exact (h.read_val _ (by decide) rfl).trans ho.g
  · exact (h.read_val _ (by decide) rfl).trans ho.h

theorem LoopFrame.outerPointers {E F : Env program.Γ} (h : LoopFrame E F)
    {chain data : Pointer} {n : Nat} (hp : OuterPointersReady E chain data n) :
    OuterPointersReady F chain data n := by
  constructor
  · change F.args 0 = _
    rw [h.1]
    exact hp.p0
  · exact (h.read_val _ (by decide) rfl).trans hp.p8
  · exact (h.read_val _ (by decide) rfl).trans hp.p16
  · exact (h.read_val _ (by decide) rfl).trans hp.p24
  · exact (h.read_val _ (by decide) rfl).trans hp.p32
  · exact (h.read_val _ (by decide) rfl).trans hp.p40
  · exact (h.read_val _ (by decide) rfl).trans hp.p48
  · exact (h.read_val _ (by decide) rfl).trans hp.p56
  · exact (h.read_val _ (by decide) rfl).trans hp.data
  · exact (h.read_val _ (by decide) rfl).trans hp.count
  · exact (h.read_val _ (by decide) rfl).trans hp.zero
  · exact (h.read_val _ (by decide) rfl).trans hp.minusOne
  · exact (h.read_val _ (by decide) rfl).trans hp.blockSize

theorem coreEntry_firstReady (E : Env program.Γ) (kp chain stack data : Pointer)
    (s : State) (n : Nat) :
    FirstLoopReady (firstNextEnv (outerNextEnv (coreEntryEnv E kp chain stack s) s data n) 0 s)
      stack data kp 0 s := by
  constructor
  · exact firstNext_ready _ _ _
  · constructor <;> simp [firstNextEnv, outerNextEnv, coreEntryEnv, entryConstants, mlir_env]
  · constructor <;> simp [firstNextEnv, outerNextEnv, coreEntryEnv, entryConstants, mlir_env]
  · constructor <;> simp [laterNextEnv, firstNextEnv, outerNextEnv, coreEntryEnv, entryConstants, mlir_env]
  · simp [firstNextEnv, outerNextEnv, coreEntryEnv, entryConstants, mlir_env]
  · simp [firstNextEnv, outerNextEnv, coreEntryEnv, entryConstants, mlir_env]

theorem coreEntry_outerPointers (E : Env program.Γ) (kp chain stack data : Pointer)
    (s : State) (n : Nat) (hp : E.read (%arg0) = .value chain) :
    OuterPointersReady (outerNextEnv (coreEntryEnv E kp chain stack s) s data n) chain data n := by
  have hp0 : E.args 0 = .value chain := hp
  constructor <;> simp [outerNextEnv, coreEntryEnv, entryConstants, mlir_env, hp0]

/-- Actual execution from the beginning of one outer iteration to return.
The round premise consists only of register constants and live input memory. -/
theorem core_one_from_outer (kp chain stack data : Pointer) (E : Env program.Γ)
    (before : GlobalState) (initial : State)
    (ho : OuterStateReady E initial) (hp : OuterPointersReady E chain data 1)
    (hfirst : FirstLoopReady (firstNextEnv E 0 initial) stack data kp 0 initial)
    (hc : SmallRange before.mem chain 64) (hs : SmallRange before.mem stack 128)
    (hd : SmallRange before.mem data 128) (hk : SmallRange before.mem kp 640)
    (hsk : stack.id ≠ kp.id) (hsd : stack.id ≠ data.id)
    (htable : ∀ j, j < 80 → before.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    ∃ middle, RingWrites stack before middle ∧
      (program kp).runFrom E 1 before =
        .value (.nil, {middle with mem := feedforwardMemory middle.mem chain (compressBlock initial (readBytes before.mem data 128))}) := by
  obtain ⟨F, middle, ht, hf, hw, he⟩ := eighty_from_input stack data kp
    (firstNextEnv E 0 initial) before initial hfirst hs hd hk hsk hsd htable
  have hframe := (firstNext_frame E 0 initial).trans he
  have hlast := feedforward_last F middle chain data initial
    (roundsFrom initial (schedule (readBytes before.mem data 128)) 0 80)
    (hframe.outerState ho) hf (hframe.outerPointers hp) (hw.smallRange hc) (hw.smallRange hd)
  refine ⟨middle, hw, ?_⟩
  rw [Func.runFrom_eq]
  change (program.bb1.run program.blockParams E before >>= _) = _
  rw [outer_start E before initial ho hp.zero]
  change (program kp).runFrom (firstNextEnv E 0 initial) 2 before = _
  rw [ht.runFrom kp, Func.runFrom_eq]
  change (program.bb4.run program.blockParams F middle >>= _) = _
  rw [hlast]
  change (program kp).runFrom _ 5 _ = _
  rw [Func.runFrom_eq]
  rfl

/-- One complete imported core run, retaining the fresh ring in the raw run state.
The following call theorem removes exactly that private allocation. -/
theorem core_run_one (kp chain data : Pointer) (state : GlobalState) (initial : State)
    (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data 128) (hk : SmallRange state.mem kp 640)
    (hm : ChainMemory state.mem chain initial)
    (htable : ∀ j, j < 80 → state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    ∃ middle, RingWrites state.allocaPtr (state.alloca 128) middle ∧
      (program kp).run (program.args (.value chain) (.value data) (.value 1#64)) state =
        .value (.nil, {middle with mem := feedforwardMemory middle.mem chain (compressBlock initial (readBytes state.mem data 128))}) := by
  let E := Env.init (program.args (.value chain) (.value data) (.value 1#64)).get
  let F := outerNextEnv (coreEntryEnv E kp chain state.allocaPtr initial) initial data 1
  have hc' : SmallRange (state.alloca 128).mem chain 64 := smallRange_alloca hwf hc
  have hd' : SmallRange (state.alloca 128).mem data 128 := smallRange_alloca hwf hd
  have hk' : SmallRange (state.alloca 128).mem kp 640 := smallRange_alloca hwf hk
  have ht' : ∀ j, j < 80 → (state.alloca 128).mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0 := by
    intro j hj
    rw [MemoryState.readAt_alloca hwf (hk.fits_add (k := 8 * j) (count := 8) (by omega))]
    exact htable j hj
  obtain ⟨middle, hw, hr⟩ := core_one_from_outer kp chain state.allocaPtr data F
    (state.alloca 128) initial (outerNext_ready _ _ _ _)
    (coreEntry_outerPointers E kp chain state.allocaPtr data initial 1 rfl)
    (coreEntry_firstReady E kp chain state.allocaPtr data initial 1)
    hc' (coreEntry_live state hwf) hd' hk'
    (Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf hk.fits))
    (Ne.symm (GlobalState.ne_allocaPtr_of_fits hwf hd.fits)) ht'
  have hbytes : readBytes (state.alloca 128).mem data 128 = readBytes state.mem data 128 := readBytes_alloca state data 128 128 hwf hd
  rw [hbytes] at hr
  refine ⟨middle, hw, ?_⟩
  rw [Func.run_runFrom_eq, Func.runFrom_eq]
  change ((program.bb0 kp).run program.blockParams E state >>= _) = _
  rw [coreEntry_block E state kp chain data 1 initial hwf rfl rfl rfl hc hm]
  exact hr

/-- Private ring writes disappear at call cleanup; the one fresh allocation id
remains consumed, as required by the RIR allocator semantics. -/
theorem core_call_one_stores (kp chain data : Pointer) (state : GlobalState) (initial : State)
    (hwf : state.WF) (hc : SmallRange state.mem chain 64)
    (hd : SmallRange state.mem data 128) (hk : SmallRange state.mem kp 640)
    (hm : ChainMemory state.mem chain initial)
    (htable : ∀ j, j < 80 → state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    (program kp).call (program.args (.value chain) (.value data) (.value 1#64)) state =
      .value (.nil, {alloc := ⟨state.alloc.nextFreeBlock + 1⟩, mem := feedforwardMemory state.mem chain (compressBlock initial (readBytes state.mem data 128))}) := by
  obtain ⟨middle, hw, hr⟩ := core_run_one kp chain data state initial hwf hc hd hk hm htable
  have hcall := Func.call_of_run hr
  have herase : middle.mem.eraseFrom state.alloc.nextFreeBlock = state.mem :=
    (hw.eraseFrom _ (Nat.le_refl _)).trans (coreEntry_frame state hwf)
  simpa only [feedforwardMemory, MemoryState.eraseFrom_storeAt, herase,
    hw.alloc, GlobalState.alloca] using hcall

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
