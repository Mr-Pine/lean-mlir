import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreControl
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCoreRingMemory

/-! Actual finite walks through the imported SHA core's two round loops. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
  (Ring RingRepresents ringWord ringStep initialRing initialRing_represents
   ringWord_spec ringStep_represents)
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

private theorem roundsFrom_head (s : State) (words : List Word) (r n : Nat) :
    roundsFrom s words r (n+1) =
      roundsFrom (Spec.round s (words.getD r 0) (constants.toList.getD r 0)) words (r+1) n := by
  simpa only [Nat.add_comm 1 n, roundsFrom, Nat.add_zero] using roundsFrom_add s words r 1 n

/-- Every nonempty suffix of the second loop reaches the feedforward block
with the standard working state and changes only the private ring allocation. -/
theorem later_suffix (kp chain stack originalData data : Pointer)
    (originalCount count : Word) (original initial : State) (block : Bytes) (n : Nat) :
    ∀ (r : Nat), 16 ≤ r → r+n=79 →
    ∀ (before : GlobalState) (q : Ring) (work : State),
    LaterMemory before.mem stack kp q → RingRepresents q block r →
    ∃ after q',
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (laterTarget initial work data count r)) before =
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (feedforwardTarget initial (roundsFrom work (schedule block) r (n+1)) data count)) after ∧
      LaterMemory after.mem stack kp q' ∧ RingRepresents q' block 80 ∧
      RingWrites stack before after := by
  induction n with
  | zero =>
    intro r hlo hend before q work hm hq
    have hr : r=79 := by omega
    subst r
    refine ⟨{before with mem := scheduleMemory before.mem stack q 79}, ringStep q 79,
      ?_, hm.step 79, ringStep_represents q block 79 hq (by decide) (by decide),
      .step (.refl before) q 79⟩
    rw [later_run kp chain stack originalData data originalCount count original initial work
      q 79 _ before (by decide) hm.liveStack hm.liveConstants hm.distinct hm.ring (hm.table 79 (by decide)),
      laterNext_last, ringWord_spec q block 79 hq (by decide) (by decide)]
    rfl
  | succ n ih =>
    intro r hlo hend before q work hm hq
    have hr : r < 79 := by omega
    let w := Spec.round work ((schedule block).getD r 0) (constants.toList.getD r 0)
    let middle : GlobalState := {before with mem := scheduleMemory before.mem stack q r}
    obtain ⟨after, q', hrun, hmem, hring, hw⟩ := ih (r+1) (by omega) (by omega)
      middle (ringStep q r) w (hm.step r) (ringStep_represents q block r hq hlo (by omega))
    refine ⟨after, q', ?_, hmem, hring, (RingWrites.step (.refl before) q r).trans hw⟩
    rw [later_run kp chain stack originalData data originalCount count original initial work
      q r _ before (by omega) hm.liveStack hm.liveConstants hm.distinct hm.ring (hm.table r (by omega)),
      laterNext_spec, ite_eq_right (by omega : r+1 ≠ 80), ringWord_spec q block r hq hlo (by omega)]
    rw [roundsFrom_head]
    exact hrun

structure FirstMemory (m : MemoryState) (stack data kp : Pointer) (block : Bytes) (r : Nat) : Prop where
  liveStack : SmallRange m stack 128
  liveData : SmallRange m data 128
  liveConstants : SmallRange m kp 640
  distinct : stack.id ≠ kp.id
  dataDistinct : stack.id ≠ data.id
  ring : InitialRingMemory m stack block r
  table : ∀ j, j < 80 → readBits m (kp.withOffset (BitVec.ofNat 64 (8*j))) 64 = constants.toList.getD j 0
  bytes : readBytes m data 128 = block

theorem FirstMemory.word {m : MemoryState} {stack data kp : Pointer} {block : Bytes} {r : Nat}
    (h : FirstMemory m stack data kp block r) (hr : r < 16) :
    bswapBV (readBits m (data.withOffset (BitVec.ofNat 64 (8*r))) 64) = (schedule block).getD r 0 := by
  change swapBytes _ = _
  rw [input_swap_eq m data r h.liveData hr, h.bytes, schedule_initial block r hr]

theorem FirstMemory.step {m : MemoryState} {stack data kp : Pointer} {block : Bytes} {r : Nat}
    (h : FirstMemory m stack data kp block r) (hr : r < 16) :
    FirstMemory (inputMemory m stack r (readBits m (data.withOffset (BitVec.ofNat 64 (8*r))) 64))
      stack data kp block (r+1) := by
  refine ⟨h.liveStack.splice _ _, h.liveData.splice _ _, h.liveConstants.splice _ _,
    h.distinct, h.dataDistinct, ?_, ?_, ?_⟩
  · apply inputMemory_initial_step m stack block r _ hr h.liveStack h.ring
    rw [input_swap_eq m data r h.liveData hr, h.bytes]
  · intro j hj
    rw [inputMemory, readBits_splice_ne (p := kp.withOffset (BitVec.ofNat 64 (8*j)))
      (q := stack.withOffset (BitVec.ofNat 64 (8*r))) _ h.distinct]
    exact h.table j hj
  · rw [inputMemory_preserves_data m stack data r _ h.dataDistinct, h.bytes]

theorem FirstMemory.complete {m : MemoryState} {stack data kp : Pointer} {block : Bytes}
    (h : FirstMemory m stack data kp block 16) : LaterMemory m stack kp (initialRing block) :=
  ⟨h.liveStack, h.liveConstants, h.distinct, initialRingMemory_full m stack block h.ring, h.table⟩

/-- Every nonempty suffix of the first loop reaches round sixteen with the
standard working state and a completely initialized circular schedule. -/
theorem first_suffix (kp chain stack originalData data : Pointer)
    (originalCount count : Word) (original initial : State) (block : Bytes) (n : Nat) :
    ∀ (r : Nat), r+n=15 → ∀ (before : GlobalState) (work : State),
    FirstMemory before.mem stack data kp block r →
    ∃ after,
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (firstTarget initial work data count r)) before =
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (laterTarget initial (roundsFrom work (schedule block) r (n+1)) data count 16)) after ∧
      LaterMemory after.mem stack kp (initialRing block) ∧ RingWrites stack before after := by
  induction n with
  | zero =>
    intro r hend before work hm
    have hr : r=15 := by omega
    subst r
    let native := readBits before.mem (data.withOffset (BitVec.ofNat 64 (8*15))) 64
    refine ⟨{before with mem := inputMemory before.mem stack 15 native}, ?_,
      (hm.step (by decide)).complete, .input (.refl before) 15 native⟩
    rw [first_run kp chain stack originalData data originalCount count original initial work
      15 native _ before (by decide) hm.liveData hm.liveStack hm.liveConstants hm.distinct rfl
      (hm.table 15 (by decide)), firstNext_exit, hm.word (by decide)]
    rfl
  | succ n ih =>
    intro r hend before work hm
    have hr : r < 15 := by omega
    let native := readBits before.mem (data.withOffset (BitVec.ofNat 64 (8*r))) 64
    let w := Spec.round work ((schedule block).getD r 0) (constants.toList.getD r 0)
    let middle : GlobalState := {before with mem := inputMemory before.mem stack r native}
    obtain ⟨after, hrun, hmem, hw⟩ := ih (r+1) (by omega) middle w (hm.step (by omega))
    refine ⟨after, ?_, hmem, (RingWrites.input (.refl before) r native).trans hw⟩
    rw [first_run kp chain stack originalData data originalCount count original initial work
      r native _ before (by omega) hm.liveData hm.liveStack hm.liveConstants hm.distinct rfl
      (hm.table r (by omega)), firstNext_continue _ _ _ _ _ _ _ (by omega), hm.word (by omega)]
    rw [roundsFrom_head]
    exact hrun

/-- The complete actual eighty-round control-flow walk. -/
theorem eighty_rounds (kp chain stack originalData data : Pointer)
    (originalCount count : Word) (original initial : State) (block : Bytes) (before : GlobalState)
    (hm : FirstMemory before.mem stack data kp block 0) :
    ∃ after,
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (outerTarget initial data count)) before =
      StateT.run (core.cfgBlocks.run (ambient kp chain stack originalData originalCount original)
        (feedforwardTarget initial (roundsFrom initial (schedule block) 0 80) data count)) after ∧
      RingWrites stack before after := by
  obtain ⟨middle, hfirst, hm', hwfirst⟩ := first_suffix kp chain stack originalData data originalCount count
    original initial block 15 0 (by decide) before initial hm
  obtain ⟨after, q', hlater, hmem, hring, hwlater⟩ := later_suffix kp chain stack originalData data originalCount count
    original initial block 63 16 (by decide) (by decide) middle (initialRing block)
    (roundsFrom initial (schedule block) 0 16) hm' (initialRing_represents block)
  refine ⟨after, ?_, hwfirst.trans hwlater⟩
  rw [outer_run, hfirst, hlater]
  rw [← roundsFrom_add]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
