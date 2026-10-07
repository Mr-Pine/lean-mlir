import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreFirstLoop

/-! Composition of the imported first and second scalar loops: exactly eighty
actual basic-block executions, preserving the enclosing registers and all
non-private memory. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem RingWrites.alloc {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) : b.alloc = a.alloc := by
  induction h with
  | refl => rfl
  | step h q r ih => exact ih
  | input h r native ih => exact ih

theorem RingWrites.wf {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (ha : a.WF) : b.WF := by
  induction h with
  | refl => exact ha
  | step h q r ih => exact ih.storeAt
  | input h r native ih => exact ih.storeAt

theorem RingWrites.smallRange {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) {p : Pointer} {bytes : Nat} (hp : SmallRange a.mem p bytes) :
    SmallRange b.mem p bytes := by
  induction h with
  | refl => exact hp
  | step h q r ih => exact ih.storeAt _ _
  | input h r native ih => exact ih.storeAt _ _

theorem RingWrites.eraseFrom {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (mark : Nat) (hm : mark ≤ stack.id.id) :
    b.mem.eraseFrom mark = a.mem.eraseFrom mark := by
  induction h with
  | refl => rfl
  | step h q r ih =>
    rw [scheduleMemory, MemoryState.eraseFrom_storeAt,
      MemoryState.storeAt_eraseFrom_of_le (show mark ≤
        (stack.add (BitVec.ofNat 64 (8 * (r % 16)))).id.id from hm)]
    exact ih
  | input h r native ih =>
    rw [inputMemory, MemoryState.eraseFrom_storeAt,
      MemoryState.storeAt_eraseFrom_of_le (show mark ≤
        (stack.add (BitVec.ofNat 64 (8 * r))).id.id from hm)]
    exact ih

theorem RingWrites.readBytes {stack : Pointer} {a b : GlobalState}
    (h : RingWrites stack a b) (p : Pointer) (bytes : Nat) (hp : SmallRange a.mem p bytes)
    (hne : stack.id ≠ p.id) : readBytes b.mem p bytes = readBytes a.mem p bytes := by
  induction h with
  | refl => rfl
  | @step middle h q r ih =>
    have hd : (Range.of (stack.add (BitVec.ofNat 64 (8 * (r % 16)))) 64).Disjoint
        (Range.of p (8 * bytes)) := Or.inl hne
    rw [scheduleMemory, readBytes_storeAt_disjoint _ _ _ _ _ (h.smallRange hp) hd]
    exact ih
  | @input middle h r native ih =>
    have hd : (Range.of (stack.add (BitVec.ofNat 64 (8 * r))) 64).Disjoint
        (Range.of p (8 * bytes)) := Or.inl hne
    rw [inputMemory, readBytes_storeAt_disjoint _ _ _ _ _ (h.smallRange hp) hd]
    exact ih

/-- A finite witness for both actual round loops, not just equality of possibly
undefined whole-program outcomes. -/
def EightyTrace (E : Env program.Γ) (before : GlobalState)
    (F : Env program.Γ) (after : GlobalState) : Prop :=
  ∃ middleEnv middleState, FirstTrace 16 E before middleEnv middleState ∧
    LaterTrace 64 middleEnv middleState F after

theorem EightyTrace.runFrom {E F : Env program.Γ} {before after : GlobalState}
    (h : EightyTrace E before F after) (kp : Pointer) :
    (program kp).runFrom E 2 before = (program kp).runFrom F 4 after := by
  obtain ⟨M, middle, first, later⟩ := h
  exact (first.runFrom kp).trans (later.runFrom kp)

theorem EightyTrace.evalFrom {E F : Env program.Γ} {before after : GlobalState}
    (h : EightyTrace E before F after) (kp : Pointer) (fuel : Nat) :
    (program kp).evalFrom (80 + fuel) E 2 before = (program kp).evalFrom fuel F 4 after := by
  obtain ⟨M, middle, first, later⟩ := h
  rw [show 80 + fuel = 16 + (64 + fuel) by omega, first.evalFrom kp, later.evalFrom kp]

/-- Exact machine rounds refine the standard working state and initialize then
update the real sixteen-word schedule allocation. -/
theorem eighty_rounds (block : Bytes) (stack data kp : Pointer) (E : Env program.Γ)
    (before : GlobalState) (initial : State)
    (h : FirstLoopReady E stack data kp 0 initial)
    (hm : FirstMemory before.mem stack data kp block 0) :
    ∃ F after q', EightyTrace E before F after ∧
      FinalReady F (roundsFrom initial (schedule block) 0 80) ∧
      LaterMemory after.mem stack kp q' ∧ RingRepresents q' block 80 ∧
      RingWrites stack before after ∧ LoopFrame E F := by
  obtain ⟨M, middle, ht1, hr1, hm1, hw1, hf1⟩ :=
    first_suffix block stack data kp 15 0 (by decide) E before initial h hm
  obtain ⟨F, after, q', ht2, hr2, hm2, hq2, hw2, hf2⟩ :=
    later_sixtyfour block stack kp M middle initial hr1 hm1.complete
  exact ⟨F, after, q', ⟨M, middle, ht1, ht2⟩, hr2, hm2, hq2,
    hw1.trans hw2, hf1.trans hf2⟩

/-- Convenient byte-memory interface at bb2. No instruction or whole-program
execution equation occurs among the hypotheses. -/
theorem eighty_from_input (stack data kp : Pointer) (E : Env program.Γ)
    (before : GlobalState) (initial : State)
    (h : FirstLoopReady E stack data kp 0 initial)
    (hs : SmallRange before.mem stack 128) (hd : SmallRange before.mem data 128)
    (hk : SmallRange before.mem kp 640) (hne : stack.id ≠ kp.id) (hnd : stack.id ≠ data.id)
    (hread : ∀ j, j < 80 → before.mem.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
      constants.toList.getD j 0) :
    ∃ F after, EightyTrace E before F after ∧
      FinalReady F (roundsFrom initial (schedule (readBytes before.mem data 128)) 0 80) ∧
      RingWrites stack before after ∧ LoopFrame E F := by
  obtain ⟨F, after, q', ht, hf, _, _, hw, he⟩ :=
    eighty_rounds (readBytes before.mem data 128) stack data kp E before initial h
      ⟨hs, hd, hk, hne, hnd, initialRingMemory_zero _ _ _, hread, rfl⟩
  exact ⟨F, after, ht, hf, hw, he⟩

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
