import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairControl
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairBody

/-! Composition of all 87 imported bb12 instructions from independent
register, range, and read obligations. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

structure BulkPairReady (E : Env program.Γ) (scratch cacheGroup k : Pointer) (r j : Nat)
    (q u : Window) (s : Spec.State) : Prop where
  schedule : BulkPairScheduleReady E k r j
  window : BulkPairWindowReady E q u
  scalar : BulkPairFirstReady E scratch j s
  two : E.read (%42) = .value 2#64
  cachePtr : E.read (%469) = .value cacheGroup

def bulkPairBodyEnv (E : Env program.Γ) (scratch cacheGroup k : Pointer) (r j : Nat)
    (q u : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) : Env program.Γ :=
  bulkPairStoreEnv (bulkPairSecondEnv
    (bulkPairFirstEnv (bulkPairScheduleEnv E k r j q u k0 k1) scratch j s kw0)
    (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw0) kw1)
    scratch cacheGroup r j ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1)
      ((avxWindowPair u).1+k0) ((avxWindowPair u).2+k1)

def bulkPairBodyState (mem : GlobalState) (scratch cacheGroup : Pointer) (j : Nat)
    (q u : Window) (k0 k1 : Word) : GlobalState :=
  bulkPairStoreState mem scratch cacheGroup j
    ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1)
    ((avxWindowPair u).1+k0) ((avxWindowPair u).2+k1)

/-- Concrete execution, including both memory writes and every instruction flag. -/
theorem bulk_pair_body (E : Env program.Γ) (mem : GlobalState)
    (scratch cacheGroup k : Pointer) (r j : Nat) (q u : Window) (s : Spec.State)
    (k0 k1 kw0 kw1 : Word) (hr : r+1<64) (hj : j<8)
    (h : BulkPairReady E scratch cacheGroup k r j q u s)
    (hs : SmallRange mem.mem scratch 128) (hc : SmallRange mem.mem cacheGroup 128)
    (hk : SmallRange mem.mem k 640)
    (hkread : mem.mem.readAt (k.add (BitVec.ofNat 64 (8*(r+16)))) 128 = k1 ++ k0)
    (hread0 : mem.mem.readAt (scratch.add (BitVec.ofNat 64 (16*j))) 64 = kw0)
    (hread1 : mem.mem.readAt ((scratch.add (BitVec.ofNat 64 (16*j))).add 8#64) 64 = kw1) :
    List.foldlM Instr.run E program.bb12.body mem =
      .value (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1,
        bulkPairBodyState mem scratch cacheGroup j q u k0 k1) := by
  let E1 := bulkPairScheduleEnv E k r j q u k0 k1
  let E2 := bulkPairFirstEnv E1 scratch j s kw0
  let E3 := bulkPairSecondEnv E2 (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw0) kw1
  have hf1 := bulkPairScheduleEnv_frame E k r j q u k0 k1
  have hf2 := bulkPairFirstEnv_frame E1 scratch j s kw0
  have hf3 := bulkPairSecondEnv_frame E2 (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw0) kw1
  have hf23 : RegFrame 516 566 E1 E3 :=
    (hf2.enlarge (by decide) (by decide)).trans (hf3.enlarge (by decide) (by decide))
  have hf123 : RegFrame 488 566 E E3 :=
    (hf1.enlarge (by decide) (by decide)).trans (hf23.enlarge (by decide) (by decide))
  have h1 := h.scalar.of_frame hf1
  have h2 := bulkPairFirstEnv_second_ready E1 scratch j s kw0 h1
  have hstore : BulkPairStoreReady E3 scratch cacheGroup r j
      ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1)
      ((avxWindowPair u).1+k0) ((avxWindowPair u).2+k1) := by
    constructor
    · exact (hf123.read (%83)).trans h.scalar.scratchPtr
    · exact (hf123.read (%469)).trans h.cachePtr
    · exact (hf123.read (%471)).trans h.scalar.slot
    · exact (hf123.read (%470)).trans h.schedule.nextIndex
    · rw [hf23.read (%488)]; simp [E1, bulkPairScheduleEnv, mlir_env]
    · exact (hf23.read (%515)).trans (bulkPairScheduleEnv_words E k r j q u k0 k1).2
    · exact (hf123.read (%42)).trans h.two
    · exact (hf123.read (%3)).trans h.scalar.eight
  have hprefix := bulk_pair_schedule_prefix E mem k r j q u k0 k1 hr hj h.schedule h.window hk hkread
  have hfirst := bulk_pair_first_body E1 mem scratch j s kw0 hj h1 hs hread0
  have hsecond := bulk_pair_second_body E2 mem (scratch.add (BitVec.ofNat 64 (16*j)))
    (tailRound s kw0) kw1 h2 (pair_range mem.mem scratch j hs hj) hread1
  have hlast := bulk_pair_store_body E3 mem scratch cacheGroup r j
    ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1)
    ((avxWindowPair u).1+k0) ((avxWindowPair u).2+k1) hj hstore hs hc
  dsimp only [E1, E2, E3] at hfirst hsecond hlast
  have hcut : program.bb12.body =
      program.bb12.body.take 28 ++ (program.bb12.body.drop 28).take 26 ++
        (program.bb12.body.drop 54).take 25 ++ (program.bb12.body.drop 79).take 8 := by rfl
  rw [hcut, List.foldlM_append, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, hprefix, PoisonOr.value_bind, hfirst, hsecond, hlast]
  rfl

theorem bulkPairBodyEnv_frame (E : Env program.Γ) (scratch cacheGroup k : Pointer)
    (r j : Nat) (q u : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) :
    BulkPairBodyFrame E (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1) := by
  unfold bulkPairBodyEnv
  apply RegFrame.trans (RegFrame.trans (RegFrame.trans
    ((bulkPairScheduleEnv_frame _ _ _ _ _ _ _ _).enlarge (by decide) (by decide))
    ((bulkPairFirstEnv_frame _ _ _ _ _).enlarge (by decide) (by decide)))
    ((bulkPairSecondEnv_frame _ _ _ _).enlarge (by decide) (by decide)))
  exact (bulkPairStoreEnv_frame _ _ _ _ _ _ _ _ _).enlarge (by decide) (by decide)

theorem bulkPairBodyEnv_final_ready (E : Env program.Γ) (scratch cacheGroup k : Pointer)
    (r j : Nat) (q u : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word)
    (h : BulkPairReady E scratch cacheGroup k r j q u s) :
    BulkPairSecondFinalReady (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1)
      (pairSecondState (tailRound s kw0) kw1) := by
  have h1 := h.scalar.of_frame (bulkPairScheduleEnv_frame E k r j q u k0 k1)
  have h2 := bulkPairFirstEnv_second_ready _ scratch j s kw0 h1
  exact (bulkPairSecondEnv_final_ready _ _ _ kw1 h2).of_frame
    (bulkPairStoreEnv_frame _ _ _ _ _ _ _ _ _)

theorem bulkPairBodyEnv_window_words (E : Env program.Γ) (scratch cacheGroup k : Pointer)
    (r j : Nat) (q u : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) :
    (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1).read (%514) =
      bulkPairVec (avxWindowPair q) (avxWindowPair u) := by
  unfold bulkPairBodyEnv
  rw [(bulkPairStoreEnv_frame _ _ _ _ _ _ _ _ _).read (%514),
    (bulkPairSecondEnv_frame _ _ _ _).read (%514),
    (bulkPairFirstEnv_frame _ _ _ _ _).read (%514)]
  exact (bulkPairScheduleEnv_words _ _ _ _ _ _ _ _).1

end Agave.Ed25519.SHA512.Execution.Avx2
