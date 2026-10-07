import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairControl

/-! Composition of the exact 82-instruction bb5 body, with independent
memory reads and register frames rather than backend-result assumptions. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure PairReady (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) : Prop where
  schedule : PairScheduleReady E k r j
  window : PairWindowReady E q
  scalar : PairFirstReady E scratch j s
  two : E.read (%42) = .value 2#64

def pairBodyEnv (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) : Env program.Γ :=
  pairStoreEnv (pairSecondEnv
    (pairFirstEnv (pairScheduleEnv E k r j q k0 k1) scratch j s kw0)
    (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw0) kw1) scratch r j

def pairBodyState (mem : GlobalState) (scratch : Pointer) (j : Nat)
    (q : Window) (k0 k1 : Word) : GlobalState :=
  pairStoreState mem scratch j ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1)

theorem pair_range (mem : MemoryState) (scratch : Pointer) (j : Nat)
    (h : SmallRange mem scratch 128) (hj : j < 8) :
    SmallRange mem (scratch.add (BitVec.ofNat 64 (16*j))) 16 := by
  have hn := h.no_wrap (k := 16*j) (by omega)
  have hk64 : 16*j < 2^64 := by omega
  obtain ⟨b, hb, hsmall, hsize⟩ := h
  refine ⟨b, hb, hsmall, ?_⟩
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  omega

/-- Execute the four proven source slices in their actual imported order. -/
theorem pair_body (E : Env program.Γ) (mem : GlobalState)
    (scratch k : Pointer) (r j : Nat) (q : Window) (s : Spec.State)
    (k0 k1 kw0 kw1 : Word) (hr : r+1<64) (hj : j<8)
    (h : PairReady E scratch k r j q s)
    (hs : SmallRange mem.mem scratch 128) (hk : SmallRange mem.mem k 640)
    (hkread : mem.mem.readAt (k.add (BitVec.ofNat 64 (8*(r+16)))) 128 = k1 ++ k0)
    (hread0 : mem.mem.readAt (scratch.add (BitVec.ofNat 64 (16*j))) 64 = kw0)
    (hread1 : mem.mem.readAt ((scratch.add (BitVec.ofNat 64 (16*j))).add 8#64) 64 = kw1) :
    List.foldlM Instr.run E program.bb5.body mem =
      .value (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1,
        pairBodyState mem scratch j q k0 k1) := by
  let E1 := pairScheduleEnv E k r j q k0 k1
  let E2 := pairFirstEnv E1 scratch j s kw0
  let E3 := pairSecondEnv E2 (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw0) kw1
  have hf1 := pairScheduleEnv_frame E k r j q k0 k1
  have hf2 := pairFirstEnv_frame E1 scratch j s kw0
  have hf3 := pairSecondEnv_frame E2 (scratch.add (BitVec.ofNat 64 (16*j))) (tailRound s kw0) kw1
  have hf23 : RegFrame 218 268 E1 E3 :=
    (hf2.enlarge (by decide) (by decide)).trans (hf3.enlarge (by decide) (by decide))
  have hf123 : RegFrame 191 268 E E3 :=
    (hf1.enlarge (by decide) (by decide)).trans (hf23.enlarge (by decide) (by decide))
  have h1 := h.scalar.of_frame hf1
  have h2 := pairFirstEnv_second_ready E1 scratch j s kw0 h1
  have hstore : PairStoreReady E3 scratch r j
      ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1) := by
    constructor
    · exact (hf123.read (%81)).trans h.scalar.scratchPtr
    · exact (hf123.read (%174)).trans h.scalar.slot
    · exact (hf123.read (%173)).trans h.schedule.nextIndex
    · rw [hf23.read (%191)]; simp [E1, pairScheduleEnv, mlir_env]
    · exact (hf23.read (%217)).trans (pairScheduleEnv_words E k r j q k0 k1).2
    · exact (hf123.read (%42)).trans h.two
    · exact (hf123.read (%3)).trans h.scalar.eight
  have hprefix := pair_schedule_prefix E mem k r j q k0 k1 hr hj h.schedule h.window hk hkread
  have hfirst := pair_first_body E1 mem scratch j s kw0 hj h1 hs hread0
  have hsecond := pair_second_body E2 mem (scratch.add (BitVec.ofNat 64 (16*j)))
    (tailRound s kw0) kw1 h2 (pair_range mem.mem scratch j hs hj) hread1
  have hlast := pair_store_body E3 mem scratch r j
    ((avxWindowPair q).1+k0) ((avxWindowPair q).2+k1) hj hstore hs
  dsimp only [E1, E2, E3] at hfirst hsecond hlast
  have hcut : program.bb5.body =
      program.bb5.body.take 27 ++ (program.bb5.body.drop 27).take 26 ++
        (program.bb5.body.drop 53).take 25 ++ (program.bb5.body.drop 78).take 4 := by rfl
  rw [hcut, List.foldlM_append, List.foldlM_append, List.foldlM_append]
  simp only [EffectM.bind_eq, hprefix, PoisonOr.value_bind, hfirst, hsecond, hlast]
  rfl

theorem pairBodyEnv_frame (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) :
    PairBodyFrame E (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1) := by
  unfold pairBodyEnv
  apply RegFrame.trans (RegFrame.trans (RegFrame.trans
    ((pairScheduleEnv_frame _ _ _ _ _ _ _).enlarge (by decide) (by decide))
    ((pairFirstEnv_frame _ _ _ _ _).enlarge (by decide) (by decide)))
    ((pairSecondEnv_frame _ _ _ _).enlarge (by decide) (by decide)))
  exact (pairStoreEnv_frame _ _ _ _).enlarge (by decide) (by decide)

theorem pairBodyEnv_final_ready (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word)
    (h : PairReady E scratch k r j q s) :
    PairSecondFinalReady (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1)
      (pairSecondState (tailRound s kw0) kw1) := by
  have h1 := h.scalar.of_frame (pairScheduleEnv_frame E k r j q k0 k1)
  have h2 := pairFirstEnv_second_ready _ scratch j s kw0 h1
  exact (pairSecondEnv_final_ready _ _ _ kw1 h2).of_frame (pairStoreEnv_frame _ _ _ _)

/-- The schedule word survives both scalar rounds and the scratch store. -/
theorem pairBodyEnv_window_words (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) :
    (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1).read (%216) =
      pairVec (avxWindowPair q).1 (avxWindowPair q).2 := by
  unfold pairBodyEnv
  rw [(pairStoreEnv_frame _ _ _ _).read (%216),
    (pairSecondEnv_frame _ _ _ _).read (%216),
    (pairFirstEnv_frame _ _ _ _ _).read (%216)]
  exact (pairScheduleEnv_words _ _ _ _ _ _ _).1

end Agave.Ed25519.SHA512.Execution.Avx2
