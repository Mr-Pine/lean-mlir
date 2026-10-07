import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairBody
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionGroupControl

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem pairBodyEnv_counters (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) :
    (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1).read (%270) =
      .value (BitVec.ofNat 64 (r+18)) ∧
    (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1).read (%191) =
      .value (BitVec.ofNat 64 (j+1)) := by
  constructor
  · simp [pairBodyEnv, pairStoreEnv, mlir_env]
  · unfold pairBodyEnv
    rw [(pairStoreEnv_frame _ _ _ _).read (%191),
      (pairSecondEnv_frame _ _ _ _).read (%191),
      (pairFirstEnv_frame _ _ _ _ _).read (%191)]
    simp [pairScheduleEnv, mlir_env]

theorem pairBodyEnv_next_ready (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (q : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word)
    (h : PairReady E scratch k r j q s) :
    PairReady (pairNextEnv (pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1))
      scratch k (r+2) (j+1) (avxWindowStep q) (pairSecondState (tailRound s kw0) kw1) := by
  let E' := pairBodyEnv E scratch k r j q s k0 k1 kw0 kw1
  have hf : PairBodyFrame E E' := pairBodyEnv_frame E scratch k r j q s k0 k1 kw0 kw1
  have hc := pairBodyEnv_counters E scratch k r j q s k0 k1 kw0 kw1
  change E'.read (%270) = _ ∧ E'.read (%191) = _ at hc
  have hs := pairNextEnv_scalar E' _ (pairBodyEnv_final_ready E scratch k r j q s k0 k1 kw0 kw1 h)
  have hw : PairWindowReady E' q := by
    constructor
    · exact (hf.read (%176)).trans h.window.p0
    · exact (hf.read (%175)).trans h.window.p1
    · exact (hf.read (%180)).trans h.window.p2
    · exact (hf.read (%181)).trans h.window.p3
    · exact (hf.read (%178)).trans h.window.p4
    · exact (hf.read (%177)).trans h.window.p5
    · exact (hf.read (%182)).trans h.window.p6
    · exact (hf.read (%179)).trans h.window.p7
  change PairReady (pairNextEnv E') _ _ _ _ _ _
  constructor
  · constructor
    · simp [pairNextEnv, mlir_env, hf.read (%24), h.schedule.constantPtr]
    · simp [pairNextEnv, mlir_env, hc.1, Nat.add_assoc]
    · simp [pairNextEnv, mlir_env, hc.2]
    · simp [pairNextEnv, mlir_env, hf.read (%1), h.schedule.one]
    · simp [pairNextEnv, mlir_env, hf.read (%25), h.schedule.c1]
    · simp [pairNextEnv, mlir_env, hf.read (%26), h.schedule.c7]
    · simp [pairNextEnv, mlir_env, hf.read (%27), h.schedule.c56]
    · simp [pairNextEnv, mlir_env, hf.read (%28), h.schedule.c8]
    · simp [pairNextEnv, mlir_env, hf.read (%29), h.schedule.c63]
    · simp [pairNextEnv, mlir_env, hf.read (%30), h.schedule.c6]
    · simp [pairNextEnv, mlir_env, hf.read (%31), h.schedule.c3]
    · simp [pairNextEnv, mlir_env, hf.read (%32), h.schedule.c19]
    · simp [pairNextEnv, mlir_env, hf.read (%33), h.schedule.c45]
    · simp [pairNextEnv, mlir_env, hf.read (%34), h.schedule.c61]
  · exact pairNextEnv_window E' q hw (pairBodyEnv_window_words E scratch k r j q s k0 k1 kw0 kw1)
  · rcases hs with ⟨ha, hb, hc', hd, he, hf', hg, hh⟩
    constructor
    · simp [pairNextEnv, mlir_env, hf.read (%81), h.scalar.scratchPtr]
    · simp [pairNextEnv, mlir_env, hc.2]
    · exact ha
    · exact hb
    · exact hc'
    · exact hd
    · exact he
    · exact hf'
    · exact hg
    · exact hh
    · simp [pairNextEnv, mlir_env, hf.read (%3), h.scalar.eight]
    · simp [pairNextEnv, mlir_env, hf.read (%35), h.scalar.shift]
    · simp [pairNextEnv, mlir_env, hf.read (%36), h.scalar.rot14]
    · simp [pairNextEnv, mlir_env, hf.read (%37), h.scalar.rot18]
    · simp [pairNextEnv, mlir_env, hf.read (%38), h.scalar.rot41]
    · simp [pairNextEnv, mlir_env, hf.read (%39), h.scalar.rot28]
    · simp [pairNextEnv, mlir_env, hf.read (%40), h.scalar.rot34]
    · simp [pairNextEnv, mlir_env, hf.read (%41), h.scalar.rot39]
  · simpa [pairNextEnv, mlir_env, hf.read (%42)] using h.two

set_option maxHeartbeats 4000000 in
theorem pair_group_reset_ready (E : Env program.Γ) (scratch k : Pointer)
    (r j b : Nat) (q : Window) (s : Spec.State)
    (h : PairReady (pairNextEnv E) scratch k r j q s)
    (hz : E.read (%2) = .value 0#64) :
    PairReady (groupPairEnv (groupNextEnv (groupBodyEnv E b))) scratch k r 0 q s := by
  constructor
  · constructor
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.constantPtr
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.nextIndex
    · simp [groupPairEnv, groupNextEnv, groupBodyEnv, mlir_env, hz]
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.one
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c1
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c7
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c56
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c8
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c63
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c6
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c3
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c19
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c45
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.schedule.c61
  · constructor
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p0
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p1
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p2
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p3
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p4
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p5
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p6
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.window.p7
  · constructor
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.scratchPtr
    · simp [groupPairEnv, groupNextEnv, groupBodyEnv, mlir_env, hz]
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.a
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.b
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.c
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.d
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.e
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.f
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.g
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.h
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.eight
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.shift
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.rot14
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.rot18
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.rot41
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.rot28
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.rot34
    · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.scalar.rot39
  · simpa [groupPairEnv, groupNextEnv, groupBodyEnv, pairNextEnv, mlir_env] using h.two

structure PairLoopConstants (E : Env program.Γ) : Prop where
  zero : E.read (%2) = .value 0#64
  tailStart : E.read (%15) = .value 64#64
  tailLimit : E.read (%17) = .value 80#64
  mask : E.read (%44) = .value 15#64

theorem PairLoopConstants.of_frame {E E' : Env program.Γ}
    (h : PairLoopConstants E) (hf : GroupFrame E E') : PairLoopConstants E' := by
  constructor
  · exact (hf.read (%2)).trans h.zero
  · exact (hf.read (%15)).trans h.tailStart
  · exact (hf.read (%17)).trans h.tailLimit
  · exact (hf.read (%44)).trans h.mask

theorem GroupReady.of_pair_frame {E E' : Env program.Γ} {b : Nat}
    (h : GroupReady E b) (hf : RegFrame 173 271 E E') : GroupReady E' b := by
  constructor
  · exact (hf.read (%156)).trans h.counter
  · exact (hf.read (%0)).trans h.one
  · exact (hf.read (%43)).trans h.limit

theorem pairNextEnv_frame (E : Env program.Γ) :
    RegFrame 173 190 E (pairNextEnv E) := by
  unfold pairNextEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem group_reset_frame (E : Env program.Γ) (b : Nat) :
    GroupFrame E (groupPairEnv (groupNextEnv (groupBodyEnv E b))) := by
  unfold groupPairEnv groupNextEnv groupBodyEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem group_reset_counter (E : Env program.Γ) (b : Nat) (h : GroupReady E b) :
    GroupReady (groupPairEnv (groupNextEnv (groupBodyEnv E b))) (b+1) := by
  constructor <;> simp [groupPairEnv, groupNextEnv, groupBodyEnv, mlir_env, h.one, h.limit]

end Agave.Ed25519.SHA512.Execution.Avx2
