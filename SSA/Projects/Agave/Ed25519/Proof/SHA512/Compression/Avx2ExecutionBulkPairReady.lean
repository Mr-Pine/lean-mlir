import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairBody

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

theorem bulkPairBodyEnv_counters (E : Env program.Γ) (scratch cacheGroup k : Pointer)
    (r j : Nat) (q u : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word) :
    (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1).read (%571) =
      .value (BitVec.ofNat 64 (r+18)) ∧
    (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1).read (%488) =
      .value (BitVec.ofNat 64 (j+1)) := by
  constructor
  · simp [bulkPairBodyEnv, bulkPairStoreEnv, mlir_env]
  · unfold bulkPairBodyEnv
    rw [(bulkPairStoreEnv_frame _ _ _ _ _ _ _ _ _).read (%488),
      (bulkPairSecondEnv_frame _ _ _ _).read (%488),
      (bulkPairFirstEnv_frame _ _ _ _ _).read (%488)]
    simp [bulkPairScheduleEnv, mlir_env]

theorem bulkPairBodyEnv_next_ready (E : Env program.Γ) (scratch cacheGroup k : Pointer)
    (r j : Nat) (q u : Window) (s : Spec.State) (k0 k1 kw0 kw1 : Word)
    (h : BulkPairReady E scratch cacheGroup k r j q u s) :
    BulkPairReady (bulkPairNextEnv (bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1))
      scratch cacheGroup k (r+2) (j+1) (avxWindowStep q) (avxWindowStep u)
        (pairSecondState (tailRound s kw0) kw1) := by
  let E' := bulkPairBodyEnv E scratch cacheGroup k r j q u s k0 k1 kw0 kw1
  have hf : BulkPairBodyFrame E E' := bulkPairBodyEnv_frame E scratch cacheGroup k r j q u s k0 k1 kw0 kw1
  have hc := bulkPairBodyEnv_counters E scratch cacheGroup k r j q u s k0 k1 kw0 kw1
  change E'.read (%571) = _ ∧ E'.read (%488) = _ at hc
  have hs := bulkPairNextEnv_scalar E' _
    (bulkPairBodyEnv_final_ready E scratch cacheGroup k r j q u s k0 k1 kw0 kw1 h)
  have hw : BulkPairWindowReady E' q u := by
    constructor
    · exact (hf.read (%473)).trans h.window.p0
    · exact (hf.read (%472)).trans h.window.p1
    · exact (hf.read (%477)).trans h.window.p2
    · exact (hf.read (%478)).trans h.window.p3
    · exact (hf.read (%475)).trans h.window.p4
    · exact (hf.read (%474)).trans h.window.p5
    · exact (hf.read (%479)).trans h.window.p6
    · exact (hf.read (%476)).trans h.window.p7
  change BulkPairReady (bulkPairNextEnv E') _ _ _ _ _ _ _ _
  constructor
  · constructor
    · simp [bulkPairNextEnv, mlir_env, hf.read (%24), h.schedule.constantPtr]
    · simp [bulkPairNextEnv, mlir_env, hc.1, Nat.add_assoc]
    · simp [bulkPairNextEnv, mlir_env, hc.2]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%1), h.schedule.one]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%68), h.schedule.c1]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%69), h.schedule.c7]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%70), h.schedule.c56]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%71), h.schedule.c8]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%72), h.schedule.c63]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%73), h.schedule.c6]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%74), h.schedule.c3]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%75), h.schedule.c19]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%76), h.schedule.c45]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%77), h.schedule.c61]
  · exact bulkPairNextEnv_window E' q u hw
      (bulkPairBodyEnv_window_words E scratch cacheGroup k r j q u s k0 k1 kw0 kw1)
  · rcases hs with ⟨ha, hb, hc', hd, he, hf', hg, hh⟩
    constructor
    · simp [bulkPairNextEnv, mlir_env, hf.read (%83), h.scalar.scratchPtr]
    · simp [bulkPairNextEnv, mlir_env, hc.2]
    · exact ha
    · exact hb
    · exact hc'
    · exact hd
    · exact he
    · exact hf'
    · exact hg
    · exact hh
    · simp [bulkPairNextEnv, mlir_env, hf.read (%3), h.scalar.eight]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%35), h.scalar.shift]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%36), h.scalar.rot14]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%37), h.scalar.rot18]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%38), h.scalar.rot41]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%39), h.scalar.rot28]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%40), h.scalar.rot34]
    · simp [bulkPairNextEnv, mlir_env, hf.read (%41), h.scalar.rot39]
  · simpa [bulkPairNextEnv, mlir_env, hf.read (%42)] using h.two
  · simpa [bulkPairNextEnv, mlir_env, hf.read (%469)] using h.cachePtr

theorem bulkPairNextEnv_frame (E : Env program.Γ) :
    RegFrame 470 487 E (bulkPairNextEnv E) := by
  unfold bulkPairNextEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem BulkGroupReady.of_pair_frame {E E' : Env program.Γ} {g : Nat}
    (h : BulkGroupReady E g) (hf : RegFrame 470 572 E E') : BulkGroupReady E' g := by
  constructor
  · exact (hf.read (%451)).trans h.counter
  · exact (hf.read (%1)).trans h.one
  · exact (hf.read (%78)).trans h.limit

/-- The last pair's scalar state is readable before the bb10 group backedge. -/
theorem BulkPairReady.final_of_next {E : Env program.Γ} {scratch cacheGroup k : Pointer}
    {r j : Nat} {q u : Window} {s : Spec.State}
    (h : BulkPairReady (bulkPairNextEnv E) scratch cacheGroup k r j q u s) :
    BulkPairSecondFinalReady E s := by
  constructor
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.a
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.b
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.c
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.d
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.e
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.f
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.g
  · simpa [bulkPairNextEnv, mlir_env] using h.scalar.h

end Agave.Ed25519.SHA512.Execution.Avx2
