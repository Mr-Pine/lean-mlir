import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStep
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTrace
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionScratchFrame

/-! Eight concrete bb5 iterations consume one group of sixteen rounds. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem pairSpecEnv_next_ready (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (block : Bytes) (s : Spec.State) (hr : r+1<64)
    (h : PairReady E scratch k r j (specWindow block r) s) :
    PairReady (pairNextEnv (pairSpecEnv E scratch k r j block s)) scratch k (r+2) (j+1)
      (specWindow block (r+2)) (roundsFrom s (schedule block) r 2) := by
  have hh := pairBodyEnv_next_ready E scratch k r j (specWindow block r) s
    (constants.toList.getD (r+16) 0) (constants.toList.getD (r+17) 0)
    (scheduleKW (schedule block) r) (scheduleKW (schedule block) (r+1)) h
  rw [pair_rounds_eq, avxWindowStep_spec block r hr] at hh
  exact hh

theorem pairSpecEnv_frame (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (block : Bytes) (s : Spec.State) :
    RegFrame 191 271 E (pairSpecEnv E scratch k r j block s) :=
  pairBodyEnv_frame _ _ _ _ _ _ _ _ _ _ _

theorem pairSpecNext_frame (E : Env program.Γ) (scratch k : Pointer) (r j : Nat)
    (block : Bytes) (s : Spec.State) :
    RegFrame 173 271 E (pairNextEnv (pairSpecEnv E scratch k r j block s)) :=
  ((pairSpecEnv_frame _ _ _ _ _ _ _).enlarge (by decide) (by decide)).trans
    ((pairNextEnv_frame _).enlarge (by decide) (by decide))

/-- Read the scalar result directly at the unparameterized bb3 group boundary. -/
theorem PairReady.final_of_next {E : Env program.Γ} {scratch k : Pointer}
    {r j : Nat} {q : Window} {s : Spec.State}
    (h : PairReady (pairNextEnv E) scratch k r j q s) : PairSecondFinalReady E s := by
  constructor
  · simpa [pairNextEnv, mlir_env] using h.scalar.a
  · simpa [pairNextEnv, mlir_env] using h.scalar.b
  · simpa [pairNextEnv, mlir_env] using h.scalar.c
  · simpa [pairNextEnv, mlir_env] using h.scalar.d
  · simpa [pairNextEnv, mlir_env] using h.scalar.e
  · simpa [pairNextEnv, mlir_env] using h.scalar.f
  · simpa [pairNextEnv, mlir_env] using h.scalar.g
  · simpa [pairNextEnv, mlir_env] using h.scalar.h

/-- A suffix of a group executes exactly n+1 pair blocks, ending at bb3. -/
theorem pair_group_suffix (g : Globals) (scratch k : Pointer) (block : Bytes)
    (b : Nat) (hb : b<4)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) (n : Nat) :
    ∀ (j : Nat), j+n=7 → ∀ (E : Env program.Γ) (mem : GlobalState) (s : Spec.State),
      PairReady E scratch k (16*b+2*j) j (specWindow block (16*b+2*j)) s →
      PairScratch mem.mem scratch (schedule block) b j → PairConstants mem.mem k →
      ∃ E' mem', ExecTrace (program g) (n+1) E 5 mem E' 3 mem' ∧
        PairReady (pairNextEnv E') scratch k (16*(b+1)) 8 (specWindow block (16*(b+1)))
          (roundsFrom s (schedule block) (16*b+2*j) (2*(n+1))) ∧
        PairScratch mem'.mem scratch (schedule block) b 8 ∧ PairConstants mem'.mem k ∧
        RegFrame 173 271 E E' ∧ ScratchFrame scratch mem mem' := by
  induction n with
  | zero =>
    intro j hj E mem s h hs hk
    have hj7 : j=7 := by omega
    subst j
    let E' := pairSpecEnv E scratch k (16*b+2*7) 7 block s
    let mem' := pairSpecMem mem scratch (16*b+2*7) 7 block
    refine ⟨E', mem', ExecTrace.single (pair_spec_exit E mem scratch k b block s hb h hs hk),
      ?_, pairSpecMem_scratch mem scratch b 7 block (by decide) hs,
      pairSpecMem_constants mem scratch k (16*b+2*7) 7 block (by decide) hs.live hk hd,
      (pairSpecEnv_frame _ _ _ _ _ _ _).enlarge (by decide) (by decide), ?_⟩
    · have hn := pairSpecEnv_next_ready E scratch k (16*b+2*7) 7 block s (by omega) h
      simpa only [show 16*b+2*7+2=16*(b+1) by omega] using hn
    · exact pairSpecMem_frame mem scratch (16*b+2*7) 7 block hs.live (by decide)
  | succ n ih =>
    intro j hj E mem s h hs hk
    have hj7 : j<7 := by omega
    let r := 16*b+2*j
    let s1 := roundsFrom s (schedule block) r 2
    let E1 := pairNextEnv (pairSpecEnv E scratch k r j block s)
    let mem1 := pairSpecMem mem scratch r j block
    have hrnext : r+2=16*b+2*(j+1) := by dsimp [r]; omega
    have hnext : PairReady E1 scratch k (16*b+2*(j+1)) (j+1)
        (specWindow block (16*b+2*(j+1))) s1 := by
      have hn := pairSpecEnv_next_ready E scratch k r j block s (by dsimp [r]; omega) h
      simpa only [hrnext] using hn
    have hs1 := pairSpecMem_scratch mem scratch b j block (by omega) hs
    have hk1 := pairSpecMem_constants mem scratch k r j block (by omega) hs.live hk hd
    obtain ⟨E', mem', ht, hf, hs', hk', he, hm⟩ :=
      ih (j+1) (by omega) E1 mem1 s1 hnext hs1 hk1
    refine ⟨E', mem', ExecTrace.step (pair_spec_backedge E mem scratch k b j block s hb hj7 h hs hk) ht,
      ?_, hs', hk', (pairSpecNext_frame _ _ _ _ _ _ _).trans he,
      (pairSpecMem_frame mem scratch r j block hs.live (by omega)).trans hm⟩
    have hround := roundsFrom_add s (schedule block) r 2 (2*(n+1))
    rw [hrnext] at hround
    rw [← hround] at hf
    simpa only [show 2+2*(n+1)=2*(n+1+1) by omega] using hf

/-- One whole group: sixteen standard rounds and eight exact imported bb5 blocks. -/
theorem pair_group (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch k : Pointer) (block : Bytes) (b : Nat) (s : Spec.State)
    (hb : b<4) (h : PairReady E scratch k (16*b) 0 (specWindow block (16*b)) s)
    (hs : PairScratch mem.mem scratch (schedule block) b 0) (hk : PairConstants mem.mem k)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) :
    ∃ E' mem', ExecTrace (program g) 8 E 5 mem E' 3 mem' ∧
      PairReady (pairNextEnv E') scratch k (16*(b+1)) 8 (specWindow block (16*(b+1)))
        (roundsFrom s (schedule block) (16*b) 16) ∧
      PairScratch mem'.mem scratch (schedule block) b 8 ∧ PairConstants mem'.mem k ∧
      RegFrame 173 271 E E' ∧ ScratchFrame scratch mem mem' := by
  simpa only [Nat.mul_zero, Nat.add_zero] using
    pair_group_suffix g scratch k block b hb hd 7 0 (by decide) E mem s h hs hk

end Agave.Ed25519.SHA512.Execution.Avx2
