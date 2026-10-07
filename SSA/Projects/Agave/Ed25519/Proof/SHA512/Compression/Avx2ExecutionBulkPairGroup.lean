import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairStep
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTrace

/-! Eight concrete bb12 iterations consume sixteen standard first-block rounds
and append sixteen standard second-block schedule words. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

theorem bulk_pair_group_suffix (g : Globals) (scratch cache k : Pointer)
    (block₀ block₁ : Bytes) (b : Nat) (hb : b<4)
    (hsc : scratch.id ≠ cache.id) (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id) (n : Nat) :
    ∀ (j : Nat), j+n=7 → ∀ (E : Env program.Γ) (mem : GlobalState) (s : Spec.State),
      BulkPairSpecReady E scratch cache k b j block₀ block₁ s →
      PairScratch mem.mem scratch (schedule block₀) b j →
      BulkCachePrefix mem.mem cache (schedule block₁) (16*(b+1)+2*j) → PairConstants mem.mem k →
      ∃ E' mem', ExecTrace (program g) (n+1) E 12 mem E' 10 mem' ∧
        BulkPairSpecReady (bulkPairNextEnv E') scratch cache k b 8 block₀ block₁
          (roundsFrom s (schedule block₀) (16*b+2*j) (2*(n+1))) ∧
        PairScratch mem'.mem scratch (schedule block₀) b 8 ∧
        BulkCachePrefix mem'.mem cache (schedule block₁) (16*(b+2)) ∧
        PairConstants mem'.mem k ∧ RegFrame 470 572 E E' ∧
        BulkPairMemFrame scratch cache mem mem' := by
  induction n with
  | zero =>
    intro j hj E mem s h hs hc hk
    have hj7 : j=7 := by omega
    subst j
    let E' := bulkPairSpecEnv E scratch cache k b 7 block₀ block₁ s
    let mem' := bulkPairSpecMem mem scratch cache b 7 (schedule block₀) (schedule block₁)
    refine ⟨E', mem', ExecTrace.single (bulk_pair_spec_exit E mem scratch cache k b block₀ block₁ s hb h hs hc hk),
      ?_, bulkPairSpecMem_scratch mem scratch cache b 7 (schedule block₀) (schedule block₁) (by decide) hs hsc,
      ?_, bulkPairSpecMem_constants mem scratch cache k b 7 (schedule block₀) (schedule block₁) hk hsk hck,
      (bulkPairSpecEnv_frame _ _ _ _ _ _ _ _ _).enlarge (by decide) (by decide),
      bulkPairSpecMem_frame _ _ _ _ _ _ _⟩
    · exact bulkPairSpecEnv_next_ready E scratch cache k b 7 block₀ block₁ s (by omega) h
    · have hh := bulkPairSpecMem_cache mem scratch cache b 7 (schedule block₀) (schedule block₁) hb (by decide) hc hsc
      simpa only [show 16*(b+1)+2*(7+1)=16*(b+2) by omega] using hh
  | succ n ih =>
    intro j hj E mem s h hs hc hk
    have hj7 : j<7 := by omega
    let r := 16*b+2*j
    let s1 := roundsFrom s (schedule block₀) r 2
    let E1 := bulkPairNextEnv (bulkPairSpecEnv E scratch cache k b j block₀ block₁ s)
    let mem1 := bulkPairSpecMem mem scratch cache b j (schedule block₀) (schedule block₁)
    have hrnext : r+2=16*b+2*(j+1) := by dsimp [r]; omega
    have hnext : BulkPairSpecReady E1 scratch cache k b (j+1) block₀ block₁ s1 :=
      bulkPairSpecEnv_next_ready E scratch cache k b j block₀ block₁ s (by omega) h
    have hs1 := bulkPairSpecMem_scratch mem scratch cache b j (schedule block₀) (schedule block₁) (by omega) hs hsc
    have hc1 := bulkPairSpecMem_cache mem scratch cache b j (schedule block₀) (schedule block₁) hb (by omega) hc hsc
    have hk1 := bulkPairSpecMem_constants mem scratch cache k b j (schedule block₀) (schedule block₁) hk hsk hck
    obtain ⟨E', mem', ht, hf, hs', hc', hk', he, hm⟩ :=
      ih (j+1) (by omega) E1 mem1 s1 hnext hs1 hc1 hk1
    refine ⟨E', mem', ExecTrace.step
      (bulk_pair_spec_backedge E mem scratch cache k b j block₀ block₁ s hb hj7 h hs hc hk) ht,
      ?_, hs', hc', hk', (bulkPairSpecNext_frame _ _ _ _ _ _ _ _ _).trans he,
      (bulkPairSpecMem_frame _ _ _ _ _ _ _).trans hm⟩
    have hround := roundsFrom_add s (schedule block₀) r 2 (2*(n+1))
    rw [hrnext] at hround
    rw [← hround] at hf
    simpa only [show 2+2*(n+1)=2*(n+1+1) by omega] using hf

theorem bulk_pair_group (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k : Pointer) (block₀ block₁ : Bytes) (b : Nat) (s : Spec.State)
    (hb : b<4) (h : BulkPairSpecReady E scratch cache k b 0 block₀ block₁ s)
    (hs : PairScratch mem.mem scratch (schedule block₀) b 0)
    (hc : BulkCachePrefix mem.mem cache (schedule block₁) (16*(b+1)))
    (hk : PairConstants mem.mem k)
    (hsc : scratch.id ≠ cache.id) (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id) :
    ∃ E' mem', ExecTrace (program g) 8 E 12 mem E' 10 mem' ∧
      BulkPairSpecReady (bulkPairNextEnv E') scratch cache k b 8 block₀ block₁
        (roundsFrom s (schedule block₀) (16*b) 16) ∧
      PairScratch mem'.mem scratch (schedule block₀) b 8 ∧
      BulkCachePrefix mem'.mem cache (schedule block₁) (16*(b+2)) ∧ PairConstants mem'.mem k ∧
      RegFrame 470 572 E E' ∧ BulkPairMemFrame scratch cache mem mem' := by
  simpa only [Nat.mul_zero, Nat.add_zero] using
    bulk_pair_group_suffix g scratch cache k block₀ block₁ b hb hsc hsk hck 7 0 (by decide) E mem s h hs hc hk

end Agave.Ed25519.SHA512.Execution.Avx2
