import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairGroup
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairGroupReady

/-! The complete first 64 rounds of the two-block path, with all eighty
second-block cached schedule words produced by the same concrete execution. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

theorem bulk_prefix_groups_suffix (g : Globals) (scratch cache k : Pointer)
    (block₀ block₁ : Bytes)
    (hsc : scratch.id ≠ cache.id) (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id) (n : Nat) :
    ∀ (b : Nat), b+n=3 → ∀ (E : Env program.Γ) (mem : GlobalState) (s : Spec.State),
      BulkPairSpecReady E scratch cache k b 0 block₀ block₁ s →
      PairScratch mem.mem scratch (schedule block₀) b 0 →
      BulkCachePrefix mem.mem cache (schedule block₁) (16*(b+1)) → PairConstants mem.mem k →
      BulkGroupReady E (b+1) → BulkPairLoopConstants E cache →
      ∃ E' mem', ExecTrace (program g) (10*n+9) E 12 mem E' 13 mem' ∧
        BulkTailReady E' scratch 64 (roundsFrom s (schedule block₀) (16*b) (16*(n+1))) ∧
        TailSchedule mem'.mem scratch (schedule block₀) ∧
        BulkSecondSchedule mem'.mem cache (schedule block₁) ∧
        RegFrame 448 581 E E' ∧ BulkPairMemFrame scratch cache mem mem' := by
  induction n with
  | zero =>
    intro b hb E mem s h hs hcache hk hg hc
    have hb3 : b=3 := by omega
    subst b
    obtain ⟨E1, mem1, ht, hv, hs1, hcache1, hk1, he, hm⟩ :=
      bulk_pair_group g E mem scratch cache k block₀ block₁ 3 s (by decide)
        h hs hcache hk hsc hsk hck
    have hg1 := hg.of_pair_frame he
    have he' : RegFrame 448 581 E E1 := he.enlarge (by decide) (by decide)
    have hc1 := hc.of_frame he'
    have hedge : ExecTrace (program g) 1 E1 10 mem1
        (bulkGroupTailEnv (bulkGroupBodyEnv E1 4)) 13 mem1 :=
      ExecTrace.single (bulk_group_exit E1 mem1 hg1)
    refine ⟨bulkGroupTailEnv (bulkGroupBodyEnv E1 4), mem1, ht.trans hedge,
      bulk_group_tail_ready E1 scratch _ cache k _ _ _ _ _ hv hc1,
      hs1.next_group.tail, hcache1.complete,
      he'.trans (bulk_group_tail_frame E1), hm⟩
  | succ n ih =>
    intro b hb E mem s h hs hcache hk hg hc
    have hb3 : b<3 := by omega
    obtain ⟨E1, mem1, ht, hv, hs1, hcache1, hk1, he, hm⟩ :=
      bulk_pair_group g E mem scratch cache k block₀ block₁ b s (by omega)
        h hs hcache hk hsc hsk hck
    have hg1 := hg.of_pair_frame he
    have he' : RegFrame 448 581 E E1 := he.enlarge (by decide) (by decide)
    have hc1 := hc.of_frame he'
    let E2 := bulkGroupResetEnv E1 cache (b+1)
    let s1 := roundsFrom s (schedule block₀) (16*b) 16
    have hr : BulkPairSpecReady E2 scratch cache k (b+1) 0 block₀ block₁ s1 := by
      have hh := bulk_group_reset_ready E1 scratch
        (cache.add (BitVec.ofNat 64 (128*(b+1)))) cache k (16*b+2*8) 8 (b+1)
        _ _ _ hv hc1.zero
      simpa only [BulkPairSpecReady, E2, s1,
        show 16*b+2*8=16*(b+1) by omega, Nat.mul_zero, Nat.add_zero] using hh
    have he2 : RegFrame 448 581 E1 E2 := bulk_group_reset_frame E1 cache (b+1)
    have hc2 := hc1.of_frame he2
    have hg2 : BulkGroupReady E2 (b+1+1) := bulk_group_reset_counter E1 cache (b+1) hg1
    have hedge1 : ExecTrace (program g) 1 E1 10 mem1
        (bulkGroupNextEnv (bulkGroupBodyEnv E1 (b+1))) 11 mem1 :=
      ExecTrace.single (bulk_group_backedge E1 mem1 (b+1) (by omega) hg1)
    have hedge2 : ExecTrace (program g) 1 (bulkGroupNextEnv (bulkGroupBodyEnv E1 (b+1)))
        11 mem1 E2 12 mem1 := by
      apply ExecTrace.single
      apply bulk_group_setup_run _ mem1 cache (b+1+1) (by omega) hcache1.live
      · simpa [bulkGroupNextEnv, bulkGroupBodyEnv, mlir_env] using hc1.cachePtr
      · simp [bulkGroupNextEnv, bulkGroupBodyEnv, mlir_env]
      · simpa [bulkGroupNextEnv, bulkGroupBodyEnv, mlir_env] using hc1.shift
    have hcache2 : BulkCachePrefix mem1.mem cache (schedule block₁) (16*((b+1)+1)) := by
      simpa only [Nat.add_assoc] using hcache1
    obtain ⟨E', mem', ht', hf', hs', hcache', he'', hm'⟩ :=
      ih (b+1) (by omega) E2 mem1 s1 hr hs1.next_group hcache2 hk1 hg2 hc2
    refine ⟨E', mem', ?_, ?_, hs', hcache', (he'.trans he2).trans he'', hm.trans hm'⟩
    · have hh := ((ht.trans hedge1).trans hedge2).trans ht'
      simpa only [show 8+1+1+(10*n+9)=10*(n+1)+9 by omega] using hh
    · have hround := roundsFrom_add s (schedule block₀) (16*b) 16 (16*(n+1))
      have hstart : 16*b+16=16*(b+1) := by omega
      rw [hstart] at hround
      change BulkTailReady E' scratch 64
        (roundsFrom (roundsFrom s (schedule block₀) (16*b) 16)
          (schedule block₀) (16*(b+1)) (16*(n+1))) at hf'
      rw [← hround] at hf'
      simpa only [show 16+16*(n+1)=16*(n+1+1) by omega] using hf'

/-- Thirty-two real bb12 blocks and seven real control blocks reach bb13.
Both cache conclusions are derived from the stores; neither is assumed at entry. -/
theorem bulk_prefix_sixtyfour (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch cache k : Pointer) (block₀ block₁ : Bytes) (initial : Spec.State)
    (h : BulkPairSpecReady E scratch cache k 0 0 block₀ block₁ initial)
    (hs : PairScratch mem.mem scratch (schedule block₀) 0 0)
    (hcache : BulkCachePrefix mem.mem cache (schedule block₁) 16)
    (hk : PairConstants mem.mem k) (hg : BulkGroupReady E 1)
    (hc : BulkPairLoopConstants E cache)
    (hsc : scratch.id ≠ cache.id) (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id) :
    ∃ E' mem', ExecTrace (program g) 39 E 12 mem E' 13 mem' ∧
      BulkTailReady E' scratch 64 (roundsFrom initial (schedule block₀) 0 64) ∧
      TailSchedule mem'.mem scratch (schedule block₀) ∧
      BulkSecondSchedule mem'.mem cache (schedule block₁) ∧
      RegFrame 448 581 E E' ∧ BulkPairMemFrame scratch cache mem mem' :=
  bulk_prefix_groups_suffix g scratch cache k block₀ block₁ hsc hsk hck 3 0 (by decide)
    E mem initial h hs hcache hk hg hc

end Agave.Ed25519.SHA512.Execution.Avx2
