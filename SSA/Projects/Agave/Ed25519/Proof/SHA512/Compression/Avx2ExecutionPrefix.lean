import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairGroup

/-! Four groups of imported pair blocks compute the first sixty-four SHA-512
rounds and establish the exact scratch input of the scalar tail. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem group_tail_frame (E : Env program.Γ) :
    GroupFrame E (groupTailEnv (groupBodyEnv E 3)) := by
  unfold groupTailEnv groupBodyEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem virtual_tail_constants {E : Env program.Γ} {scratch k : Pointer}
    {r j : Nat} {q : Window} {s : Spec.State}
    (h : PairReady (pairNextEnv E) scratch k r j q s)
    (hc : PairLoopConstants E) : GroupTailConstants E scratch := by
  have hf := pairNextEnv_frame E
  constructor
  · exact (hf.read (%81)).symm.trans h.scalar.scratchPtr
  · exact (hf.read (%1)).symm.trans h.schedule.one
  · exact hc.tailLimit
  · exact (hf.read (%36)).symm.trans h.scalar.rot14
  · exact (hf.read (%37)).symm.trans h.scalar.rot18
  · exact (hf.read (%38)).symm.trans h.scalar.rot41
  · exact (hf.read (%39)).symm.trans h.scalar.rot28
  · exact (hf.read (%40)).symm.trans h.scalar.rot34
  · exact (hf.read (%41)).symm.trans h.scalar.rot39
  · exact hc.mask

/-- A nonempty suffix of groups executes all remaining pair rounds, plus the
actual bb3/bb4 transitions, and stops at the real scalar-tail header. -/
theorem prefix_groups_suffix (g : Globals) (scratch k : Pointer) (block : Bytes)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) (n : Nat) :
    ∀ (b : Nat), b+n=3 → ∀ (E : Env program.Γ) (mem : GlobalState) (s : Spec.State),
      PairReady E scratch k (16*b) 0 (specWindow block (16*b)) s →
      PairScratch mem.mem scratch (schedule block) b 0 → PairConstants mem.mem k →
      GroupReady E b → PairLoopConstants E →
      ∃ E' mem', ExecTrace (program g) (10*n+9) E 5 mem E' 6 mem' ∧
        TailReady E' scratch 64 (roundsFrom s (schedule block) (16*b) (16*(n+1))) ∧
        TailSchedule mem'.mem scratch (schedule block) ∧
        GroupFrame E E' ∧ ScratchFrame scratch mem mem' := by
  induction n with
  | zero =>
    intro b hb E mem s h hs hk hg hc
    have hb3 : b = 3 := by omega
    subst b
    obtain ⟨E1, mem1, ht, hv, hs1, hk1, he, hm⟩ :=
      pair_group g E mem scratch k block 3 s (by decide) h hs hk hd
    have hg1 := hg.of_pair_frame he
    have he' : GroupFrame E E1 := he.enlarge (by decide) (by decide)
    have hc1 := hc.of_frame he'
    have hedge : ExecTrace (program g) 1 E1 3 mem1
        (groupTailEnv (groupBodyEnv E1 3)) 6 mem1 :=
      ExecTrace.single (group_exit E1 mem1 hg1)
    refine ⟨groupTailEnv (groupBodyEnv E1 3), mem1, ht.trans hedge,
      group_tail_ready E1 scratch _ hv.final_of_next (virtual_tail_constants hv hc1)
        hc1.tailStart, ?_, he'.trans (group_tail_frame E1), hm⟩
    exact hs1.next_group.tail
  | succ n ih =>
    intro b hb E mem s h hs hk hg hc
    have hb3 : b < 3 := by omega
    obtain ⟨E1, mem1, ht, hv, hs1, hk1, he, hm⟩ :=
      pair_group g E mem scratch k block b s (by omega) h hs hk hd
    have hg1 := hg.of_pair_frame he
    have he' : GroupFrame E E1 := he.enlarge (by decide) (by decide)
    have hc1 := hc.of_frame he'
    let E2 := groupPairEnv (groupNextEnv (groupBodyEnv E1 b))
    let s1 := roundsFrom s (schedule block) (16*b) 16
    have hr : PairReady E2 scratch k (16*(b+1)) 0 (specWindow block (16*(b+1))) s1 :=
      pair_group_reset_ready E1 scratch k (16*(b+1)) 8 b _ _ hv hc1.zero
    have he2 : GroupFrame E1 E2 := group_reset_frame E1 b
    have hc2 := hc1.of_frame he2
    have hg2 : GroupReady E2 (b+1) := group_reset_counter E1 b hg1
    have hedge1 : ExecTrace (program g) 1 E1 3 mem1
        (groupNextEnv (groupBodyEnv E1 b)) 4 mem1 :=
      ExecTrace.single (group_backedge E1 mem1 b hb3 hg1)
    have hedge2 : ExecTrace (program g) 1 (groupNextEnv (groupBodyEnv E1 b)) 4 mem1
        E2 5 mem1 := ExecTrace.single (group_pair_entry _ mem1)
    obtain ⟨E', mem', ht', hf', hs', he'', hm'⟩ :=
      ih (b+1) (by omega) E2 mem1 s1 hr hs1.next_group hk1 hg2 hc2
    refine ⟨E', mem', ?_, ?_, hs', (he'.trans he2).trans he'', hm.trans hm'⟩
    · have hh := ((ht.trans hedge1).trans hedge2).trans ht'
      simpa only [show 8+1+1+(10*n+9)=10*(n+1)+9 by omega] using hh
    · have hround := roundsFrom_add s (schedule block) (16*b) 16 (16*(n+1))
      have hstart : 16*b+16=16*(b+1) := by omega
      rw [hstart] at hround
      change TailReady E' scratch 64
        (roundsFrom (roundsFrom s (schedule block) (16*b) 16)
          (schedule block) (16*(b+1)) (16*(n+1))) at hf'
      rw [← hround] at hf'
      simpa only [show 16+16*(n+1)=16*(n+1+1) by omega] using hf'

/-- Thirty-two actual bb5 iterations plus seven actual control blocks reach
bb6 after sixty-four standard rounds, with its final sixteen scratch words. -/
theorem prefix_sixtyfour (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch k : Pointer) (block : Bytes) (initial : Spec.State)
    (h : PairReady E scratch k 0 0 (specWindow block 0) initial)
    (hs : PairScratch mem.mem scratch (schedule block) 0 0)
    (hk : PairConstants mem.mem k) (hg : GroupReady E 0) (hc : PairLoopConstants E)
    (hd : (Range.of scratch 1024).Disjoint (Range.of k 5120)) :
    ∃ E' mem', ExecTrace (program g) 39 E 5 mem E' 6 mem' ∧
      TailReady E' scratch 64 (roundsFrom initial (schedule block) 0 64) ∧
      TailSchedule mem'.mem scratch (schedule block) ∧
      GroupFrame E E' ∧ ScratchFrame scratch mem mem' :=
  prefix_groups_suffix g scratch k block hd 3 0 (by decide) E mem initial h hs hk hg hc

end Agave.Ed25519.SHA512.Execution.Avx2
