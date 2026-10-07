import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoopStep
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkFold

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

theorem BulkPairMemFrame.readBytes {scratch cache : Pointer} {before after : GlobalState}
    (h : BulkPairMemFrame scratch cache before after) (p : Pointer) (n : Nat)
    (hs : scratch.id ≠ p.id) (hc : cache.id ≠ p.id) :
    Agave.Ed25519.Verifier.Execution.Challenge.readBytes after.mem p n =
      Agave.Ed25519.Verifier.Execution.Challenge.readBytes before.mem p n := by
  unfold Agave.Ed25519.Verifier.Execution.Challenge.readBytes
  congr 1
  funext i
  exact h.read _ _ (by simpa using hs) (by simpa using hc)

theorem BulkPairMemFrame.constants {scratch cache k : Pointer} {before after : GlobalState}
    (h : BulkPairMemFrame scratch cache before after) (hk : PairConstants before.mem k)
    (hs : scratch.id ≠ k.id) (hc : cache.id ≠ k.id) : PairConstants after.mem k := by
  refine ⟨h.live hk.live, ?_⟩
  intro r hr
  exact (h.read _ _ (by simpa using hs) (by simpa using hc)).trans (hk.pairs r hr)

/-- Arbitrarily many positive pairs execute the imported backedge and implement
exactly the streaming fold, retaining the private scratch/cache memory frame. -/
theorem bulk_loop_positive (g : Globals) (chain data scratch cache : Pointer)
    (hsc : scratch.id ≠ cache.id) (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id)
    (hsk : scratch.id ≠ g.address0.id) (hck : cache.id ≠ g.address0.id)
    (k : Nat) :
    ∀ (E : Env program.Γ) (mem : GlobalState) (index : Nat) (initial : Spec.State),
    BulkLoopInvariant g E chain scratch cache →
    BulkOuterReady E initial (BitVec.ofNat 64 index) (BitVec.ofNat 64 (k+1)) →
    E.read (%arg1) = .value data →
    index+2*(k+1) < 2^56 →
    SmallRange mem.mem data (128*(index+2*(k+1))) →
    SmallRange mem.mem scratch 128 → SmallRange mem.mem cache 640 →
    PairConstants mem.mem g.address0 →
    ∃ E' mem' final, ExecTrace (program g) (139*(k+1)) E 9 mem E' 17 mem' ∧
      BulkStoreReady E' chain final ∧
      pack final = Spec.run (pack initial)
        (readBytes mem.mem (data.add (BitVec.ofNat 64 (128*index))) (256*(k+1))) ∧
      BulkPairMemFrame scratch cache mem mem' := by
  induction k with
  | zero =>
    intro E mem index initial hi ho hdata hb hd hs hc hk
    have hd' : SmallRange mem.mem data (128*index+256) := by
      convert hd using 1 <;> omega
    obtain ⟨E',m',ht,hr,hm⟩ := bulk_loop_pair_exit g E mem chain data scratch cache index initial
      hi ho hdata hd' hs hc hk hsc hsd hcd hsk hck
    refine ⟨E',m',_,ht,hr,?_,hm⟩
    have hh := bulk_run_pair initial mem.mem (data.add (BitVec.ofNat 64 (128*index))) 0
    have hz (p : Pointer) : readBytes mem.mem p 0 = [] := rfl
    simpa only [Nat.zero_add, Nat.mul_zero, hz, Spec.run_empty, Nat.mul_one] using hh.symm
  | succ k ih =>
    intro E mem index initial hi ho hdata hb hd hs hc hk
    have hd' : SmallRange mem.mem data (128*index+256) :=
      live_prefix hd (by omega)
    have hmore := bulk_counter_nonzero (k+1+1) (by omega) (by omega)
    obtain ⟨E1,m1,ht,hr,hi1,hframe,hm⟩ :=
      bulk_loop_pair_backedge g E mem chain data scratch cache index _ initial hi ho hdata hd'
        hs hc hk hsc hsd hcd hsk hck hmore
    rw [bulk_counter_decrement _ (by omega) (by omega), bulk_index_increment] at hr
    have hsub : k+1+1-1 = k+1 := by omega
    rw [hsub] at hr
    have hd1 : SmallRange m1.mem data (128*(index+2+2*(k+1))) := by
      convert hm.live hd using 1 <;> omega
    obtain ⟨E2,m2,final,ht2,hr2,hspec,hm2⟩ := ih E1 m1 (index+2) _ hi1 hr
      ((hframe.read (%arg1)).trans hdata) (by omega) hd1 (hm.live hs) (hm.live hc)
      (hm.constants hk hsk hck)
    refine ⟨E2,m2,final,?_,hr2,?_,hm.trans hm2⟩
    · convert ht.trans ht2 using 1 <;> omega
    · rw [hm.readBytes _ _ (by simpa using hsd) (by simpa using hcd)] at hspec
      rw [← bulk_pair_pointer] at hspec
      rw [hspec]
      have hh := bulk_run_pair initial mem.mem (data.add (BitVec.ofNat 64 (128*index))) (2*(k+1))
      rw [show 128*(2*(k+1)+2) = 256*(Nat.succ k+1) by omega,
        show 128*(2*(k+1)) = 256*(k+1) by omega] at hh
      exact hh.symm

end Agave.Ed25519.SHA512.Execution.Avx2
