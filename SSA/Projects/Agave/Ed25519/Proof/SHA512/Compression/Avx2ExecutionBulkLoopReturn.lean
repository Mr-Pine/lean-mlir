import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoop

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem bulk_loop_evalFrom (g : Globals) (chain data scratch cache : Pointer)
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
    PairConstants mem.mem g.address0 → SmallRange mem.mem chain 64 →
    ∃ mem', (program g).evalFrom (139*(k+1)+2) E 9 mem =
      .value (some .nil, {mem' with mem := (mem'.mem.storeAt chain
        (Spec.run (pack initial)
          (readBytes mem.mem (data.add (BitVec.ofNat 64 (128*index))) (256*(k+1)))))}) ∧
      BulkPairMemFrame scratch cache mem mem'  := by
  intro E mem index initial hi ho hdata hb hd hs hc hk hchain
  obtain ⟨E',mem',final,ht,hr,hspec,hm⟩ :=
    bulk_loop_positive g chain data scratch cache hsc hsd hcd hsk hck k
      E mem index initial hi ho hdata hb hd hs hc hk
  refine ⟨mem', ?_, hm⟩
  rw [ht.evalFrom 2, bulk_store_evalFrom g E' mem' chain final hr (hm.live hchain), hspec]

end Agave.Ed25519.SHA512.Execution.Avx2
