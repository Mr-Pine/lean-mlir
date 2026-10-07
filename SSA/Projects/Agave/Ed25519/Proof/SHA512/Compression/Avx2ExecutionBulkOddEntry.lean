import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCountOne
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkOdd
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkEntry

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem bulk_odd_entry_to_pairs (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hp : E.read (%arg0) = .value chain) (hq : E.read (%arg1) = .value data)
    (count : BitVec 64) (hn : E.read (%arg2) = .value count)
    (hodd : bulkParity count = 1#64) :
    ExecTrace (program g) 3 E 0 mem
      (initialPairEnv (entryEnv g E mem) chain data mem.allocaPtr
        (unpack (mem.mem.readAt chain 512)) (readBytes mem.mem data 128)) 5
      (initialScratchStores (entryState mem) mem.allocaPtr
        (readBytes mem.mem data 128) 8) := by
  have hentry := entry_ready g E mem
  have hp' := ((entry_frame g E mem).read (%arg0)).trans hp
  have hq' := ((entry_frame g E mem).read (%arg1)).trans hq
  have hsep := (entry_slots_disjoint_old hwf hd 1024).1
  have hinit := initial_block_run_unpack (entryEnv g E mem) (entryState mem)
    chain data mem.allocaPtr (hentry.initial_chain chain hp')
    (hentry.initial_vector data hq') (entryState_live hwf hc)
    (entryState_live hwf hd) (entry_scratch_live mem hwf) hsep
  rw [entryState_read hwf hc 512, entryState_readBytes hwf hd] at hinit
  have hgroup := group_pair_entry
    (initialGroupEnv (initialBlockEnv (entryEnv g E mem) chain data mem.allocaPtr
      (unpack (mem.mem.readAt chain 512)) (readBytes mem.mem data 128)))
    (initialScratchStores (entryState mem) mem.allocaPtr (readBytes mem.mem data 128) 8)
  exact ((ExecTrace.single (bulk_entry_odd g E mem count hn hodd)).trans
    (ExecTrace.single hinit)).trans (ExecTrace.single hgroup)

theorem bulk_odd_entry_compress (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hk : PairConstants mem.mem g.address0)
    (hp : E.read (%arg0) = .value chain) (hq : E.read (%arg1) = .value data)
    (count : BitVec 64) (hn : E.read (%arg2) = .value count)
    (hodd : bulkParity count = 1#64) :
    let initial := unpack (mem.mem.readAt chain 512)
    let block := readBytes mem.mem data 128
    ∃ E' scratchState, ExecTrace (program g) 59 E 0 mem E' 1
        {scratchState with mem := scratchState.mem.storeAt chain (pack (compressBlock initial block))} ∧
      ScratchFrame mem.allocaPtr (entryState mem) scratchState ∧
      scratchState.mem.eraseFrom mem.alloc.nextFreeBlock = mem.mem ∧
      RegFrame 86 320 (entryEnv g E mem) E' ∧ E'.read (%86) = .value 1#64 := by
  let block := readBytes mem.mem data 128
  let initial := unpack (mem.mem.readAt chain 512)
  let Eentry := entryEnv g E mem
  let Ep := initialPairEnv Eentry chain data mem.allocaPtr initial block
  let mi := initialScratchStores (entryState mem) mem.allocaPtr block 8
  let buffer := (mem.alloca 128).allocaPtr
  have hentry : EntryReady g Eentry mem := entry_ready g E mem
  have hp' : Eentry.read (%arg0) = .value chain :=
    ((entry_frame g E mem).read (%arg0)).trans hp
  have hscratch := entry_scratch_live mem hwf
  have hiscratch := initialScratchStores_frame (entryState mem) mem.allocaPtr block
    8 (by decide) hscratch
  have hsepK := (entry_slots_disjoint_old hwf hk.live 5120).1
  have hsepC := (entry_slots_disjoint_old hwf hc 512).1
  have hready := initialPairEnv_ready g Eentry mem chain data initial block hentry
  have hgroup := initialPairEnv_group g Eentry mem chain data initial block hentry
  have hloop := initialPairEnv_loopConstants g Eentry mem chain data initial block hentry
  have hfeed := initialPairEnv_feedForward g Eentry mem chain data initial block hentry hp'
  have hconstants : PairConstants mi.mem g.address0 :=
    (hk.entryState hwf).initialScratchStores block 8 (by decide) hscratch hsepK
  have hchain : mi.mem.readAt chain 512 = pack initial := by
    rw [hiscratch.read chain 512 hsepC, entryState_read hwf hc 512, pack_unpack]
  obtain ⟨Ef, mt, hcompress, hframe, herase, hregs, hconsumed⟩ :=
    bulk_odd_from_pairs g Ep mi mem.allocaPtr g.address0 chain block
      initial mem.alloc.nextFreeBlock (by simp [GlobalState.allocaPtr]) hready
      (initialScratchStores_ready (entryState mem) mem.allocaPtr block hscratch)
      hconstants hgroup hloop hsepK hfeed (hiscratch.live (entryState_live hwf hc))
      hchain hsepC
  refine ⟨Ef, mt, (bulk_odd_entry_to_pairs g E mem chain data hwf hc hd hp hq count hn hodd).trans
    hcompress, hiscratch.trans hframe, ?_, ?_, hconsumed⟩
  · rw [herase, initialScratchStores_erasure (entryState mem) mem.allocaPtr block 8
      mem.alloc.nextFreeBlock (by simp [GlobalState.allocaPtr]), entryState_frame mem hwf]
  · exact ((initialPairEnv_frame Eentry chain data mem.allocaPtr initial block).enlarge
      (by decide) (by decide)).trans hregs

end Agave.Ed25519.SHA512.Execution.Avx2
