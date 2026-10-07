import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialReady
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntryFacts
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCompressionPrivate
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionConstants
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ContextContract
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! The complete count-one call of the locally imported AVX2 compressor.
The caller's chain and 128 message bytes determine the result, and the three
actual stack allocations disappear under the real RIR call cleanup. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

/-- bb0, bb2 and bb4 establish the first concrete schedule-pair header. -/
theorem entry_to_pairs (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hp : E.read (%arg0) = .value chain) (hq : E.read (%arg1) = .value data)
    (hn : E.read (%arg2) = .value 1#64) :
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
  exact ((ExecTrace.single (entry_block g E mem hn)).trans
    (ExecTrace.single hinit)).trans (ExecTrace.single hgroup)

/-- Exactly 61 imported basic blocks execute successfully for count one.
The public memory is precisely one independent SHA-512 compression update. -/
theorem count_one_evalFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hk : PairConstants mem.mem g.address0)
    (hp : E.read (%arg0) = .value chain) (hq : E.read (%arg1) = .value data)
    (hn : E.read (%arg2) = .value 1#64) :
    ∃ mem', (program g).evalFrom 61 E 0 mem = .value (some .nil, mem') ∧
      (program g).runFrom E 0 mem = .value (.nil, mem') ∧
      mem'.mem.eraseFrom mem.alloc.nextFreeBlock =
        mem.mem.storeAt chain
          (compressBlockBytes (mem.mem.readAt chain 512) (readBytes mem.mem data 128)) ∧
      mem'.alloc.nextFreeBlock = mem.alloc.nextFreeBlock + 3 := by
  let block := readBytes mem.mem data 128
  let initial := unpack (mem.mem.readAt chain 512)
  let Eentry := entryEnv g E mem
  let Ep := initialPairEnv Eentry chain data mem.allocaPtr initial block
  let mi := initialScratchStores (entryState mem) mem.allocaPtr block 8
  let buffer := (mem.alloca 128).allocaPtr
  have hentry : EntryReady g Eentry mem := entry_ready g E mem
  have hp' : Eentry.read (%arg0) = .value chain :=
    ((entry_frame g E mem).read (%arg0)).trans hp
  have hn' : Eentry.read (%arg2) = .value 1#64 :=
    ((entry_frame g E mem).read (%arg2)).trans hn
  have hscratch := entry_scratch_live mem hwf
  have hiscratch := initialScratchStores_frame (entryState mem) mem.allocaPtr block
    8 (by decide) hscratch
  have hsepK := (entry_slots_disjoint_old hwf hk.live 5120).1
  have hsepC := (entry_slots_disjoint_old hwf hc 512).1
  have hready := initialPairEnv_ready g Eentry mem chain data initial block hentry
  have hgroup := initialPairEnv_group g Eentry mem chain data initial block hentry
  have hloop := initialPairEnv_loopConstants g Eentry mem chain data initial block hentry
  have hfeed := initialPairEnv_feedForward g Eentry mem chain data initial block hentry hp'
  have hreturn := initialPairEnv_return g Eentry mem chain data initial block hentry hn'
  have hseed : ReturnSeed Ep buffer := by
    constructor
    · simpa [mlir_env] using hreturn.count
    · simpa [mlir_env] using hreturn.bufferPtr
    · simpa [mlir_env] using hreturn.offset
    · simpa [mlir_env] using hreturn.byteZero
    · simpa [mlir_env] using hreturn.length
    · simpa [mlir_env] using hreturn.one
    · simpa [mlir_env] using hreturn.zero
  have hconstants : PairConstants mi.mem g.address0 :=
    (hk.entryState hwf).initialScratchStores block 8 (by decide) hscratch hsepK
  have hchain : mi.mem.readAt chain 512 = pack initial := by
    rw [hiscratch.read chain 512 hsepC, entryState_read hwf hc 512, pack_unpack]
  obtain ⟨Ef, mt, hcompress, hframe, herase, hret⟩ :=
    compression_from_pairs_private g Ep mi mem.allocaPtr g.address0 chain buffer block
      initial mem.alloc.nextFreeBlock (by simp [GlobalState.allocaPtr]) hready
      (initialScratchStores_ready (entryState mem) mem.allocaPtr block hscratch)
      hconstants hgroup hloop hsepK hfeed (hiscratch.live (entryState_live hwf hc))
      hchain hsepC hseed
  let mout : GlobalState := {mt with mem := mt.mem.storeAt chain (pack (compressBlock initial block))}
  have hbuffer : SmallRange mout.mem buffer 640 :=
    (hframe.live (hiscratch.live (entry_cache_live mem hwf))).storeAt _ _
  have htrace := (entry_to_pairs g E mem chain data hwf hc hd hp hq hn).trans hcompress
  refine ⟨returnState mout buffer, ?_, ?_, ?_, ?_⟩
  · rw [show 61 = 59+2 by decide, htrace.evalFrom 2]
    exact return_evalFrom g Ef mout buffer hret hbuffer
  · rw [htrace.runFrom]
    exact return_runFrom g Ef mout buffer hret hbuffer
  · rw [returnState_erase mout buffer mem.alloc.nextFreeBlock
        (by simp [buffer, GlobalState.allocaPtr, GlobalState.alloca]),
      MemoryState.eraseFrom_storeAt, herase,
      initialScratchStores_erasure (entryState mem) mem.allocaPtr block 8
        mem.alloc.nextFreeBlock (by simp [GlobalState.allocaPtr]),
      entryState_frame mem hwf]
    rfl
  · change mt.alloc.nextFreeBlock = _
    rw [hframe.alloc, hiscratch.alloc, entryState_counter]

/-- The exact call includes RIR's real cleanup of all three private slots. -/
theorem count_one_call (g : Globals) (mem : GlobalState) (chain data : Pointer)
    (hwf : mem.WF) (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hk : PairConstants mem.mem g.address0) :
    (program g).call (.cons (.value chain) (.cons (.value data) (.cons (.value 1#64) .nil)))
      mem = .value (.nil, {
        alloc := ⟨mem.alloc.nextFreeBlock + 3⟩,
        mem := mem.mem.storeAt chain (compressBlockBytes (mem.mem.readAt chain 512)
          (readBytes mem.mem data 128)) }) := by
  let args : Vals program.Γ.args := .cons (.value chain) (.cons (.value data)
    (.cons (.value 1#64) .nil))
  obtain ⟨mout, _, hrunFrom, herase, halloc⟩ := count_one_evalFrom g (Env.init args.get) mem
    chain data hwf hc hd hk (by rfl) (by rfl) (by rfl)
  have hrun : (program g).run args mem = .value (.nil, mout) := by
    rw [Func.run_runFrom_eq]
    exact hrunFrom
  have hcall := Func.call_of_run hrun
  rw [herase] at hcall
  have ha : mout.alloc = ⟨mem.alloc.nextFreeBlock+3⟩ := by
    cases h : mout.alloc
    simp only [h] at halloc
    exact congrArg AllocState.mk halloc
  simpa only [args, ha] using hcall

/-- Express the checked one-block result through the existing pure compression interface. -/
theorem count_one_call_spec (g : Globals) (mem : GlobalState) (chain data : Pointer)
    (hwf : mem.WF) (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hk : PairConstants mem.mem g.address0) :
    (program g).call (.cons (.value chain) (.cons (.value data) (.cons (.value 1#64) .nil)))
      mem = .value (.nil, {
        alloc := ⟨mem.alloc.nextFreeBlock + 3⟩,
        mem := mem.mem.storeAt chain (Spec.compression.run (mem.mem.readAt chain 512)
          (readBytes mem.mem data 128)) }) := by
  rw [show Spec.compression.run (mem.mem.readAt chain 512) (readBytes mem.mem data 128) =
    compressBlockBytes (mem.mem.readAt chain 512) (readBytes mem.mem data 128) from
      Spec.run_one_block _ _ (by simp [readBytes])]
  exact count_one_call g mem chain data hwf hc hd hk

/-- The exact pinned source globals supply the constant-table premise. -/
theorem count_one_call_source (g : ShaSourceGlobals) (mem : GlobalState)
    (chain data : Pointer) (hwf : mem.WF)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hsource : ShaSourceReady g mem) :
    (program ⟨g.compression.constantsPtr⟩).call
      (.cons (.value chain) (.cons (.value data) (.cons (.value 1#64) .nil)))
      mem = .value (.nil, {
        alloc := ⟨mem.alloc.nextFreeBlock + 3⟩,
        mem := mem.mem.storeAt chain (Spec.compression.run (mem.mem.readAt chain 512)
          (readBytes mem.mem data 128)) }) :=
  count_one_call_spec ⟨g.compression.constantsPtr⟩ mem chain data hwf hc hd
    (pairConstants_of_source g mem hsource)

/-- The direct AVX2 backend inhabits the existing contextual single-block ABI.
Its cache byte is preserved, including when the caller is initially cold. -/
theorem count_one_contract (g : CompressionGlobals) :
    OneBlockCompressContractUnder g (program ⟨g.constantsPtr⟩).call Spec.compression := by
  intro mem chain data hwf hr hc hd _
  let result := Spec.compression.run (mem.mem.readAt chain 512) (readBytes mem.mem data 128)
  let after : GlobalState := {
    alloc := ⟨mem.alloc.nextFreeBlock + 3⟩,
    mem := mem.mem.storeAt chain result }
  have hcall := count_one_call_spec ⟨g.constantsPtr⟩ mem chain data hwf hc hd
    (pairConstants_of_ready g mem hr.globals)
  obtain ⟨old, ho, hp⟩ := hr.globals.cache
  have he : CompressionStoreEffect g mem after chain result := by
    refine ⟨old, old, ho, hp, CacheTransition.refl old, ?_, ?_⟩
    · rw [cache_store_same g mem.mem old hp]
    · dsimp [after]
      omega
  exact ⟨after, hcall, he, he.ready hr.globals hr.chainConstants hr.chainCache⟩

end Agave.Ed25519.SHA512.Execution.Avx2
