import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialBlockSlices
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialMemory

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure InitialVectorReady (E : Env program.Γ) (data scratch : Pointer) : Prop where
  dataPtr : E.read (%arg1) = .value data
  scratchPtr : E.read (%81) = .value scratch
  k0 : E.read (%11) = pairVec (constants[0]!) (constants[1]!)
  k1 : E.read (%12) = pairVec (constants[2]!) (constants[3]!)
  k2 : E.read (%13) = pairVec (constants[4]!) (constants[5]!)
  k3 : E.read (%14) = pairVec (constants[6]!) (constants[7]!)
  k4 : E.read (%16) = pairVec (constants[8]!) (constants[9]!)
  k5 : E.read (%18) = pairVec (constants[10]!) (constants[11]!)
  k6 : E.read (%20) = pairVec (constants[12]!) (constants[13]!)
  k7 : E.read (%22) = pairVec (constants[14]!) (constants[15]!)

def initialBlockEnv (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) : Env program.Γ :=
  let E := initialChainEnv E chain s
  let E := initialSlice0Env E data scratch block (constants[0]!) (constants[1]!)
  let E := initialSlice1Env E data scratch block (constants[2]!) (constants[3]!)
  let E := initialSlice2Env E data scratch block (constants[4]!) (constants[5]!)
  let E := initialSlice3Env E data scratch block (constants[6]!) (constants[7]!)
  let E := initialSlice4Env E data scratch block (constants[8]!) (constants[9]!)
  let E := initialSlice5Env E data scratch block (constants[10]!) (constants[11]!)
  let E := initialSlice6Env E data scratch block (constants[12]!) (constants[13]!)
  let E := initialSlice7Env E data scratch block (constants[14]!) (constants[15]!)
  E

theorem initialBlockEnv_frame (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    RegFrame 92 152 E (initialBlockEnv E chain data scratch s block) := by
  unfold initialBlockEnv initialChainEnv initialSlice0Env initialSlice1Env initialSlice2Env initialSlice3Env initialSlice4Env initialSlice5Env initialSlice6Env initialSlice7Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

/-- Execute every imported bb2 instruction from concrete chain and message reads. -/
theorem initial_block_body (E : Env program.Γ) (mem : GlobalState)
    (chain data scratch : Pointer) (s : Spec.State)
    (h : InitialChainReady E chain) (hv : InitialVectorReady E data scratch)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hs : SmallRange mem.mem scratch 128) (hr : InitialChainReads mem.mem chain s)
    (hsep : (Range.of scratch 1024).Disjoint (Range.of data 1024)) :
    List.foldlM Instr.run E program.bb2.body mem =
      .value (initialBlockEnv E chain data scratch s (readBytes mem.mem data 128),
        initialScratchStores mem scratch (readBytes mem.mem data 128) 8) := by
  let block := readBytes mem.mem data 128
  let E0 := initialChainEnv E chain s
  let E1 := initialSlice0Env E0 data scratch block (constants[0]!) (constants[1]!)
  let E2 := initialSlice1Env E1 data scratch block (constants[2]!) (constants[3]!)
  let E3 := initialSlice2Env E2 data scratch block (constants[4]!) (constants[5]!)
  let E4 := initialSlice3Env E3 data scratch block (constants[6]!) (constants[7]!)
  let E5 := initialSlice4Env E4 data scratch block (constants[8]!) (constants[9]!)
  let E6 := initialSlice5Env E5 data scratch block (constants[10]!) (constants[11]!)
  let E7 := initialSlice6Env E6 data scratch block (constants[12]!) (constants[13]!)
  let E8 := initialSlice7Env E7 data scratch block (constants[14]!) (constants[15]!)
  have hchain := initial_chain_body E mem chain s h hc hr
  have hf0 := initialScratchStores_frame mem scratch block 0 (by decide) hs
  have hread0 := initialScratchStores_load_pair mem scratch data block 0 0
    (by decide) (by decide) hs hd hsep
  have hex0 := initial_slice0_body E0 (initialScratchStores mem scratch block 0)
    data scratch block (constants[0]!) (constants[1]!) (hf0.live hd) (hf0.live hs)
    (by simpa [E0, initialChainEnv, mlir_env] using hv.dataPtr)
    (by simpa [E0, initialChainEnv, mlir_env] using hv.scratchPtr)
    (by simpa [E0, initialChainEnv, mlir_env] using hv.k0)
    (by simpa [block] using hread0)
  have hf1 := initialScratchStores_frame mem scratch block 1 (by decide) hs
  have hread1 := initialScratchStores_load_pair mem scratch data block 1 1
    (by decide) (by decide) hs hd hsep
  have hex1 := initial_slice1_body E1 (initialScratchStores mem scratch block 1)
    data scratch block (constants[2]!) (constants[3]!) (hf1.live hd) (hf1.live hs)
    (by simpa [E0, E1, initialChainEnv, initialSlice0Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, initialChainEnv, initialSlice0Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, initialChainEnv, initialSlice0Env , mlir_env] using hv.k1)
    (by simpa [block] using hread1)
  have hf2 := initialScratchStores_frame mem scratch block 2 (by decide) hs
  have hread2 := initialScratchStores_load_pair mem scratch data block 2 2
    (by decide) (by decide) hs hd hsep
  have hex2 := initial_slice2_body E2 (initialScratchStores mem scratch block 2)
    data scratch block (constants[4]!) (constants[5]!) (hf2.live hd) (hf2.live hs)
    (by simpa [E0, E1, E2, initialChainEnv, initialSlice0Env, initialSlice1Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, E2, initialChainEnv, initialSlice0Env, initialSlice1Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, E2, initialChainEnv, initialSlice0Env, initialSlice1Env , mlir_env] using hv.k2)
    (by simpa [block] using hread2)
  have hf3 := initialScratchStores_frame mem scratch block 3 (by decide) hs
  have hread3 := initialScratchStores_load_pair mem scratch data block 3 3
    (by decide) (by decide) hs hd hsep
  have hex3 := initial_slice3_body E3 (initialScratchStores mem scratch block 3)
    data scratch block (constants[6]!) (constants[7]!) (hf3.live hd) (hf3.live hs)
    (by simpa [E0, E1, E2, E3, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, E2, E3, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, E2, E3, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env , mlir_env] using hv.k3)
    (by simpa [block] using hread3)
  have hf4 := initialScratchStores_frame mem scratch block 4 (by decide) hs
  have hread4 := initialScratchStores_load_pair mem scratch data block 4 4
    (by decide) (by decide) hs hd hsep
  have hex4 := initial_slice4_body E4 (initialScratchStores mem scratch block 4)
    data scratch block (constants[8]!) (constants[9]!) (hf4.live hd) (hf4.live hs)
    (by simpa [E0, E1, E2, E3, E4, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, E2, E3, E4, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, E2, E3, E4, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env , mlir_env] using hv.k4)
    (by simpa [block] using hread4)
  have hf5 := initialScratchStores_frame mem scratch block 5 (by decide) hs
  have hread5 := initialScratchStores_load_pair mem scratch data block 5 5
    (by decide) (by decide) hs hd hsep
  have hex5 := initial_slice5_body E5 (initialScratchStores mem scratch block 5)
    data scratch block (constants[10]!) (constants[11]!) (hf5.live hd) (hf5.live hs)
    (by simpa [E0, E1, E2, E3, E4, E5, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, E2, E3, E4, E5, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, E2, E3, E4, E5, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env , mlir_env] using hv.k5)
    (by simpa [block] using hread5)
  have hf6 := initialScratchStores_frame mem scratch block 6 (by decide) hs
  have hread6 := initialScratchStores_load_pair mem scratch data block 6 6
    (by decide) (by decide) hs hd hsep
  have hex6 := initial_slice6_body E6 (initialScratchStores mem scratch block 6)
    data scratch block (constants[12]!) (constants[13]!) (hf6.live hd) (hf6.live hs)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env, initialSlice5Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env, initialSlice5Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env, initialSlice5Env , mlir_env] using hv.k6)
    (by simpa [block] using hread6)
  have hf7 := initialScratchStores_frame mem scratch block 7 (by decide) hs
  have hread7 := initialScratchStores_load_pair mem scratch data block 7 7
    (by decide) (by decide) hs hd hsep
  have hex7 := initial_slice7_body E7 (initialScratchStores mem scratch block 7)
    data scratch block (constants[14]!) (constants[15]!) (hf7.live hd) (hf7.live hs)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, E7, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env, initialSlice5Env, initialSlice6Env , mlir_env] using hv.dataPtr)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, E7, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env, initialSlice5Env, initialSlice6Env , mlir_env] using hv.scratchPtr)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, E7, initialChainEnv, initialSlice0Env, initialSlice1Env, initialSlice2Env, initialSlice3Env, initialSlice4Env, initialSlice5Env, initialSlice6Env , mlir_env] using hv.k7)
    (by simpa [block] using hread7)
  have hcut : program.bb2.body = program.bb2.body.take 18 ++
    (program.bb2.body.drop 18).take 5 ++
    (program.bb2.body.drop 23).take 7 ++
    (program.bb2.body.drop 30).take 7 ++
    (program.bb2.body.drop 37).take 7 ++
    (program.bb2.body.drop 44).take 7 ++
    (program.bb2.body.drop 51).take 7 ++
    (program.bb2.body.drop 58).take 7 ++
    (program.bb2.body.drop 65).take 7 ++
    program.bb2.body.drop 72 := by rfl
  change List.foldlM Instr.run E0 ((program.bb2.body.drop 18).take 5) mem =
    .value (E1, initialScratchStores mem scratch block 1) at hex0
  change List.foldlM Instr.run E1 ((program.bb2.body.drop 23).take 7)
    (initialScratchStores mem scratch block 1) =
      .value (E2, initialScratchStores mem scratch block 2) at hex1
  change List.foldlM Instr.run E2 ((program.bb2.body.drop 30).take 7)
    (initialScratchStores mem scratch block 2) =
      .value (E3, initialScratchStores mem scratch block 3) at hex2
  change List.foldlM Instr.run E3 ((program.bb2.body.drop 37).take 7)
    (initialScratchStores mem scratch block 3) =
      .value (E4, initialScratchStores mem scratch block 4) at hex3
  change List.foldlM Instr.run E4 ((program.bb2.body.drop 44).take 7)
    (initialScratchStores mem scratch block 4) =
      .value (E5, initialScratchStores mem scratch block 5) at hex4
  change List.foldlM Instr.run E5 ((program.bb2.body.drop 51).take 7)
    (initialScratchStores mem scratch block 5) =
      .value (E6, initialScratchStores mem scratch block 6) at hex5
  change List.foldlM Instr.run E6 ((program.bb2.body.drop 58).take 7)
    (initialScratchStores mem scratch block 6) =
      .value (E7, initialScratchStores mem scratch block 7) at hex6
  change List.foldlM Instr.run E7 ((program.bb2.body.drop 65).take 7)
    (initialScratchStores mem scratch block 7) =
      .value (E8, initialScratchStores mem scratch block 8) at hex7
  dsimp only [E0, E1, E2, E3, E4, E5, E6, E7, E8] at hex0 hex1 hex2 hex3 hex4 hex5 hex6 hex7
  rw [hcut]
  simp only [List.foldlM_append, EffectM.bind_eq, hchain, LeanMLIR.RIR.PoisonOr.value_bind, hex0, hex1, hex2, hex3, hex4, hex5, hex6, hex7]
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run, EffectM.pure_eq, mlir_effect, initialBlockEnv, E0, E1, E2, E3, E4, E5, E6, E7, E8, block]

/-- The full imported initial block reaches bb4 after its eight real stores. -/
theorem initial_block_run (E : Env program.Γ) (mem : GlobalState)
    (chain data scratch : Pointer) (s : Spec.State)
    (h : InitialChainReady E chain) (hv : InitialVectorReady E data scratch)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hs : SmallRange mem.mem scratch 128) (hr : InitialChainReads mem.mem chain s)
    (hsep : (Range.of scratch 1024).Disjoint (Range.of data 1024)) :
    program.bb2.run program.blockParams E mem =
      .value ((initialGroupEnv (initialBlockEnv E chain data scratch s
        (readBytes mem.mem data 128)), .inr 4),
        initialScratchStores mem scratch (readBytes mem.mem data 128) 8) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    initial_block_body E mem chain data scratch s h hv hc hd hs hr hsep,
    LeanMLIR.RIR.PoisonOr.value_bind]
  exact initial_group_exit _ _

/-- A fully concrete initial-block endpoint: the public memory determines all
initial working words and message bytes. -/
theorem initial_block_run_unpack (E : Env program.Γ) (mem : GlobalState)
    (chain data scratch : Pointer)
    (h : InitialChainReady E chain) (hv : InitialVectorReady E data scratch)
    (hc : SmallRange mem.mem chain 64) (hd : SmallRange mem.mem data 128)
    (hs : SmallRange mem.mem scratch 128)
    (hsep : (Range.of scratch 1024).Disjoint (Range.of data 1024)) :
    program.bb2.run program.blockParams E mem =
      .value ((initialGroupEnv (initialBlockEnv E chain data scratch
        (Spec.unpack (mem.mem.readAt chain 512)) (readBytes mem.mem data 128)), .inr 4),
        initialScratchStores mem scratch (readBytes mem.mem data 128) 8) :=
  initial_block_run E mem chain data scratch _ h hv hc hd hs
    (initialChainReads_unpack mem.mem chain hc) hsep

end Agave.Ed25519.SHA512.Execution.Avx2
