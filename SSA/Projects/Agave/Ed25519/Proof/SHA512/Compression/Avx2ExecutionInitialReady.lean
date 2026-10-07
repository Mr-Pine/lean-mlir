import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialBlock
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionEntry
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionReturn

/-! Typed entry invariants at the first imported pair-loop header. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Bridge.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem EntryReady.initial_chain {g : Globals} {E : Env program.Γ} {mem : GlobalState}
    (h : EntryReady g E mem) (chain : Pointer) (hp : E.read (%arg0) = .value chain) :
    InitialChainReady E chain :=
  ⟨hp, h.v3, h.v4, h.v5, h.v6, h.v7, h.v8, h.v9⟩

theorem EntryReady.initial_vector {g : Globals} {E : Env program.Γ} {mem : GlobalState}
    (h : EntryReady g E mem) (data : Pointer) (hp : E.read (%arg1) = .value data) :
    InitialVectorReady E data mem.allocaPtr := by
  constructor
  · exact hp
  · exact h.scratch
  · exact h.v11
  · exact h.v12
  · exact h.v13
  · exact h.v14
  · exact h.v16
  · exact h.v18
  · exact h.v20
  · exact h.v22

/-- The two actual simultaneous branch-argument maps following bb2. -/
def initialPairEnv (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) : Env program.Γ :=
  groupPairEnv (initialGroupEnv (initialBlockEnv E chain data scratch s block))

private theorem initialGroupEnv_frame (E : Env program.Γ) :
    RegFrame 92 190 E (initialGroupEnv E) := by
  unfold initialGroupEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initialGroupPairEnv_frame (E : Env program.Γ) :
    RegFrame 92 190 E (groupPairEnv E) := by
  unfold groupPairEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem initialPairEnv_frame (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    RegFrame 92 190 E (initialPairEnv E chain data scratch s block) :=
  (((initialBlockEnv_frame E chain data scratch s block).enlarge (by decide) (by decide)).trans
    (initialGroupEnv_frame _)).trans (initialGroupPairEnv_frame _)

/-- Entry constants and allocation pointers survive the initial loop setup. -/
theorem EntryReady.of_initial_frame {g : Globals} {E E' : Env program.Γ}
    {mem : GlobalState} (h : EntryReady g E mem) (hf : RegFrame 92 190 E E') :
    EntryReady g E' mem := by
  constructor
  · exact (hf.read (%0)).trans h.v0
  · exact (hf.read (%1)).trans h.v1
  · exact (hf.read (%2)).trans h.v2
  · exact (hf.read (%3)).trans h.v3
  · exact (hf.read (%4)).trans h.v4
  · exact (hf.read (%5)).trans h.v5
  · exact (hf.read (%6)).trans h.v6
  · exact (hf.read (%7)).trans h.v7
  · exact (hf.read (%8)).trans h.v8
  · exact (hf.read (%9)).trans h.v9
  · exact (hf.read (%10)).trans h.v10
  · exact (hf.read (%11)).trans h.v11
  · exact (hf.read (%12)).trans h.v12
  · exact (hf.read (%13)).trans h.v13
  · exact (hf.read (%14)).trans h.v14
  · exact (hf.read (%15)).trans h.v15
  · exact (hf.read (%16)).trans h.v16
  · exact (hf.read (%17)).trans h.v17
  · exact (hf.read (%18)).trans h.v18
  · exact (hf.read (%19)).trans h.v19
  · exact (hf.read (%20)).trans h.v20
  · exact (hf.read (%21)).trans h.v21
  · exact (hf.read (%22)).trans h.v22
  · exact (hf.read (%23)).trans h.v23
  · exact (hf.read (%24)).trans h.v24
  · exact (hf.read (%25)).trans h.v25
  · exact (hf.read (%26)).trans h.v26
  · exact (hf.read (%27)).trans h.v27
  · exact (hf.read (%28)).trans h.v28
  · exact (hf.read (%29)).trans h.v29
  · exact (hf.read (%30)).trans h.v30
  · exact (hf.read (%31)).trans h.v31
  · exact (hf.read (%32)).trans h.v32
  · exact (hf.read (%33)).trans h.v33
  · exact (hf.read (%34)).trans h.v34
  · exact (hf.read (%35)).trans h.v35
  · exact (hf.read (%36)).trans h.v36
  · exact (hf.read (%37)).trans h.v37
  · exact (hf.read (%38)).trans h.v38
  · exact (hf.read (%39)).trans h.v39
  · exact (hf.read (%40)).trans h.v40
  · exact (hf.read (%41)).trans h.v41
  · exact (hf.read (%42)).trans h.v42
  · exact (hf.read (%43)).trans h.v43
  · exact (hf.read (%44)).trans h.v44
  · exact (hf.read (%45)).trans h.v45
  · exact (hf.read (%46)).trans h.v46
  · exact (hf.read (%47)).trans h.v47
  · exact (hf.read (%48)).trans h.v48
  · exact (hf.read (%49)).trans h.v49
  · exact (hf.read (%50)).trans h.v50
  · exact (hf.read (%51)).trans h.v51
  · exact (hf.read (%52)).trans h.v52
  · exact (hf.read (%53)).trans h.v53
  · exact (hf.read (%54)).trans h.v54
  · exact (hf.read (%55)).trans h.v55
  · exact (hf.read (%56)).trans h.v56
  · exact (hf.read (%57)).trans h.v57
  · exact (hf.read (%58)).trans h.v58
  · exact (hf.read (%59)).trans h.v59
  · exact (hf.read (%60)).trans h.v60
  · exact (hf.read (%61)).trans h.v61
  · exact (hf.read (%62)).trans h.v62
  · exact (hf.read (%63)).trans h.v63
  · exact (hf.read (%64)).trans h.v64
  · exact (hf.read (%65)).trans h.v65
  · exact (hf.read (%66)).trans h.v66
  · exact (hf.read (%67)).trans h.v67
  · exact (hf.read (%68)).trans h.v68
  · exact (hf.read (%69)).trans h.v69
  · exact (hf.read (%70)).trans h.v70
  · exact (hf.read (%71)).trans h.v71
  · exact (hf.read (%72)).trans h.v72
  · exact (hf.read (%73)).trans h.v73
  · exact (hf.read (%74)).trans h.v74
  · exact (hf.read (%75)).trans h.v75
  · exact (hf.read (%76)).trans h.v76
  · exact (hf.read (%77)).trans h.v77
  · exact (hf.read (%78)).trans h.v78
  · exact (hf.read (%79)).trans h.v79
  · exact (hf.read (%80)).trans h.v80
  · exact (hf.read (%81)).trans h.scratch
  · exact (hf.read (%82)).trans h.cache
  · exact (hf.read (%83)).trans h.buffer
  · exact (hf.read (%84)).trans h.parity
  · exact (hf.read (%85)).trans h.branch

theorem initialPairEnv_entry (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem) :
    EntryReady g (initialPairEnv E chain data mem.allocaPtr s block) mem :=
  h.of_initial_frame (initialPairEnv_frame E chain data mem.allocaPtr s block)

private theorem initial_pair_read173 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%173) = B.read (%4) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read174 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%174) = B.read (%2) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read175 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%175) = B.read (%114) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read176 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%176) = B.read (%109) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read177 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%177) = B.read (%138) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read178 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%178) = B.read (%132) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read179 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%179) = B.read (%150) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read180 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%180) = B.read (%120) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read181 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%181) = B.read (%126) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read182 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%182) = B.read (%144) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read183 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%183) = B.read (%106) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read184 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%184) = B.read (%100) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read185 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%185) = B.read (%104) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read186 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%186) = B.read (%102) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read187 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%187) = B.read (%92) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read188 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%188) = B.read (%94) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read189 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%189) = B.read (%96) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read190 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%190) = B.read (%98) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read156 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%156) = B.read (%23) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_pair_read99 (B : Env program.Γ) :
    (groupPairEnv (initialGroupEnv B)).read (%99) = B.read (%99) := by
  simp [groupPairEnv, initialGroupEnv, mlir_env]

private theorem initial_slice_frame0 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 107 110 E (initialSlice0Env E data scratch block k0 k1) := by
  unfold initialSlice0Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame1 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 111 116 E (initialSlice1Env E data scratch block k0 k1) := by
  unfold initialSlice1Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame2 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 117 122 E (initialSlice2Env E data scratch block k0 k1) := by
  unfold initialSlice2Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame3 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 123 128 E (initialSlice3Env E data scratch block k0 k1) := by
  unfold initialSlice3Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame4 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 129 134 E (initialSlice4Env E data scratch block k0 k1) := by
  unfold initialSlice4Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame5 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 135 140 E (initialSlice5Env E data scratch block k0 k1) := by
  unfold initialSlice5Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame6 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 141 146 E (initialSlice6Env E data scratch block k0 k1) := by
  unfold initialSlice6Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_slice_frame7 (E : Env program.Γ) (data scratch : Pointer)
    (block : Bytes) (k0 k1 : Word) :
    RegFrame 147 152 E (initialSlice7Env E data scratch block k0 k1) := by
  unfold initialSlice7Env
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

private theorem initial_block_read109 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%109) = pairVec (readWordBE block 0) (readWordBE block 1) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%109)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%109)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%109)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%109)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%109)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%109)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%109)]
  simp [initialSlice0Env, mlir_env]

private theorem initial_block_read114 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%114) = pairVec (readWordBE block 2) (readWordBE block 3) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%114)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%114)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%114)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%114)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%114)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%114)]
  simp [initialSlice1Env, mlir_env]

private theorem initial_block_read120 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%120) = pairVec (readWordBE block 4) (readWordBE block 5) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%120)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%120)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%120)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%120)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%120)]
  simp [initialSlice2Env, mlir_env]

private theorem initial_block_read126 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%126) = pairVec (readWordBE block 6) (readWordBE block 7) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%126)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%126)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%126)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%126)]
  simp [initialSlice3Env, mlir_env]

private theorem initial_block_read132 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%132) = pairVec (readWordBE block 8) (readWordBE block 9) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%132)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%132)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%132)]
  simp [initialSlice4Env, mlir_env]

private theorem initial_block_read138 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%138) = pairVec (readWordBE block 10) (readWordBE block 11) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%138)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%138)]
  simp [initialSlice5Env, mlir_env]

private theorem initial_block_read144 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%144) = pairVec (readWordBE block 12) (readWordBE block 13) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%144)]
  simp [initialSlice6Env, mlir_env]

private theorem initial_block_read150 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%150) = pairVec (readWordBE block 14) (readWordBE block 15) := by
  unfold initialBlockEnv
  simp [initialSlice7Env, mlir_env]

private theorem initial_block_read92 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%92) = .value s.a := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%92)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%92)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read94 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%94) = .value s.b := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%94)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%94)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read96 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%96) = .value s.c := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%96)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%96)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read98 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%98) = .value s.d := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%98)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%98)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read100 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%100) = .value s.e := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%100)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%100)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read102 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%102) = .value s.f := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%102)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%102)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read104 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%104) = .value s.g := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%104)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%104)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read106 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%106) = .value s.h := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%106)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%106)]
  simp [initialChainEnv, mlir_env]

private theorem initial_block_read99 (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    (initialBlockEnv E chain data scratch s block).read (%99) = .value (chain.add 32#64) := by
  unfold initialBlockEnv
  rw [(initial_slice_frame7 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame6 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame5 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame4 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame3 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame2 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame1 _ _ _ _ _ _).read (%99)]
  rw [(initial_slice_frame0 _ _ _ _ _ _).read (%99)]
  simp [initialChainEnv, mlir_env]

macro "initial_pair_read" : tactic => `(tactic| (
  simp only [initialPairEnv, initial_pair_read173,initial_pair_read174,initial_pair_read175,initial_pair_read176,initial_pair_read177,initial_pair_read178,initial_pair_read179,initial_pair_read180,initial_pair_read181,initial_pair_read182,initial_pair_read183,initial_pair_read184,initial_pair_read185,initial_pair_read186,initial_pair_read187,initial_pair_read188,initial_pair_read189,initial_pair_read190,initial_pair_read156,initial_pair_read99]
  simp only [initial_block_read109,initial_block_read114,initial_block_read120,initial_block_read126,initial_block_read132,initial_block_read138,initial_block_read144,initial_block_read150,initial_block_read92,initial_block_read94,initial_block_read96,initial_block_read98,initial_block_read100,initial_block_read102,initial_block_read104,initial_block_read106,initial_block_read99]))

theorem initialPairEnv_window (E : Env program.Γ) (chain data scratch : Pointer)
    (s : Spec.State) (block : Bytes) :
    PairWindowReady (initialPairEnv E chain data scratch s block) (specWindow block 0) := by
  rw [← initialWindow_eq]
  constructor <;> (initial_pair_read; rfl)

theorem initialPairEnv_scalar (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem) :
    PairFirstReady (initialPairEnv E chain data mem.allocaPtr s block) mem.allocaPtr 0 s := by
  have h' := initialPairEnv_entry g E mem chain data s block h
  constructor
  · exact h'.scratch
  · simp only [initialPairEnv, initial_pair_read173,initial_pair_read174,initial_pair_read175,initial_pair_read176,initial_pair_read177,initial_pair_read178,initial_pair_read179,initial_pair_read180,initial_pair_read181,initial_pair_read182,initial_pair_read183,initial_pair_read184,initial_pair_read185,initial_pair_read186,initial_pair_read187,initial_pair_read188,initial_pair_read189,initial_pair_read190,initial_pair_read156,initial_pair_read99,
      (initialBlockEnv_frame E chain data mem.allocaPtr s block).read (%2), h.v2]
  · initial_pair_read
  · initial_pair_read
  · initial_pair_read
  · initial_pair_read
  · initial_pair_read
  · initial_pair_read
  · initial_pair_read
  · initial_pair_read
  · exact h'.v3
  · exact h'.v35
  · exact h'.v36
  · exact h'.v37
  · exact h'.v38
  · exact h'.v39
  · exact h'.v40
  · exact h'.v41

theorem initialPairEnv_schedule (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem) :
    PairScheduleReady (initialPairEnv E chain data mem.allocaPtr s block) g.address0 0 0 := by
  have h' := initialPairEnv_entry g E mem chain data s block h
  have hf := initialBlockEnv_frame E chain data mem.allocaPtr s block
  constructor
  · exact h'.v24
  · simp only [initialPairEnv, initial_pair_read173,initial_pair_read174,initial_pair_read175,initial_pair_read176,initial_pair_read177,initial_pair_read178,initial_pair_read179,initial_pair_read180,initial_pair_read181,initial_pair_read182,initial_pair_read183,initial_pair_read184,initial_pair_read185,initial_pair_read186,initial_pair_read187,initial_pair_read188,initial_pair_read189,initial_pair_read190,initial_pair_read156,initial_pair_read99, hf.read (%4), h.v4]
  · simp only [initialPairEnv, initial_pair_read173,initial_pair_read174,initial_pair_read175,initial_pair_read176,initial_pair_read177,initial_pair_read178,initial_pair_read179,initial_pair_read180,initial_pair_read181,initial_pair_read182,initial_pair_read183,initial_pair_read184,initial_pair_read185,initial_pair_read186,initial_pair_read187,initial_pair_read188,initial_pair_read189,initial_pair_read190,initial_pair_read156,initial_pair_read99, hf.read (%2), h.v2]
  · exact h'.v1
  · exact h'.v25
  · exact h'.v26
  · exact h'.v27
  · exact h'.v28
  · exact h'.v29
  · exact h'.v30
  · exact h'.v31
  · exact h'.v32
  · exact h'.v33
  · exact h'.v34

theorem initialPairEnv_ready (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem) :
    PairReady (initialPairEnv E chain data mem.allocaPtr s block) mem.allocaPtr g.address0
      0 0 (specWindow block 0) s :=
  ⟨initialPairEnv_schedule g E mem chain data s block h,
    initialPairEnv_window E chain data mem.allocaPtr s block,
    initialPairEnv_scalar g E mem chain data s block h,
    (initialPairEnv_entry g E mem chain data s block h).v42⟩

theorem initialPairEnv_group (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem) :
    GroupReady (initialPairEnv E chain data mem.allocaPtr s block) 0 := by
  have h' := initialPairEnv_entry g E mem chain data s block h
  constructor
  · simp only [initialPairEnv, initial_pair_read173,initial_pair_read174,initial_pair_read175,initial_pair_read176,initial_pair_read177,initial_pair_read178,initial_pair_read179,initial_pair_read180,initial_pair_read181,initial_pair_read182,initial_pair_read183,initial_pair_read184,initial_pair_read185,initial_pair_read186,initial_pair_read187,initial_pair_read188,initial_pair_read189,initial_pair_read190,initial_pair_read156,initial_pair_read99,
      (initialBlockEnv_frame E chain data mem.allocaPtr s block).read (%23), h.v23]
  · exact h'.v0
  · exact h'.v43

theorem initialPairEnv_loopConstants (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem) :
    PairLoopConstants (initialPairEnv E chain data mem.allocaPtr s block) := by
  have h' := initialPairEnv_entry g E mem chain data s block h
  exact ⟨h'.v2, h'.v15, h'.v17, h'.v44⟩

theorem initialPairEnv_feedForward (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem)
    (hp : E.read (%arg0) = .value chain) :
    FeedForwardReady (initialPairEnv E chain data mem.allocaPtr s block) chain := by
  have h' := initialPairEnv_entry g E mem chain data s block h
  constructor
  · exact ((initialPairEnv_frame E chain data mem.allocaPtr s block).read (%arg0)).trans hp
  · initial_pair_read
  · exact h'.v2
  · exact h'.v1
  · exact h'.v42
  · exact h'.v46

/-- The inherited return inputs, once the compression exit writes its count. -/
theorem initialPairEnv_return (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain data : Pointer) (s : Spec.State) (block : Bytes) (h : EntryReady g E mem)
    (hc : E.read (%arg2) = .value 1#64) :
    ReturnReady ((initialPairEnv E chain data mem.allocaPtr s block)[%86 := .value 1#64])
      (mem.alloca 128).allocaPtr := by
  have h' := initialPairEnv_entry g E mem chain data s block h
  have ha := ((initialPairEnv_frame E chain data mem.allocaPtr s block).read (%arg2)).trans hc
  change (initialPairEnv E chain data mem.allocaPtr s block).args 2 = .value 1#64 at ha
  constructor <;> simp [mlir_env, ha, h'.cache, h'.v47, h'.v48, h'.v49, h'.v1, h'.v2]

end Agave.Ed25519.SHA512.Execution.Avx2
