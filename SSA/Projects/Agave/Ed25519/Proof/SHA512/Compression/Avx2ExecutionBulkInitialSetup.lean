import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialBlockChain
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkControl

/-! Exact read-only setup of the arbitrary-count two-block path, bb8. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false

structure BulkInitialReady (E : Env program.Γ) (chain scratch cache : Pointer) : Prop where
  chainReady : InitialChainReady E chain
  scratchPtr : E.read (%83) = .value scratch
  cachePtr : E.read (%82) = .value cache
  c64 : E.read (%15) = .value 64#64
  c80 : E.read (%17) = .value 80#64
  c96 : E.read (%19) = .value 96#64
  c112 : E.read (%21) = .value 112#64

/-- Precomputed destinations of the eight initial dual-cache stores. -/
structure BulkInitialPointers (E : Env program.Γ) (scratch cache : Pointer) : Prop where
  scratchPtr : E.read (%83) = .value scratch
  cachePtr : E.read (%82) = .value cache
  scratch1 : E.read (%321) = .value (scratch.add 16#64)
  cache1 : E.read (%322) = .value (cache.add 16#64)
  scratch2 : E.read (%323) = .value (scratch.add 32#64)
  cache2 : E.read (%324) = .value (cache.add 32#64)
  scratch3 : E.read (%325) = .value (scratch.add 48#64)
  cache3 : E.read (%326) = .value (cache.add 48#64)
  scratch4 : E.read (%327) = .value (scratch.add 64#64)
  cache4 : E.read (%328) = .value (cache.add 64#64)
  scratch5 : E.read (%329) = .value (scratch.add 80#64)
  cache5 : E.read (%330) = .value (cache.add 80#64)
  scratch6 : E.read (%331) = .value (scratch.add 96#64)
  cache6 : E.read (%332) = .value (cache.add 96#64)
  scratch7 : E.read (%333) = .value (scratch.add 112#64)
  cache7 : E.read (%334) = .value (cache.add 112#64)

def bulkInitialSetupEnv (E : Env program.Γ) (chain scratch cache : Pointer)
    (s : Spec.State) : Env program.Γ :=
  E[%321 := .value (scratch.add 16#64),
    %322 := .value (cache.add 16#64),
    %323 := .value (scratch.add 32#64),
    %324 := .value (cache.add 32#64),
    %325 := .value (scratch.add 48#64),
    %326 := .value (cache.add 48#64),
    %327 := .value (scratch.add 64#64),
    %328 := .value (cache.add 64#64),
    %329 := .value (scratch.add 80#64),
    %330 := .value (cache.add 80#64),
    %331 := .value (scratch.add 96#64),
    %332 := .value (cache.add 96#64),
    %333 := .value (scratch.add 112#64),
    %334 := .value (cache.add 112#64),
    %335 := .value (chain.add 8#64),
    %336 := .value (chain.add 16#64),
    %337 := .value (chain.add 24#64),
    %338 := .value (chain.add 32#64),
    %339 := .value (chain.add 40#64),
    %340 := .value (chain.add 48#64),
    %341 := .value (chain.add 56#64),
    %342 := .value s.a,
    %343 := .value s.b,
    %344 := .value s.c,
    %345 := .value s.d,
    %346 := .value s.e,
    %347 := .value s.f,
    %348 := .value s.g,
    %349 := .value s.h]

theorem bulk_initial_setup_body (E : Env program.Γ) (mem : GlobalState)
    (chain scratch cache : Pointer) (s : Spec.State)
    (h : BulkInitialReady E chain scratch cache)
    (hc : SmallRange mem.mem chain 64) (hs : SmallRange mem.mem scratch 128)
    (hcache : SmallRange mem.mem cache 640) (hr : InitialChainReads mem.mem chain s) :
    List.foldlM Instr.run E program.bb8.body mem =
      .value (bulkInitialSetupEnv E chain scratch cache s, mem) := by
  have hptr : E.args 0 = .value chain := h.chainReady.ptr
  have hs16 := hs.gep (k := 16) (by decide)
  have hs32 := hs.gep (k := 32) (by decide)
  have hs48 := hs.gep (k := 48) (by decide)
  have hs64 := hs.gep (k := 64) (by decide)
  have hs80 := hs.gep (k := 80) (by decide)
  have hs96 := hs.gep (k := 96) (by decide)
  have hs112 := hs.gep (k := 112) (by decide)
  have hcache16 := hcache.gep (k := 16) (by decide)
  have hcache32 := hcache.gep (k := 32) (by decide)
  have hcache48 := hcache.gep (k := 48) (by decide)
  have hcache64 := hcache.gep (k := 64) (by decide)
  have hcache80 := hcache.gep (k := 80) (by decide)
  have hcache96 := hcache.gep (k := 96) (by decide)
  have hcache112 := hcache.gep (k := 112) (by decide)
  have hc8 := hc.gep (k := 8) (by decide)
  have hc16 := hc.gep (k := 16) (by decide)
  have hc24 := hc.gep (k := 24) (by decide)
  have hc32 := hc.gep (k := 32) (by decide)
  have hc40 := hc.gep (k := 40) (by decide)
  have hc48 := hc.gep (k := 48) (by decide)
  have hc56 := hc.gep (k := 56) (by decide)
  have hf0 : Fits mem.mem chain 64 := by
    simpa only [Pointer.add_zero] using hc.fits_add (k := 0) (count := 8) (by decide)
  have hf8 := hc.fits_add (k := 8) (count := 8) (by decide)
  have hf16 := hc.fits_add (k := 16) (count := 8) (by decide)
  have hf24 := hc.fits_add (k := 24) (count := 8) (by decide)
  have hf32 := hc.fits_add (k := 32) (count := 8) (by decide)
  have hf40 := hc.fits_add (k := 40) (count := 8) (by decide)
  have hf48 := hc.fits_add (k := 48) (count := 8) (by decide)
  have hf56 := hc.fits_add (k := 56) (count := 8) (by decide)
  norm_num only at hs16 hs32 hs48 hs64 hs80 hs96 hs112 hcache16 hcache32 hcache48 hcache64 hcache80 hcache96 hcache112 hc8 hc16 hc24 hc32 hc40 hc48 hc56
  simp [program.bb8, List.foldlM_cons, List.foldlM_nil, Instr.run,
    bulkInitialSetupEnv, hptr, h.scratchPtr, h.cachePtr,
    h.chainReady.c8, h.chainReady.c16, h.chainReady.c24, h.chainReady.c32,
    h.chainReady.c40, h.chainReady.c48, h.chainReady.c56, h.c64, h.c80, h.c96, h.c112,
    hs16, hs32, hs48, hs64, hs80, hs96, hs112, hcache16, hcache32, hcache48, hcache64, hcache80, hcache96, hcache112, hc8, hc16, hc24, hc32, hc40, hc48, hc56,
    hf0, hf8, hf16, hf24, hf32, hf40, hf48, hf56,
    hr.a, hr.b, hr.c, hr.d, hr.e, hr.f, hr.g, hr.h,
    GepIndex.inboundsOffset, Operation.load,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

def bulkInitialOuterEnv (E : Env program.Γ) : Env program.Γ :=
  E[%350 := E.read (%349), %351 := E.read (%348),
    %352 := E.read (%347), %353 := E.read (%346),
    %354 := E.read (%345), %355 := E.read (%344),
    %356 := E.read (%343), %357 := E.read (%342),
    %358 := E.read (%86), %359 := E.read (%90)]

theorem bulk_initial_setup_run (E : Env program.Γ) (mem : GlobalState)
    (chain scratch cache : Pointer) (s : Spec.State)
    (h : BulkInitialReady E chain scratch cache)
    (hc : SmallRange mem.mem chain 64) (hs : SmallRange mem.mem scratch 128)
    (hcache : SmallRange mem.mem cache 640) (hr : InitialChainReads mem.mem chain s) :
    program.bb8.run program.blockParams E mem =
      .value ((bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s), .inr 9), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    bulk_initial_setup_body E mem chain scratch cache s h hc hs hcache hr,
    PoisonOr.value_bind]
  simp [program.bb8, Exit.run, Jump.run, bulkInitialOuterEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulk_initial_setup_pointers (E : Env program.Γ) (chain scratch cache : Pointer)
    (s : Spec.State) (h : BulkInitialReady E chain scratch cache) :
    BulkChainPointers (bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s)) chain ∧
    BulkInitialPointers (bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s)) scratch cache := by
  have hptr : E.args 0 = .value chain := h.chainReady.ptr
  constructor <;> constructor <;>
    simp [bulkInitialOuterEnv, bulkInitialSetupEnv, mlir_env,
      hptr, h.scratchPtr, h.cachePtr]

theorem bulk_initial_setup_ready (E : Env program.Γ) (chain scratch cache : Pointer)
    (s : Spec.State) (index pairs : BitVec 64)
    (hi : E.read (%86) = .value index) (hp : E.read (%90) = .value pairs) :
    BulkOuterReady (bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s)) s index pairs := by
  constructor <;> simp [bulkInitialOuterEnv, bulkInitialSetupEnv, mlir_env, hi, hp]

theorem bulkInitialSetupEnv_frame (E : Env program.Γ) (chain scratch cache : Pointer)
    (s : Spec.State) : RegFrame 321 349 E (bulkInitialSetupEnv E chain scratch cache s) := by
  unfold bulkInitialSetupEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulkInitialOuterEnv_frame (E : Env program.Γ) :
    RegFrame 350 359 E (bulkInitialOuterEnv E) := by
  unfold bulkInitialOuterEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

theorem bulk_initial_setup_frame (E : Env program.Γ) (chain scratch cache : Pointer)
    (s : Spec.State) :
    RegFrame 321 359 E (bulkInitialOuterEnv (bulkInitialSetupEnv E chain scratch cache s)) :=
  ((bulkInitialSetupEnv_frame _ _ _ _ _).enlarge (by decide) (by decide)).trans
    ((bulkInitialOuterEnv_frame _).enlarge (by decide) (by decide))

end Agave.Ed25519.SHA512.Execution.Avx2
