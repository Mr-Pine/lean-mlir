import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkLoopStep
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkTest

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure BulkSeed (g : Globals) (E : Env program.Γ) (chain scratch cache : Pointer) : Prop where
  initial : BulkInitialReady E chain scratch cache
  constants : BulkInitialEntryReady g E
  tail : BulkTailSecondConstants E cache
  minusOne : E.read (%80) = .value 18446744073709551615#64
  byteZero : E.read (%48) = .value 0#8
  length : E.read (%49) = .value 512#64

theorem BulkSeed.of_frame {g : Globals} {E E' : Env program.Γ} {chain scratch cache : Pointer}
    (h : BulkSeed g E chain scratch cache) (hf : RegFrame 86 320 E E') :
    BulkSeed g E' chain scratch cache := by
  refine ⟨?_,h.constants.of_frame hf,?_,(hf.read (%80)).trans h.minusOne,
    (hf.read (%48)).trans h.byteZero,(hf.read (%49)).trans h.length⟩
  · refine ⟨?_,(hf.read (%83)).trans h.initial.scratchPtr,
      (hf.read (%82)).trans h.initial.cachePtr,(hf.read (%15)).trans h.initial.c64,
      (hf.read (%17)).trans h.initial.c80,(hf.read (%19)).trans h.initial.c96,
      (hf.read (%21)).trans h.initial.c112⟩
    exact ⟨(hf.read (%arg0)).trans h.initial.chainReady.ptr,
      (hf.read (%3)).trans h.initial.chainReady.c8,
      (hf.read (%4)).trans h.initial.chainReady.c16,
      (hf.read (%5)).trans h.initial.chainReady.c24,
      (hf.read (%6)).trans h.initial.chainReady.c32,
      (hf.read (%7)).trans h.initial.chainReady.c40,
      (hf.read (%8)).trans h.initial.chainReady.c48,
      (hf.read (%9)).trans h.initial.chainReady.c56⟩
  · exact ⟨(hf.read (%82)).trans h.tail.cache,(hf.read (%3)).trans h.tail.eight,
      (hf.read (%79)).trans h.tail.limit,(hf.read (%36)).trans h.tail.rot14,
      (hf.read (%37)).trans h.tail.rot18,(hf.read (%38)).trans h.tail.rot41,
      (hf.read (%39)).trans h.tail.rot28,(hf.read (%40)).trans h.tail.rot34,
      (hf.read (%41)).trans h.tail.rot39⟩

theorem bulkEntryEnv_seed (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (count : BitVec 64) (chain : Pointer) (hp : E.read (%arg0) = .value chain) :
    BulkSeed g (bulkEntryEnv g E mem count) chain
      ((mem.alloca 128).alloca 640).allocaPtr (mem.alloca 128).allocaPtr := by
  change E.args 0 = .value chain at hp
  refine ⟨?_,bulkEntryEnv_bulkInitialReady g E mem count,?_,?_,?_,?_⟩
  · constructor
    · constructor <;> simp [bulkEntryEnv,entryConstantsEnv,entryConstants0,entryConstants1,
        entryConstants2,mlir_env,hp]
    all_goals simp [bulkEntryEnv,entryConstantsEnv,entryConstants0,entryConstants1,
      entryConstants2,mlir_env]
  · constructor <;> simp [bulkEntryEnv,entryConstantsEnv,entryConstants0,entryConstants1,
      entryConstants2,mlir_env]
  all_goals simp [bulkEntryEnv,entryConstantsEnv,entryConstants0,entryConstants1,
      entryConstants2,mlir_env]

theorem BulkSeed.testReady {g : Globals} {E : Env program.Γ} {chain scratch cache : Pointer}
    (h : BulkSeed g E chain scratch cache) (count consumed : BitVec 64)
    (hc : E.read (%arg2) = .value count) (hi : E.read (%86) = .value consumed) :
    BulkTestReady E cache count consumed :=
  ⟨hc,hi,h.initial.cachePtr,h.constants.v47,h.byteZero,h.length,h.constants.v1,h.constants.v2⟩

theorem entryEnv_seed (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain : Pointer) (hp : E.read (%arg0) = .value chain) :
    BulkSeed g (entryEnv g E mem) chain
      ((mem.alloca 128).alloca 640).allocaPtr (mem.alloca 128).allocaPtr := by
  have hh := bulkEntryEnv_seed g E mem 1#64 chain hp
  simpa [bulkEntryEnv,entryEnv,bulkParity] using hh

end Agave.Ed25519.SHA512.Execution.Avx2
