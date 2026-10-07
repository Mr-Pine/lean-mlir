import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddMemory
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleWords

/-! Exact positive-add intervals of the unchanged AVX2 table constructor. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Add
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice prepareConstants differenceConstants abdcVec)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
attribute [local implicit_reducible] Ty.width

def rowEnv (E : ⟪kernel.Γ⟫) (table : Pointer) (index : Fin 64) : ⟪kernel.Γ⟫ :=
  E[%804 := .value (BitVec.ofNat 64 (index.val+1)), %805 := .value (tableRow table index)]

theorem row_frame (E : ⟪kernel.Γ⟫) (table : Pointer) (index : Fin 64) :
    RegisterFrame 804 806 E (rowEnv E table index) := by
  unfold rowEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem row_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (table : Pointer) (index : Fin 64) (bytes : Nat)
    (ht : Reduce64.Execution.SmallRange s.mem table bytes)
    (hi : 160 * index.val + 160 ≤ bytes)
    (hpt : E.read (%360) = .value table)
    (hpi : E.read (%803) = .value (BitVec.ofNat 64 index.val))
    (hone : E.read (%22) = .value 1#64) :
    runSlice (kernel.bb2 p) E 0 4 s = .value (rowEnv E table index, s) := by
  have hscale := tableIndex_scale index
  have hgep := ht.gep (k := 160 * index.val) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hadd : Operation.add {nsw := true, nuw := true}
      (.value (BitVec.ofNat 64 index.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (index.val+1)) := by
    exact CacheScale.add_nat index.val 1 (by have := index.isLt; omega) (by decide)
  simp [runSlice, kernel.bb2, rowEnv, tableRow,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    mlir_env, hpt, hpi, hone, hscale, hgep, hadd]

def copyInput (s : GlobalState) (q : Scratch) (fixed : Pointer) : GlobalState :=
  {s with mem := copyPointBytes s.mem q.prepared fixed}

theorem copyInput_ready (s : GlobalState) (q : Scratch) (fixed cached : Pointer)
    (h : MemoryReady s q cached) : MemoryReady (copyInput s q fixed) q cached := by
  refine ⟨copyPointBytes_wf s q.prepared fixed h.wf, ?_, h.distinct⟩
  intro i
  exact copyPointBytes_live (h.live i) _ _

theorem copyInput_cached (s : GlobalState) (q : Scratch) (fixed cached : Pointer)
    (h : MemoryReady s q cached) :
    Avx2FieldMul.Execution.readBlocks (copyInput s q fixed).mem cached =
      Avx2FieldMul.Execution.readBlocks s.mem cached := by
  funext k
  have hn : q.prepared.id ≠ cached.id := h.ne 1 6 (by decide)
  simp only [Avx2FieldMul.Execution.readBlocks, copyInput,
    readAt_copyPointBytes_ne s.mem q.prepared fixed
      (cached.add (BitVec.ofNat 64 (32*k.val))) 256 hn]

theorem copyInput_read (s : GlobalState) (q : Scratch) (fixed : Pointer)
    (hp : Reduce64.Execution.SmallRange s.mem q.prepared 160)
    (hf : Reduce64.Execution.SmallRange s.mem fixed 160) :
    Avx2FieldMul.Execution.readBlocks (copyInput s q fixed).mem q.prepared =
      Avx2FieldMul.Execution.readBlocks s.mem fixed :=
  copyPointBytes_readBlocks s.mem q.prepared fixed hp hf

def resultState (s : GlobalState) (q : Scratch) (fixed : Pointer) (P C : Point) : GlobalState :=
  pipelineState (copyInput s q fixed) q false P C 7

theorem resultState_read (s : GlobalState) (q : Scratch) (fixed : Pointer) (P C : Point)
    (h : Reduce64.Execution.SmallRange s.mem q.output 160) :
    Avx2FieldMul.Execution.readBlocks (resultState s q fixed P C).mem q.output =
      packPoint (add P C) := by
  exact (result_read (copyInput s q fixed) q false P C
    (copyPointBytes_live h q.prepared fixed)).trans (congrArg packPoint (resultPoint_eq false P C))

theorem resultState_frame (s : GlobalState) (q : Scratch) (fixed : Pointer) (P C : Point)
    (h : s.WF) : OutputFrame q s (resultState s q fixed P C) := by
  have hp := pipelineState_frame (copyInput s q fixed) q false P C
    (copyPointBytes_wf s q.prepared fixed h) 7
  refine ⟨hp.allocation, hp.wellFormed, ?_, ?_⟩
  · intro ptr bytes hr
    exact hp.live ptr bytes (copyPointBytes_live hr q.prepared fixed)
  · intro ptr width hne
    exact (hp.read ptr width hne).trans
      (readAt_copyPointBytes_ne s.mem q.prepared fixed ptr width (hne 1))

end Agave.Ed25519.Tables.Avx2Constructor.Add
