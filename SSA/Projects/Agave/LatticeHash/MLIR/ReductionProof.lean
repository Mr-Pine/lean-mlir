import SSA.Projects.Agave.LatticeHash.MLIR.agave_add_u16_8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_add_u16_16
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.SLLVM.Dialect.Semantics.StepLemmas

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The two adjacent `u16` lanes of each source `u32` wrap independently. -/
def addLanes {n : Nat} (a b : BitVec (16 * n)) : Vector (BitVec 16) n :=
  Vector.ofFn fun i => a.extractLsb' (i.val * 16) 16 + b.extractLsb' (i.val * 16) 16

def addResult {n : Nat} (a b : BitVec (16 * n)) : BitVec (16 * n) :=
  BitVec.packLanes (addLanes a b)

private theorem add_unflatten {n : Nat} (a b : BitVec (16 * n)) :
    (Vector.ofFn fun i : Fin n =>
      InstCombine.binaryDenote (.add {nsw := false, nuw := false})
        (LLVM.Ty.ofVector (LLVM.Ty.unflatten (.vector n (.bitvec 16)) b))[i]
        (LLVM.Ty.ofVector (LLVM.Ty.unflatten (.vector n (.bitvec 16)) a))[i]) =
      (addLanes a b).map PoisonOr.value := by
  ext i hi
  simp [LLVM.Ty.unflatten, addLanes, InstCombine.binaryDenote, LLVM.add, LLVM.add?,
    BitVec.add_comm, LLVM.Ty.width]

private theorem flatten_values {n : Nat} (a : Vector (BitVec 16) n) :
    LLVM.Ty.flatten (.vector n (.bitvec 16)) (a.map PoisonOr.value) =
      .value (BitVec.packLanes a) := by
  have hd : LLVM.Ty.Defined (.vector n (.bitvec 16)) (a.map PoisonOr.value) := by
    intro i
    change (a.map PoisonOr.value)[i] ≠ .poison
    simpa using PoisonOr.value_ne_poison a[i]
  unfold LLVM.Ty.flatten
  rw [ite_eq_left hd]
  congr 1
  simp [LLVM.Ty.flattenBV, LLVM.Ty.ofVector, LLVM.Ty.ofBitvec]

private def reductionBody (n : Nat) (out a b : Pointer) : EffectM (HVector toType ([] : List SLLVM.Ty)) := do
  let av ← (liftM (SLLVM.load (.value a) (.vector n (.bitvec 16))) : EffectM _)
  let bv ← (liftM (SLLVM.load (.value b) (.vector n (.bitvec 16))) : EffectM _)
  let rv := Vector.ofFn fun i : Fin n =>
    InstCombine.binaryDenote (.add {nsw := false, nuw := false}) (LLVM.Ty.ofVector bv)[i] (LLVM.Ty.ofVector av)[i]
  let _ ← (liftM (SLLVM.store (.value out) (.vector n (.bitvec 16)) rv) : EffectM _)
  pure []ₕ

private theorem body_run (n : Nat) (out a b : Pointer) (s : GlobalState)
    (ab bb : LiveBlock) (ha : s.mem[a.id]? = some (.live ab))
    (hb : s.mem[b.id]? = some (.live bb))
    (hal : a.offsetInBits + 16 * n ≤ ab.lengthInBits)
    (hbl : b.offsetInBits + 16 * n ≤ bb.lengthInBits)
    (hout : Fits s.mem out (16 * n)) :
    StateT.run (reductionBody n out a b) s =
      .value ([]ₕ, { s with mem := s.mem.splice out (addResult
        (ab.bytes.extractLsb' a.offsetInBits (16 * n))
        (bb.bytes.extractLsb' b.offsetInBits (16 * n))) }) := by
  simp only [reductionBody, EffectM.run_bind,
    run_liftM (run_load (t := .vector n (.bitvec 16)) ha hal), PoisonOr.value_bind,
    run_liftM (run_load (t := .vector n (.bitvec 16)) hb hbl), add_unflatten]
  rw [run_liftM (run_store (flatten_values _) hout)]
  rfl

/-- Each lane of the stored bit pattern is exactly wrapping `u16` addition. -/
theorem addResult_lane {n : Nat} (a b : BitVec (16 * n)) (i : Fin n) :
    (addResult a b).extractLsb' (i.val * 16) 16 =
      a.extractLsb' (i.val * 16) 16 + b.extractLsb' (i.val * 16) 16 := by
  simp [addResult, BitVec.extractLsb'_packLanes, addLanes]

/-- A memory-level contract: the compiled function returns normally, replaces
only the output slice by the packed wrapping sums, and preserves all other
live blocks, the allocation counter, and globals. Both loads precede the
store, so the SLLVM contract also permits overlap; the compiler ABI's stronger
noalias and alignment obligations remain external to SLLVM. -/
def ReductionSpec (cfg : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [])
    (n : Nat) (out a b : Pointer) (s : GlobalState) (ab bb : LiveBlock) : Prop :=
  let result := addResult (ab.bytes.extractLsb' a.offsetInBits (16 * n))
    (bb.bytes.extractLsb' b.offsetInBits (16 * n))
  ∃ s' : GlobalState,
    StateT.run (runFunction (cfg.denote
      (Ctxt.Valuation.ofHVector [.value b, .value a, .value out]ₕ))) s = .value ([]ₕ, s') ∧
    s' ≈ { s with mem := s.mem.splice out result } ∧
    s'.alloc = s.alloc ∧ s'.globals = s.globals ∧
    ∀ q : BlockId, q ≠ out.id → s'.mem.live? q = s.mem.live? q

private theorem reduction_conforms
    (cfg : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [])
    (n : Nat) (out a b : Pointer) (s : GlobalState) (hs : s.WF)
    (ab bb : LiveBlock) (ha : s.mem[a.id]? = some (.live ab))
    (hb : s.mem[b.id]? = some (.live bb))
    (hal : a.offsetInBits + 16 * n ≤ ab.lengthInBits)
    (hbl : b.offsetInBits + 16 * n ≤ bb.lengthInBits)
    (hout : Fits s.mem out (16 * n))
    (hcode : cfg.denote (Ctxt.Valuation.ofHVector [.value b, .value a, .value out]ₕ) =
      reductionBody n out a b) : ReductionSpec cfg n out a b s ab bb := by
  let result := addResult (ab.bytes.extractLsb' a.offsetInBits (16 * n))
    (bb.bytes.extractLsb' b.offsetInBits (16 * n))
  have he : s.popFrame (s.mem.splice out result) ≈ { s with mem := s.mem.splice out result } :=
    (hs.splice (p := out) (x := result)).popFrame_equiv.symm
  refine ⟨s.popFrame (s.mem.splice out result), ?_, he, rfl, rfl, ?_⟩
  · rw [hcode]
    exact run_runFunction (body_run n out a b s ab bb ha hb hal hbl hout)
  · intro q hq
    exact (he.live q).trans (live?_splice_ne (Ne.symm hq))

/-- Execution refinement for the extracted 8-word backend's packed `u16` add. -/
theorem agave_add_u16_8_conforms (out a b : Pointer) (s : GlobalState) (hs : s.WF)
    (ab bb : LiveBlock) (ha : s.mem[a.id]? = some (.live ab))
    (hb : s.mem[b.id]? = some (.live bb))
    (hal : a.offsetInBits + 256 ≤ ab.lengthInBits)
    (hbl : b.offsetInBits + 256 ≤ bb.lengthInBits)
    (hout : Fits s.mem out 256) :
    ReductionSpec agave_add_u16_8 16 out a b s ab bb := by
  apply reduction_conforms agave_add_u16_8 16 out a b s hs ab bb ha hb hal hbl hout
  simp only [agave_add_u16_8, agave_add_u16_8.cfgEntry,
    Cfg.denote, BlockCom.denote, Terminator.denote, reductionBody,
    Expr.denote, DialectDenote.denote, simp_denote, simp_sllvm]
  dsimp
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  simp only [simp_spine, simp_denote, simp_sllvm]

/-- Execution refinement for the extracted 16-word backend's packed `u16` add. -/
theorem agave_add_u16_16_conforms (out a b : Pointer) (s : GlobalState) (hs : s.WF)
    (ab bb : LiveBlock) (ha : s.mem[a.id]? = some (.live ab))
    (hb : s.mem[b.id]? = some (.live bb))
    (hal : a.offsetInBits + 512 ≤ ab.lengthInBits)
    (hbl : b.offsetInBits + 512 ≤ bb.lengthInBits)
    (hout : Fits s.mem out 512) :
    ReductionSpec agave_add_u16_16 32 out a b s ab bb := by
  apply reduction_conforms agave_add_u16_16 32 out a b s hs ab bb ha hb hal hbl hout
  simp only [agave_add_u16_16, agave_add_u16_16.cfgEntry,
    Cfg.denote, BlockCom.denote, Terminator.denote, reductionBody,
    Expr.denote, DialectDenote.denote, simp_denote, simp_sllvm]
  dsimp
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  simp only [simp_spine, simp_denote, simp_sllvm]

end AgaveLatticeHash.MLIR
