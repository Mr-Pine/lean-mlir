import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.CFGSlice

/-! Execute the original successor-record stores and loop exit. The value of
the five cache vectors is exposed; their arithmetic refinement is separate. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.LoopTail
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open Avx2FieldMul.Execution (Blocks storeBlocks)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def input (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  E[%195 := .value 160#64, %196 := .value 192#64, %197 := .value 224#64,
    %198 := .value 256#64, %199 := .value 288#64, %350 := .value 7#64,
    %804 := .value (BitVec.ofNat 64 (i.val + 1)), %805 := .value r,
    %1021 := Ty.wrap (v 0), %1022 := Ty.wrap (v 1), %1023 := Ty.wrap (v 2),
    %1024 := Ty.wrap (v 3), %1025 := Ty.wrap (v 4)]

def result (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  (input E r v i)[%1026 := .value (r.add 160#64), %1027 := .value (r.add 192#64),
    %1028 := .value (r.add 224#64), %1029 := .value (r.add 256#64),
    %1030 := .value (r.add 288#64), %1031 := .value (if i.val = 6 then 1#1 else 0#1)]

/-- The exact source store order, relative to the current record. -/
def stores (m : MemoryState) (r : Pointer) (v : Blocks) : MemoryState :=
  let m := m.storeAt (r.add 160#64) (BitVec.packLanes (v 0))
  let m := m.storeAt (r.add 192#64) (BitVec.packLanes (v 1))
  let m := m.storeAt (r.add 224#64) (BitVec.packLanes (v 2))
  let m := m.storeAt (r.add 256#64) (BitVec.packLanes (v 3))
  let m := m.storeAt (r.add 288#64) (BitVec.packLanes (v 4))
  m

theorem stores_eq (m : MemoryState) (r : Pointer) (v : Blocks) :
    stores m r v = storeBlocks m (r.add 160#64) v := by
  simp [stores, storeBlocks, Pointer.add_add]

/-- A pair of records is sufficient for every inbounds promise in this suffix. -/
theorem body (p : Primitives) (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks)
    (i : Fin 7) (s : GlobalState) (hr : SmallRange s.mem r 320) :
    (kernel.bb2 p).runBodyFrom (input E r v i) 250 s =
      .value (result E r v i, {s with mem := stores s.mem r v}) := by
  have hg0 := hr.gep (k := 160) (by decide)
  have hf0 := hr.fits_add (k := 160) (count := 32) (by decide)
  have hr1 := hr.storeAt (r.add 160#64) (BitVec.packLanes (v 0))
  have hg1 := hr1.gep (k := 192) (by decide)
  have hf1 := hr1.fits_add (k := 192) (count := 32) (by decide)
  have hr2 := hr1.storeAt (r.add 192#64) (BitVec.packLanes (v 1))
  have hg2 := hr2.gep (k := 224) (by decide)
  have hf2 := hr2.fits_add (k := 224) (count := 32) (by decide)
  have hr3 := hr2.storeAt (r.add 224#64) (BitVec.packLanes (v 2))
  have hg3 := hr3.gep (k := 256) (by decide)
  have hf3 := hr3.fits_add (k := 256) (count := 32) (by decide)
  have hr4 := hr3.storeAt (r.add 256#64) (BitVec.packLanes (v 3))
  have hg4 := hr4.gep (k := 288) (by decide)
  have hf4 := hr4.fits_add (k := 288) (count := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hg0 hg1 hg2 hg3 hg4
  have hc := (ConstructorMemory.cursor_arithmetic i).2.1
  simp [BasicBlock.runBodyFrom, kernel.bb2, input, result, stores,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, Operation.store,
    Ty.flatten_wrap_vec, EffectM.bind_eq, EffectM.pure_eq,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    mlir_effect, mlir_env, throwUBIf, hc,hg0, hf0, hg1, hf1, hg2, hf2, hg3, hf3, hg4, hf4]

/-- The final successor test uses the exact bounded constructor cursor. -/
theorem exit (p : Primitives) (E : ⟪kernel.Γ⟫) (r : Pointer) (v : Blocks)
    (i : Fin 7) (s : GlobalState) :
    (kernel.bb2 p).exit.run kernel.blockParams (result E r v i) s =
      .value ((if i.val = 6 then result E r v i
        else (result E r v i)[%803 := .value (BitVec.ofNat 64 (i.val + 1))],
        .inr (if i.val = 6 then 1 else 2)), s) := by
  fin_cases i <;> simp [kernel.bb2, Exit.run, Jump.run, kernel.blockParams,
    result, input, mlir_env, EffectM.pure_eq]
  all_goals rfl

/-- The common outer table allocation proves the adjacent record view for all
seven constructor iterations, including the last. -/
theorem records (h : SmallRange m table 1280) (i : Fin 7) :
    SmallRange m (table.add (BitVec.ofNat 64 (160 * i.val))) 320 := by
  exact NAF.Memory.Buffer.slice h _ _ (by have := i.isLt; omega)

/-- The suffix preserves the allocation invariant and every old live range. -/
theorem frame (s : GlobalState) (r : Pointer) (v : Blocks) (hwf : s.WF) :
    ({s with mem := stores s.mem r v} : GlobalState).WF ∧
      ∀ q bytes, SmallRange s.mem q bytes → SmallRange (stores s.mem r v) q bytes := by
  rw [stores_eq]
  exact ⟨Avx2FieldMul.Execution.storeBlocks_wf _ _ _ hwf,
    fun _ _ h => Avx2FieldMul.Execution.storeBlocks_smallRange h _ _⟩

/-- Each byte outside the successor record is preserved, including other
records in the same table allocation. -/
theorem read_frame (m : MemoryState) (r q : Pointer) (v : Blocks) (width : Nat)
    (hr : SmallRange m r 320)
    (hdisjoint : (Range.of (r.add 160#64) 1280).Disjoint (Range.of q width)) :
    (stores m r v).readAt q width = m.readAt q width := by
  have hbase := Pointer.offsetInBits_add (hr.no_wrap (k := 160) (by decide))
  norm_num only [BitVec.toNat_ofNat] at hbase
  have hd (k : Fin 5) :
      (Range.of (r.add (BitVec.ofNat 64 (160 + 32 * k.val))) 256).Disjoint
        (Range.of q width) := by
    have hk := k.isLt
    have ho := Pointer.offsetInBits_add
      (hr.no_wrap (k := 160 + 32 * k.val) (by omega))
    have hsmall : 160 + 32 * k.val < 2^64 := by norm_num; omega
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at ho
    simp only [Range.Disjoint, Range.of, Pointer.add_id] at hdisjoint ⊢
    rw [hbase] at hdisjoint
    rw [ho]
    clear ho hbase
    rcases hdisjoint with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  have hd0 := hd 0
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  have hd4 := hd 4
  norm_num only [Fin.val_ofNat_lit, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod] at hd0 hd1 hd2 hd3 hd4
  dsimp only [stores]
  rw [MemoryState.readAt_storeAt_disjoint hd4,
    MemoryState.readAt_storeAt_disjoint hd3,
    MemoryState.readAt_storeAt_disjoint hd2,
    MemoryState.readAt_storeAt_disjoint hd1,
    MemoryState.readAt_storeAt_disjoint hd0]

/-- The successor record reads back exactly the five values supplied to the
actual stores. No premise assumes contents of any output byte. -/
theorem readback (m : MemoryState) (r : Pointer) (v : Blocks)
    (hr : SmallRange m r 320) :
    Avx2FieldMul.Execution.readBlocks (stores m r v) (r.add 160#64) = v := by
  rw [stores_eq]
  exact Avx2PointAdd.Phases.readBlocks_storeBlocks _ _ _
    (NAF.Memory.Buffer.slice hr 160 160 (by decide))

end Agave.Ed25519.Tables.Avx2Constructor.LoopTail
