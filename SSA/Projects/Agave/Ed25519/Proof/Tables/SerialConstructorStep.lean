import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorState

/-! The runtime successor is the actual cached-add call, four imported field
multiplications, inline cache conversion, and physical record transfer. -/
namespace Agave.Ed25519.Tables.SerialConstructorStep
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.SerialContracts (WritesOnly readPoint readCached)
open DoubleBase.RIR (completedState completedState_readPoint completedState_writesOnly)
open SerialConstructorState
open SerialConstructorArithmetic (entries)

abbrev record (table : Pointer) (k : Nat) := table.add (BitVec.ofNat 64 (160*k))

def nextState (g : SerialConstructor.Globals) (slots : Slots) (table : Pointer)
    (k : Fin 7) (u : GlobalState) : GlobalState :=
  let v := completedState u (slots 3) (slots 2)
  let w := SerialCacheExecution.cacheState v (slots 4) (slots 3) g.address0
  copyRecord w (record table (k.val+1)) (slots 4)

/-- One real successor establishes the recurrence for the complete new record
and preserves all preceding records and the fixed doubled point. -/
theorem next_state (g : SerialConstructor.Globals) (slots : Slots) (table : Pointer)
    (k : Fin 7) (s : GlobalState) (A : SerialPoint.LimbPoint)
    (hA : SerialPoint.PointTight A) (hs : Ready g slots table s)
    (hd : readPoint s (slots 5) = SerialConstructorArithmetic.double A)
    (he : ∀ j : Fin 8, j.val ≤ k.val → readCached s (record table j.val) = entries A j.val) :
    ∃ u,
      SerialPoint.cached_add.call (.cons (.value (slots 2)) (.cons (.value (slots 5))
        (.cons (.value (record table k.val)) .nil))) s = .value (.nil, u) ∧
      WritesOnly (slots 2) 160 s u ∧
      Ready g slots table u ∧
      let t := nextState g slots table k u
      Frame slots table s t ∧ Ready g slots table t ∧
      readPoint t (slots 5) = SerialConstructorArithmetic.double A ∧
      ∀ j : Fin 8, j.val ≤ k.val+1 → readCached t (record table j.val) = entries A j.val := by
  have hrec : Buffer s.mem (record table k.val) 160 :=
    hs.tableBuffer.slice _ _ (by have := k.isLt; omega)
  have hentry := he ⟨k.val, by have := k.isLt; omega⟩ (show k.val ≤ k.val from le_refl _)
  have hD : SerialPoint.PointTight (readPoint s (slots 5)) := by
    rw [hd]; exact SerialPoint.double_tight _ hA
  have hC : SerialPoint.PointBounded (readCached s (record table k.val)) := by
    rw [hentry]; exact SerialConstructorArithmetic.entries_bounded _ hA _
  obtain ⟨u, hcall, hu, hread, hbound⟩ := SerialPoint.Execution.cached_add_contract
    s (slots 2) (slots 5) (record table k.val) hs.wf
    (hs.point 2 (by decide)) (hs.point 5 (by decide)) hrec
    (Range.disjoint_of_id_ne (hs.separate 2 5 (by decide)))
    (Range.disjoint_of_id_ne (by simpa only [record, Pointer.add_id] using hs.separateTable 2)) hD hC
  have hfu : Frame slots table s u := Frame.slot 2 hu
  have hru := hs.preserve hfu
  let v := completedState u (slots 3) (slots 2)
  have hv : WritesOnly (slots 3) 160 u v :=
    completedState_writesOnly u (slots 3) (slots 2) hru.wf (hru.point 3 (by decide))
  have hrv := hru.preserve (Frame.slot 3 hv)
  have hpv : readPoint v (slots 3) = SerialPoint.asExtended
      (SerialPoint.cachedAddCompleted (SerialConstructorArithmetic.double A) (entries A k.val)) := by
    rw [completedState_readPoint u (slots 3) (slots 2) (hru.point 3 (by decide))
      (hru.point 2 (by decide)) (hs.separate 3 2 (by decide)) hbound,
      hread, hd, hentry]
  have hpvt : SerialPoint.PointTight (readPoint v (slots 3)) := by
    rw [hpv]
    exact SerialPoint.cachedAdd_tight _ _ (SerialPoint.double_tight A hA)
      (SerialConstructorArithmetic.entries_bounded A hA k.val)
  let w := SerialCacheExecution.cacheState v (slots 4) (slots 3) g.address0
  have hw : WritesOnly (slots 4) 160 v w := SerialCacheExecution.cacheState_writesOnly
    v (slots 4) (slots 3) g.address0 hrv.wf (hrv.point 4 (by decide))
  have hrw := hrv.preserve (Frame.slot 4 hw)
  have hcw : readCached w (slots 4) = entries A (k.val+1) := by
    rw [SerialCacheExecution.cacheState_readCached g v (slots 4) (slots 3)
      (hrv.point 4 (by decide)) (hrv.point 3 (by decide)) hrv.globalReady hpvt, hpv]
    rfl
  let t := copyRecord w (record table (k.val+1)) (slots 4)
  have ht : WritesOnly (record table (k.val+1)) 160 w t := copyRecord_frame hrw.wf
  have hft : Frame slots table w t := Frame.tableWrite ht (by simp [record])
  have hrt := hrw.preserve hft
  refine ⟨u, hcall, hu, hru, hfu.trans ((Frame.slot 3 hv).trans ((Frame.slot 4 hw).trans hft)), hrt, ?_, ?_⟩
  · change readPoint t (slots 5) = _
    rw [point_read_ne ht (by simpa only [record, Pointer.add_id] using (hs.separateTable 5).symm),
      point_read_ne hw (hs.separate 4 5 (by decide)),
      point_read_ne hv (hs.separate 3 5 (by decide)),
      point_read_ne hu (hs.separate 2 5 (by decide)), hd]
  · intro j hj
    change readCached t (record table j.val) = _
    by_cases hn : j.val = k.val+1
    · rw [hn, copyRecord_readCached w (record table (k.val+1)) (slots 4)
        (hrw.tableBuffer.slice _ _ (by have := k.isLt; omega)) (hrw.point 4 (by decide)), hcw]
    · have hjk : j.val ≤ k.val := by omega
      have hdis : (Range.of (record table j.val) 1280).Disjoint
          (Range.of (record table (k.val+1)) 1280) :=
        SerialPoint.Execution.subranges_disjoint hrw.tableBuffer
          (i := 160*j.val) (ni := 160) (j := 160*(k.val+1)) (nj := 160)
          (by have := j.isLt; omega) (by have := k.isLt; omega) (by omega)
      rw [cached_read_frame ht (hrw.tableBuffer.slice _ _ (by have := j.isLt; omega)) hdis,
        cached_read_ne hw (by simpa only [record, Pointer.add_id] using hs.separateTable 4),
        cached_read_ne hv (by simpa only [record, Pointer.add_id] using hs.separateTable 3),
        cached_read_ne hu (by simpa only [record, Pointer.add_id] using hs.separateTable 2)]
      exact he j hjk

end Agave.Ed25519.Tables.SerialConstructorStep
