import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSelectedCalls
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialMemory

/-! Deterministic continuation environments and combined memory frames for
all four selected serial paths. These expose the data needed by the loop
invariant instead of hiding the actual continuation behind an existential. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

def cached_subSelectedResult (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer)
    (magnitude : Fin 16) : ⟪serialKernel.Γ⟫ :=
  let converted := cached_subConvertResult (E[%39 := .value table]) temporary completed magnitude
  let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  (cached_subInput converted completed temporary table k)[%142 :=
    .value (table.add (BitVec.ofNat 64 (160 * k.val)))]

def cached_addSelectedResult (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer)
    (magnitude : Fin 16) : ⟪serialKernel.Γ⟫ :=
  let converted := cached_addConvertResult (E[%39 := .value table]) temporary completed magnitude
  let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  (cached_addInput converted completed temporary table k)[%143 :=
    .value (table.add (BitVec.ofNat 64 (160 * k.val)))]

def affine_subSelectedResult (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer)
    (magnitude : Fin 128) : ⟪serialKernel.Γ⟫ :=
  let converted := affine_subConvertResult (E[%29 := .value table]) temporary completed magnitude
  let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  (affine_subInput converted completed temporary table k)[%155 :=
    .value (table.add (BitVec.ofNat 64 (120 * k.val)))]

def affine_addSelectedResult (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer)
    (magnitude : Fin 128) : ⟪serialKernel.Γ⟫ :=
  let converted := affine_addConvertResult (E[%29 := .value table]) temporary completed magnitude
  let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  (affine_addInput converted completed temporary table k)[%156 :=
    .value (table.add (BitVec.ofNat 64 (120 * k.val)))]

theorem serial_cached_sub_converted_state (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hhelper : SerialContracts.BinaryPointContract p.call3 160
      SerialContracts.readCached SerialPoint.cachedSubCompleted)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 16)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 1280)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readCached s
      (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2)))))) :
    ∃ final : GlobalState,
      (serialKernel p g).runFrom (cached_subConvertInput
        (E[%39 := .value table]) temporary completed magnitude) 20 s =
          (serialKernel p g).runFrom (cached_subSelectedResult E temporary completed table magnitude) 26 final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = SerialPoint.cachedSubCompleted
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) ∧
      (∀ q bits, (Range.of q bits).Disjoint (Range.of completed 1280) →
        (Range.of q bits).Disjoint (Range.of temporary 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  let converted := completedState s temporary completed
  let selected := table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2)))
  have hrecord : Buffer converted.mem selected 160 :=
    (completedState_buffer htable temporary completed).slice _ _
      (by have := magnitude.isLt; omega)
  have hcache : SerialContracts.readCached converted selected = SerialContracts.readCached s selected :=
    completedState_readCached_ne s temporary completed selected
      (by simpa only [selected, Pointer.add_id] using htt)
  have hcacheBound : SerialPoint.PointBounded (SerialContracts.readCached converted selected) := by
    rw [hcache]
    exact hC
  obtain ⟨final, hcall, hframe, hpoint, hbound⟩ := hhelper converted completed temporary selected
    (completedState_wf s temporary completed hwf)
    (completedState_buffer hc temporary completed) (completedState_buffer ht temporary completed)
    hrecord (Range.disjoint_of_id_ne htc.symm)
    (Range.disjoint_of_id_ne (by simpa only [selected, Pointer.add_id] using hct))
    (completedState_pointTight s temporary completed ht hc htc hP) hcacheBound
  have hrun := serial_cached_sub_conversion_select p g hfield E temporary completed table magnitude
    s final hwf ht hc htable hcall
  dsimp only at hrun
  refine ⟨final, hrun, hframe, ?_, hbound, ?_⟩
  · rw [hpoint, completedState_readPoint s temporary completed ht hc htc hP, hcache]
  · intro q bits hdc hdt
    exact (hframe.readFrame q bits hdc).trans
      ((completedState_writesOnly s temporary completed hwf ht).readFrame q bits hdt)

theorem serial_cached_add_converted_state (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hhelper : SerialContracts.BinaryPointContract p.call5 160
      SerialContracts.readCached SerialPoint.cachedAddCompleted)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 16)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 1280)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readCached s
      (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2)))))) :
    ∃ final : GlobalState,
      (serialKernel p g).runFrom (cached_addConvertInput
        (E[%39 := .value table]) temporary completed magnitude) 21 s =
          (serialKernel p g).runFrom (cached_addSelectedResult E temporary completed table magnitude) 26 final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = SerialPoint.cachedAddCompleted
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) ∧
      (∀ q bits, (Range.of q bits).Disjoint (Range.of completed 1280) →
        (Range.of q bits).Disjoint (Range.of temporary 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  let converted := completedState s temporary completed
  let selected := table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2)))
  have hrecord : Buffer converted.mem selected 160 :=
    (completedState_buffer htable temporary completed).slice _ _
      (by have := magnitude.isLt; omega)
  have hcache : SerialContracts.readCached converted selected = SerialContracts.readCached s selected :=
    completedState_readCached_ne s temporary completed selected
      (by simpa only [selected, Pointer.add_id] using htt)
  have hcacheBound : SerialPoint.PointBounded (SerialContracts.readCached converted selected) := by
    rw [hcache]
    exact hC
  obtain ⟨final, hcall, hframe, hpoint, hbound⟩ := hhelper converted completed temporary selected
    (completedState_wf s temporary completed hwf)
    (completedState_buffer hc temporary completed) (completedState_buffer ht temporary completed)
    hrecord (Range.disjoint_of_id_ne htc.symm)
    (Range.disjoint_of_id_ne (by simpa only [selected, Pointer.add_id] using hct))
    (completedState_pointTight s temporary completed ht hc htc hP) hcacheBound
  have hrun := serial_cached_add_conversion_select p g hfield E temporary completed table magnitude
    s final hwf ht hc htable hcall
  dsimp only at hrun
  refine ⟨final, hrun, hframe, ?_, hbound, ?_⟩
  · rw [hpoint, completedState_readPoint s temporary completed ht hc htc hP, hcache]
  · intro q bits hdc hdt
    exact (hframe.readFrame q bits hdc).trans
      ((completedState_writesOnly s temporary completed hwf ht).readFrame q bits hdt)

theorem serial_affine_sub_converted_state (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hhelper : SerialContracts.BinaryPointContract p.call6 120
      SerialContracts.readAffineCached (fun P C : SerialPoint.LimbPoint => SerialPoint.affineSubCompleted P C.X C.Y C.T))
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 128)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 7680)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readAffineCached s
      (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2)))))) :
    ∃ final : GlobalState,
      (serialKernel p g).runFrom (affine_subConvertInput
        (E[%29 := .value table]) temporary completed magnitude) 27 s =
          (serialKernel p g).runFrom (affine_subSelectedResult E temporary completed table magnitude) 28 final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = (fun P C : SerialPoint.LimbPoint => SerialPoint.affineSubCompleted P C.X C.Y C.T)
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readAffineCached s (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) ∧
      (∀ q bits, (Range.of q bits).Disjoint (Range.of completed 1280) →
        (Range.of q bits).Disjoint (Range.of temporary 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  let converted := completedState s temporary completed
  let selected := table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2)))
  have hrecord : Buffer converted.mem selected 120 :=
    (completedState_buffer htable temporary completed).slice _ _
      (by have := magnitude.isLt; omega)
  have hcache : SerialContracts.readAffineCached converted selected = SerialContracts.readAffineCached s selected :=
    completedState_readAffineCached_ne s temporary completed selected
      (by simpa only [selected, Pointer.add_id] using htt)
  have hcacheBound : SerialPoint.PointBounded (SerialContracts.readAffineCached converted selected) := by
    rw [hcache]
    exact hC
  obtain ⟨final, hcall, hframe, hpoint, hbound⟩ := hhelper converted completed temporary selected
    (completedState_wf s temporary completed hwf)
    (completedState_buffer hc temporary completed) (completedState_buffer ht temporary completed)
    hrecord (Range.disjoint_of_id_ne htc.symm)
    (Range.disjoint_of_id_ne (by simpa only [selected, Pointer.add_id] using hct))
    (completedState_pointTight s temporary completed ht hc htc hP) hcacheBound
  have hrun := serial_affine_sub_conversion_select p g hfield E temporary completed table magnitude
    s final hwf ht hc htable hcall
  dsimp only at hrun
  refine ⟨final, hrun, hframe, ?_, hbound, ?_⟩
  · rw [hpoint, completedState_readPoint s temporary completed ht hc htc hP, hcache]
  · intro q bits hdc hdt
    exact (hframe.readFrame q bits hdc).trans
      ((completedState_writesOnly s temporary completed hwf ht).readFrame q bits hdt)

theorem serial_affine_add_converted_state (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hhelper : SerialContracts.BinaryPointContract p.call7 120
      SerialContracts.readAffineCached (fun P C : SerialPoint.LimbPoint => SerialPoint.affineAddCompleted P C.X C.Y C.T))
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 128)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 7680)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readAffineCached s
      (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2)))))) :
    ∃ final : GlobalState,
      (serialKernel p g).runFrom (affine_addConvertInput
        (E[%29 := .value table]) temporary completed magnitude) 29 s =
          (serialKernel p g).runFrom (affine_addSelectedResult E temporary completed table magnitude) 28 final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = (fun P C : SerialPoint.LimbPoint => SerialPoint.affineAddCompleted P C.X C.Y C.T)
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readAffineCached s (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) ∧
      (∀ q bits, (Range.of q bits).Disjoint (Range.of completed 1280) →
        (Range.of q bits).Disjoint (Range.of temporary 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  let converted := completedState s temporary completed
  let selected := table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2)))
  have hrecord : Buffer converted.mem selected 120 :=
    (completedState_buffer htable temporary completed).slice _ _
      (by have := magnitude.isLt; omega)
  have hcache : SerialContracts.readAffineCached converted selected = SerialContracts.readAffineCached s selected :=
    completedState_readAffineCached_ne s temporary completed selected
      (by simpa only [selected, Pointer.add_id] using htt)
  have hcacheBound : SerialPoint.PointBounded (SerialContracts.readAffineCached converted selected) := by
    rw [hcache]
    exact hC
  obtain ⟨final, hcall, hframe, hpoint, hbound⟩ := hhelper converted completed temporary selected
    (completedState_wf s temporary completed hwf)
    (completedState_buffer hc temporary completed) (completedState_buffer ht temporary completed)
    hrecord (Range.disjoint_of_id_ne htc.symm)
    (Range.disjoint_of_id_ne (by simpa only [selected, Pointer.add_id] using hct))
    (completedState_pointTight s temporary completed ht hc htc hP) hcacheBound
  have hrun := serial_affine_add_conversion_select p g hfield E temporary completed table magnitude
    s final hwf ht hc htable hcall
  dsimp only at hrun
  refine ⟨final, hrun, hframe, ?_, hbound, ?_⟩
  · rw [hpoint, completedState_readPoint s temporary completed ht hc htc hP, hcache]
  · intro q bits hdc hdt
    exact (hframe.readFrame q bits hdc).trans
      ((completedState_writesOnly s temporary completed hwf ht).readFrame q bits hdt)

end Agave.Ed25519.DoubleBase.RIR
