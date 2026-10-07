import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLadderState

/-! Each signed arithmetic path of the serial loop is executed and restores
its concrete register, memory, limb-bound and group-representation invariants. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (readPoint readProjective readCached readAffineCached)
set_option maxRecDepth 10000

structure SerialCompletedAt (slots : Fin 7 → Pointer) (s : GlobalState) (V : GroupPoint) : Prop where
  bounded : SerialPoint.PointBounded (readPoint s (slots 5))
  represents : Tables.Represents (SerialPoint.pointValue (SerialPoint.asExtended (readPoint s (slots 5)))) V

structure SerialProjectiveAt (slots : Fin 7 → Pointer) (s : GlobalState) (V : GroupPoint) : Prop where
  tight : SerialPoint.PointTight (readProjective s (slots 6))
  represents : ProjectiveRepresents (readProjective s (slots 6)) V

theorem nafMagnitude_positive_coefficient (w n i : Nat) (hw : NAF.Supported w)
    (hpos : 0 < nafDigits w n i) :
    ((2 * ((nafMagnitude w n i hw).val / 2) + 1 : Nat) : Int) = nafDigits w n i := by
  have hodd := (NAF.digits_bounds w hw 256 0 ⟨n, 0⟩ (by norm_num) i).2.2
  change nafDigits w n i = 0 ∨ nafDigits w n i % 2 = 1 at hodd
  have habs := Int.natAbs_of_nonneg (le_of_lt hpos)
  change ((2 * ((nafDigits w n i).natAbs / 2) + 1 : Nat) : Int) = _
  rcases hodd with hz | hodd <;> omega

theorem nafMagnitude_negative_coefficient (w n i : Nat) (hw : NAF.Supported w)
    (hneg : nafDigits w n i < 0) :
    -((2 * ((nafMagnitude w n i hw).val / 2) + 1 : Nat) : Int) = nafDigits w n i := by
  have hodd := (NAF.digits_bounds w hw 256 0 ⟨n, 0⟩ (by norm_num) i).2.2
  change nafDigits w n i = 0 ∨ nafDigits w n i % 2 = 1 at hodd
  have habs := Int.ofNat_natAbs_of_nonpos (le_of_lt hneg)
  change -((2 * ((nafDigits w n i).natAbs / 2) + 1 : Nat) : Int) = _
  rcases hodd with hz | hodd <;> omega

theorem doubleCompleted_projective_represents (P : SerialPoint.LimbPoint) (V : GroupPoint)
    (ht : SerialPoint.PointTight P) (h : ProjectiveRepresents P V) :
    Tables.Represents (SerialPoint.pointValue (SerialPoint.asExtended (SerialPoint.doubleCompleted P))) (V + V) := by
  rw [SerialPoint.double_value P ht]
  obtain ⟨Q, hQ, hX, hY, hZ⟩ := h
  have heq : PointArithmetic.serialDouble (SerialPoint.pointValue P) = PointArithmetic.serialDouble Q := by
    unfold PointArithmetic.serialDouble
    rw [hX, hY, hZ]
    rfl
  rw [heq]
  exact Tables.represents_serialDouble hQ

variable {p : SerialCFG.Primitives} {g : SerialCFG.Globals} {slots : Fin 7 → Pointer}
  {tableA tableB da db : Pointer} {a b : Nat} {A B V : GroupPoint}
  {E : ⟪serialKernel.Γ⟫} {s : GlobalState} {i : Fin 256}

theorem serial_ladder_cached_sub (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialCompletedAt slots s V)
    (hdigit : E.read (%133) = .value (Execution.nafByte 5 a i.val))
    (hsign : nafDigits 5 a i.val < 0) :
    ∃ E' s', (serialKernel p g).runFrom E 20 s = (serialKernel p g).runFrom E' 26 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialCompletedAt slots s' (V + nafDigits 5 a i.val • A) ∧ E'.args = E.args := by
  let magnitude : Fin 16 := nafMagnitude 5 a i.val (Or.inl rfl)
  let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have ht : Buffer s.mem (slots 3) 160 := by simpa [serialScratchBytes] using hm.scratch 3
  have hc : Buffer s.mem (slots 5) 160 := by simpa [serialScratchBytes] using hm.scratch 5
  have hd : E.read (%133) = .value (-BitVec.ofNat 8 magnitude.val) := by
    rw [hdigit, nafByte_negative 5 a i.val (Or.inl rfl) hsign]
  have hconv := completedState_writesOnly s (slots 3) (slots 5) hm.wellFormed ht
  obtain ⟨final, hrun, hframe, hread, hbound, _⟩ := serial_cached_sub_converted_state p g
    hh.multiply hh.cachedSub E (slots 3) (slots 5) tableA magnitude s hm.wellFormed
    ht hc hm.tableABuffer (hm.separate 3 5 (by decide)) (hm.separateA 3) (hm.separateA 5)
    hP.bounded (hm.cachedA k).1
  rw [Env.write_of_read E (%39) hr.r39, cached_subConvertInput_of_registers hr magnitude hd] at hrun
  have hf := (SerialScratchFrame.of_writesOnly 3 hconv).trans
    (SerialScratchFrame.of_writesOnly 5 hframe)
  have he := cached_subSelectedResult_frame hr magnitude hd
  refine ⟨_, final, hrun, hr.of_frame (he.weaken_serial (by decide)),
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hi,
    hm.preserve hf, hf, ⟨hbound, ?_⟩, he.1⟩
  rw [hread]
  obtain ⟨Q, hQ, hC⟩ := (hm.cachedA k).2
  have hrep := SerialPoint.cachedSubCompleted_represents _ _ (SerialPoint.asExtended_tight _ hP.bounded)
    (hm.cachedA k).1 hP.represents hQ hC
  have hcoef := nafMagnitude_negative_coefficient 5 a i.val (Or.inl rfl) hsign
  change -((2*k.val+1 : Nat) : Int) = nafDigits 5 a i.val at hcoef
  rw [sub_eq_add_neg, ← natCast_zsmul, ← neg_zsmul, hcoef] at hrep
  exact hrep

theorem serial_ladder_cached_add (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialCompletedAt slots s V)
    (hdigit : E.read (%133) = .value (Execution.nafByte 5 a i.val))
    (hsign : 0 < nafDigits 5 a i.val) :
    ∃ E' s', (serialKernel p g).runFrom E 21 s = (serialKernel p g).runFrom E' 26 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialCompletedAt slots s' (V + nafDigits 5 a i.val • A) ∧ E'.args = E.args := by
  let magnitude : Fin 16 := nafMagnitude 5 a i.val (Or.inl rfl)
  let k : Fin 8 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have ht : Buffer s.mem (slots 4) 160 := by simpa [serialScratchBytes] using hm.scratch 4
  have hc : Buffer s.mem (slots 5) 160 := by simpa [serialScratchBytes] using hm.scratch 5
  have hd : E.read (%133) = .value (BitVec.ofNat 8 magnitude.val) := by
    rw [hdigit, nafByte_positive 5 a i.val (Or.inl rfl) (le_of_lt hsign)]
  have hconv := completedState_writesOnly s (slots 4) (slots 5) hm.wellFormed ht
  obtain ⟨final, hrun, hframe, hread, hbound, _⟩ := serial_cached_add_converted_state p g
    hh.multiply hh.cachedAdd E (slots 4) (slots 5) tableA magnitude s hm.wellFormed
    ht hc hm.tableABuffer (hm.separate 4 5 (by decide)) (hm.separateA 4) (hm.separateA 5)
    hP.bounded (hm.cachedA k).1
  rw [Env.write_of_read E (%39) hr.r39, cached_addConvertInput_of_registers hr magnitude hd] at hrun
  have hf := (SerialScratchFrame.of_writesOnly 4 hconv).trans
    (SerialScratchFrame.of_writesOnly 5 hframe)
  have he := cached_addSelectedResult_frame hr magnitude hd
  refine ⟨_, final, hrun, hr.of_frame (he.weaken_serial (by decide)),
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hi,
    hm.preserve hf, hf, ⟨hbound, ?_⟩, he.1⟩
  rw [hread]
  obtain ⟨Q, hQ, hC⟩ := (hm.cachedA k).2
  have hrep : Tables.Represents (SerialPoint.pointValue (SerialPoint.asExtended
      (SerialPoint.cachedAddCompleted (SerialPoint.asExtended (readPoint s (slots 5)))
        (readCached s (tableA.add (BitVec.ofNat 64 (160*k.val)))))))
      (V + (2*k.val+1) • A) := by
    rw [SerialPoint.cachedAdd_value _ _ (SerialPoint.asExtended_tight _ hP.bounded)
      (hm.cachedA k).1, hC]
    exact Tables.represents_serialAdd hP.represents hQ
  have hcoef := nafMagnitude_positive_coefficient 5 a i.val (Or.inl rfl) hsign
  change ((2*k.val+1 : Nat) : Int) = nafDigits 5 a i.val at hcoef
  rw [← natCast_zsmul, hcoef] at hrep
  exact hrep

theorem serial_ladder_affine_sub (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialCompletedAt slots s V)
    (hdigit : E.read (%145) = .value (Execution.nafByte 8 b i.val))
    (hsign : nafDigits 8 b i.val < 0) :
    ∃ E' s', (serialKernel p g).runFrom E 27 s = (serialKernel p g).runFrom E' 28 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialCompletedAt slots s' (V + nafDigits 8 b i.val • B) ∧ E'.args = E.args := by
  let magnitude : Fin 128 := nafMagnitude 8 b i.val (Or.inr rfl)
  let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have ht : Buffer s.mem (slots 1) 160 := by simpa [serialScratchBytes] using hm.scratch 1
  have hc : Buffer s.mem (slots 5) 160 := by simpa [serialScratchBytes] using hm.scratch 5
  have hd : E.read (%145) = .value (-BitVec.ofNat 8 magnitude.val) := by
    rw [hdigit, nafByte_negative 8 b i.val (Or.inr rfl) hsign]
  have hconv := completedState_writesOnly s (slots 1) (slots 5) hm.wellFormed ht
  obtain ⟨final, hrun, hframe, hread, hbound, _⟩ := serial_affine_sub_converted_state p g
    hh.multiply hh.affineSub E (slots 1) (slots 5) tableB magnitude s hm.wellFormed
    ht hc hm.tableBBuffer (hm.separate 1 5 (by decide)) (hm.separateB 1) (hm.separateB 5)
    hP.bounded (hm.cachedB k).1
  rw [Env.write_of_read E (%29) hr.r29, affine_subConvertInput_of_registers hr magnitude hd] at hrun
  have hf := (SerialScratchFrame.of_writesOnly 1 hconv).trans
    (SerialScratchFrame.of_writesOnly 5 hframe)
  have he := affine_subSelectedResult_frame hr magnitude hd
  refine ⟨_, final, hrun, hr.of_frame (he.weaken_serial (by decide)),
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hi,
    hm.preserve hf, hf, ⟨hbound, ?_⟩, he.1⟩
  rw [hread]
  obtain ⟨Q, hQ, hC⟩ := (hm.cachedB k).2
  have hrep := SerialPoint.affineSubCompleted_represents _ _ (SerialPoint.asExtended_tight _ hP.bounded)
    (hm.cachedB k).1 hP.represents hQ hC
  have hcoef := nafMagnitude_negative_coefficient 8 b i.val (Or.inr rfl) hsign
  change -((2*k.val+1 : Nat) : Int) = nafDigits 8 b i.val at hcoef
  rw [sub_eq_add_neg, ← natCast_zsmul, ← neg_zsmul, hcoef] at hrep
  exact hrep

theorem serial_ladder_affine_add (hh : SerialLadderHelpers p)
    (hr : SerialLadderRegisters slots tableA tableB da db E)
    (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    (hm : SerialLadderMemory slots tableA tableB da db a b A B s)
    (hP : SerialCompletedAt slots s V)
    (hdigit : E.read (%145) = .value (Execution.nafByte 8 b i.val))
    (hsign : 0 < nafDigits 8 b i.val) :
    ∃ E' s', (serialKernel p g).runFrom E 29 s = (serialKernel p g).runFrom E' 28 s' ∧
      SerialLadderRegisters slots tableA tableB da db E' ∧
      E'.read (%131) = .value (BitVec.ofNat 64 i.val) ∧
      SerialLadderMemory slots tableA tableB da db a b A B s' ∧
      SerialScratchFrame slots s s' ∧
      SerialCompletedAt slots s' (V + nafDigits 8 b i.val • B) ∧ E'.args = E.args := by
  let magnitude : Fin 128 := nafMagnitude 8 b i.val (Or.inr rfl)
  let k : Fin 64 := ⟨magnitude.val / 2, by have := magnitude.isLt; omega⟩
  have ht : Buffer s.mem (slots 2) 160 := by simpa [serialScratchBytes] using hm.scratch 2
  have hc : Buffer s.mem (slots 5) 160 := by simpa [serialScratchBytes] using hm.scratch 5
  have hd : E.read (%145) = .value (BitVec.ofNat 8 magnitude.val) := by
    rw [hdigit, nafByte_positive 8 b i.val (Or.inr rfl) (le_of_lt hsign)]
  have hconv := completedState_writesOnly s (slots 2) (slots 5) hm.wellFormed ht
  obtain ⟨final, hrun, hframe, hread, hbound, _⟩ := serial_affine_add_converted_state p g
    hh.multiply hh.affineAdd E (slots 2) (slots 5) tableB magnitude s hm.wellFormed
    ht hc hm.tableBBuffer (hm.separate 2 5 (by decide)) (hm.separateB 2) (hm.separateB 5)
    hP.bounded (hm.cachedB k).1
  rw [Env.write_of_read E (%29) hr.r29, affine_addConvertInput_of_registers hr magnitude hd] at hrun
  have hf := (SerialScratchFrame.of_writesOnly 2 hconv).trans
    (SerialScratchFrame.of_writesOnly 5 hframe)
  have he := affine_addSelectedResult_frame hr magnitude hd
  refine ⟨_, final, hrun, hr.of_frame (he.weaken_serial (by decide)),
    (he.read (%131) (by intro j ht heq; cases heq; decide)).trans hi,
    hm.preserve hf, hf, ⟨hbound, ?_⟩, he.1⟩
  rw [hread]
  obtain ⟨Q, hQ, hC⟩ := (hm.cachedB k).2
  have hrep := SerialPoint.affineAddCompleted_represents _ _ (SerialPoint.asExtended_tight _ hP.bounded)
    (hm.cachedB k).1 hP.represents hQ hC
  have hcoef := nafMagnitude_positive_coefficient 8 b i.val (Or.inr rfl) hsign
  change ((2*k.val+1 : Nat) : Int) = nafDigits 8 b i.val at hcoef
  rw [← natCast_zsmul, hcoef] at hrep
  exact hrep

end Agave.Ed25519.DoubleBase.RIR
