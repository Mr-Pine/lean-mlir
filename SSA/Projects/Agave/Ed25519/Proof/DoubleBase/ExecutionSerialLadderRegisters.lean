import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSelectedState
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialNAFSelection
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialScanComplete
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSuffix

/-! Persistent compiler registers at the serial ladder boundary. Actual
selected-path environments retain the whole loop context and the cursor. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
set_option maxRecDepth 10000

structure SerialLadderRegisters (slots : Fin 7 → Pointer) (tableA tableB da db : Pointer)
    (E : ⟪serialKernel.Γ⟫) : Prop where
  r0 : E.read (%0) = .value 1#32
  r1 : E.read (%1) = .value 0#8
  r4 : E.read (%4) = .value 0#64
  r10 : E.read (%10) = .value 1#64
  r19 : E.read (%19) = .value (-1 : BitVec 64)
  r20 : E.read (%20) = .value 40#64
  r22 : E.read (%22) = .value 80#64
  r23 : E.read (%23) = .value 120#64
  r24 : E.read (%24) = .value 16#8
  r26 : E.read (%26) = .value 255#8
  r29 : E.read (%29) = .value tableB
  r32 : E.read (%32) = .value (slots 0)
  r33 : E.read (%33) = .value (slots 1)
  r34 : E.read (%34) = .value (slots 2)
  r35 : E.read (%35) = .value (slots 3)
  r36 : E.read (%36) = .value (slots 4)
  r37 : E.read (%37) = .value (slots 5)
  r38 : E.read (%38) = .value (slots 6)
  r39 : E.read (%39) = .value tableA
  r40 : E.read (%40) = .value db
  r41 : E.read (%41) = .value da
  r107 : E.read (%107) = .value ((slots 6).add 40)
  r108 : E.read (%108) = .value ((slots 6).add 80)
  r109 : E.read (%109) = .value ((slots 5).add 120)
  r110 : E.read (%110) = .value ((slots 5).add 40)
  r111 : E.read (%111) = .value ((slots 5).add 80)
  r112 : E.read (%112) = .value ((slots 4).add 40)
  r113 : E.read (%113) = .value ((slots 4).add 80)
  r114 : E.read (%114) = .value ((slots 4).add 120)
  r115 : E.read (%115) = .value ((slots 3).add 40)
  r116 : E.read (%116) = .value ((slots 3).add 80)
  r117 : E.read (%117) = .value ((slots 3).add 120)
  r118 : E.read (%118) = .value ((slots 2).add 40)
  r119 : E.read (%119) = .value ((slots 2).add 80)
  r120 : E.read (%120) = .value ((slots 2).add 120)
  r121 : E.read (%121) = .value ((slots 1).add 40)
  r122 : E.read (%122) = .value ((slots 1).add 80)
  r123 : E.read (%123) = .value ((slots 1).add 120)
  r124 : E.read (%124) = .value ((slots 0).add 40)
  r125 : E.read (%125) = .value ((slots 0).add 80)

variable {slots : Fin 7 → Pointer} {tableA tableB da db : Pointer}
  {E E' : ⟪serialKernel.Γ⟫}

theorem SerialLadderRegisters.of_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (hf : PrefixEq E E' 131) : SerialLadderRegisters slots tableA tableB da db E' := by
  constructor
  · exact (hf.read (%0) (by intro i ht heq; cases heq; decide)).trans h.r0
  · exact (hf.read (%1) (by intro i ht heq; cases heq; decide)).trans h.r1
  · exact (hf.read (%4) (by intro i ht heq; cases heq; decide)).trans h.r4
  · exact (hf.read (%10) (by intro i ht heq; cases heq; decide)).trans h.r10
  · exact (hf.read (%19) (by intro i ht heq; cases heq; decide)).trans h.r19
  · exact (hf.read (%20) (by intro i ht heq; cases heq; decide)).trans h.r20
  · exact (hf.read (%22) (by intro i ht heq; cases heq; decide)).trans h.r22
  · exact (hf.read (%23) (by intro i ht heq; cases heq; decide)).trans h.r23
  · exact (hf.read (%24) (by intro i ht heq; cases heq; decide)).trans h.r24
  · exact (hf.read (%26) (by intro i ht heq; cases heq; decide)).trans h.r26
  · exact (hf.read (%29) (by intro i ht heq; cases heq; decide)).trans h.r29
  · exact (hf.read (%32) (by intro i ht heq; cases heq; decide)).trans h.r32
  · exact (hf.read (%33) (by intro i ht heq; cases heq; decide)).trans h.r33
  · exact (hf.read (%34) (by intro i ht heq; cases heq; decide)).trans h.r34
  · exact (hf.read (%35) (by intro i ht heq; cases heq; decide)).trans h.r35
  · exact (hf.read (%36) (by intro i ht heq; cases heq; decide)).trans h.r36
  · exact (hf.read (%37) (by intro i ht heq; cases heq; decide)).trans h.r37
  · exact (hf.read (%38) (by intro i ht heq; cases heq; decide)).trans h.r38
  · exact (hf.read (%39) (by intro i ht heq; cases heq; decide)).trans h.r39
  · exact (hf.read (%40) (by intro i ht heq; cases heq; decide)).trans h.r40
  · exact (hf.read (%41) (by intro i ht heq; cases heq; decide)).trans h.r41
  · exact (hf.read (%107) (by intro i ht heq; cases heq; decide)).trans h.r107
  · exact (hf.read (%108) (by intro i ht heq; cases heq; decide)).trans h.r108
  · exact (hf.read (%109) (by intro i ht heq; cases heq; decide)).trans h.r109
  · exact (hf.read (%110) (by intro i ht heq; cases heq; decide)).trans h.r110
  · exact (hf.read (%111) (by intro i ht heq; cases heq; decide)).trans h.r111
  · exact (hf.read (%112) (by intro i ht heq; cases heq; decide)).trans h.r112
  · exact (hf.read (%113) (by intro i ht heq; cases heq; decide)).trans h.r113
  · exact (hf.read (%114) (by intro i ht heq; cases heq; decide)).trans h.r114
  · exact (hf.read (%115) (by intro i ht heq; cases heq; decide)).trans h.r115
  · exact (hf.read (%116) (by intro i ht heq; cases heq; decide)).trans h.r116
  · exact (hf.read (%117) (by intro i ht heq; cases heq; decide)).trans h.r117
  · exact (hf.read (%118) (by intro i ht heq; cases heq; decide)).trans h.r118
  · exact (hf.read (%119) (by intro i ht heq; cases heq; decide)).trans h.r119
  · exact (hf.read (%120) (by intro i ht heq; cases heq; decide)).trans h.r120
  · exact (hf.read (%121) (by intro i ht heq; cases heq; decide)).trans h.r121
  · exact (hf.read (%122) (by intro i ht heq; cases heq; decide)).trans h.r122
  · exact (hf.read (%123) (by intro i ht heq; cases heq; decide)).trans h.r123
  · exact (hf.read (%124) (by intro i ht heq; cases heq; decide)).trans h.r124
  · exact (hf.read (%125) (by intro i ht heq; cases heq; decide)).trans h.r125

theorem serialDispatchAInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (i : Fin 256) (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    : serialDispatchAInput E da (slots 5) (slots 6) i = E := by
  unfold serialDispatchAInput
  rw [Env.write_of_read E (%1) h.r1,
    Env.write_of_read E (%37) h.r37,
    Env.write_of_read E (%38) h.r38,
    Env.write_of_read E (%41) h.r41,
    Env.write_of_read E (%131) hi]

theorem serialDispatchBInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (i : Fin 256) (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    : serialDispatchBInput E db i = E := by
  unfold serialDispatchBInput
  rw [Env.write_of_read E (%1) h.r1,
    Env.write_of_read E (%40) h.r40,
    Env.write_of_read E (%131) hi]

theorem projectiveInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (i : Fin 256) (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val))
    : projectiveInput E (slots 0) (slots 5) (slots 6) i = E := by
  unfold projectiveInput
  rw [Env.write_of_read E (%4) h.r4,
    Env.write_of_read E (%23) h.r23,
    Env.write_of_read E (%32) h.r32,
    Env.write_of_read E (%37) h.r37,
    Env.write_of_read E (%38) h.r38,
    Env.write_of_read E (%109) h.r109,
    Env.write_of_read E (%110) h.r110,
    Env.write_of_read E (%111) h.r111,
    Env.write_of_read E (%124) h.r124,
    Env.write_of_read E (%125) h.r125,
    Env.write_of_read E (%131) hi]

theorem serialReturnInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    : serialReturnInput E (slots 6) = E := by
  unfold serialReturnInput
  rw [Env.write_of_read E (%0) h.r0,
    Env.write_of_read E (%20) h.r20,
    Env.write_of_read E (%22) h.r22,
    Env.write_of_read E (%23) h.r23,
    Env.write_of_read E (%38) h.r38,
    Env.write_of_read E (%107) h.r107,
    Env.write_of_read E (%108) h.r108]

theorem cached_subConvertInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 16)
    (hdigit : E.read (%133) = .value (-BitVec.ofNat 8 magnitude.val))
    : cached_subConvertInput E (slots 3) (slots 5) magnitude = E := by
  unfold cached_subConvertInput
  rw [Env.write_of_read E (%1) h.r1,
    Env.write_of_read E (%10) h.r10,
    Env.write_of_read E (%24) h.r24,
    Env.write_of_read E (%35) h.r35,
    Env.write_of_read E (%37) h.r37,
    Env.write_of_read E (%109) h.r109,
    Env.write_of_read E (%110) h.r110,
    Env.write_of_read E (%111) h.r111,
    Env.write_of_read E (%115) h.r115,
    Env.write_of_read E (%116) h.r116,
    Env.write_of_read E (%117) h.r117,
    Env.write_of_read E (%133) hdigit]

theorem cached_addConvertInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 16)
    (hdigit : E.read (%133) = .value (BitVec.ofNat 8 magnitude.val))
    : cached_addConvertInput E (slots 4) (slots 5) magnitude = E := by
  unfold cached_addConvertInput
  rw [Env.write_of_read E (%1) h.r1,
    Env.write_of_read E (%10) h.r10,
    Env.write_of_read E (%24) h.r24,
    Env.write_of_read E (%36) h.r36,
    Env.write_of_read E (%37) h.r37,
    Env.write_of_read E (%109) h.r109,
    Env.write_of_read E (%110) h.r110,
    Env.write_of_read E (%111) h.r111,
    Env.write_of_read E (%112) h.r112,
    Env.write_of_read E (%113) h.r113,
    Env.write_of_read E (%114) h.r114,
    Env.write_of_read E (%133) hdigit]

theorem affine_subConvertInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 128)
    (hdigit : E.read (%145) = .value (-BitVec.ofNat 8 magnitude.val))
    : affine_subConvertInput E (slots 1) (slots 5) magnitude = E := by
  unfold affine_subConvertInput
  rw [Env.write_of_read E (%1) h.r1,
    Env.write_of_read E (%10) h.r10,
    Env.write_of_read E (%26) h.r26,
    Env.write_of_read E (%33) h.r33,
    Env.write_of_read E (%37) h.r37,
    Env.write_of_read E (%109) h.r109,
    Env.write_of_read E (%110) h.r110,
    Env.write_of_read E (%111) h.r111,
    Env.write_of_read E (%121) h.r121,
    Env.write_of_read E (%122) h.r122,
    Env.write_of_read E (%123) h.r123,
    Env.write_of_read E (%145) hdigit]

theorem affine_addConvertInput_of_registers (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 128)
    (hdigit : E.read (%145) = .value (BitVec.ofNat 8 magnitude.val))
    : affine_addConvertInput E (slots 2) (slots 5) magnitude = E := by
  unfold affine_addConvertInput
  rw [Env.write_of_read E (%1) h.r1,
    Env.write_of_read E (%10) h.r10,
    Env.write_of_read E (%26) h.r26,
    Env.write_of_read E (%34) h.r34,
    Env.write_of_read E (%37) h.r37,
    Env.write_of_read E (%109) h.r109,
    Env.write_of_read E (%110) h.r110,
    Env.write_of_read E (%111) h.r111,
    Env.write_of_read E (%118) h.r118,
    Env.write_of_read E (%119) h.r119,
    Env.write_of_read E (%120) h.r120,
    Env.write_of_read E (%145) hdigit]

theorem PrefixEq.weaken_serial {limit limit' : Nat} (h : PrefixEq E E' limit)
    (hle : limit' ≤ limit) : PrefixEq E E' limit' :=
  ⟨h.1, fun i hi => h.2 i (lt_of_lt_of_le hi hle)⟩

theorem serialDispatchAResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (i : Fin 256) (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val)) (digit : BitVec 8) :
    PrefixEq E (serialDispatchAResult E da (slots 5) (slots 6) i digit) 132 := by
  unfold serialDispatchAResult
  rw [serialDispatchAInput_of_registers h i hi]
  iterate 3 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem serialDispatchBResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (i : Fin 256) (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val)) (digit : BitVec 8) :
    PrefixEq E (serialDispatchBResult E db i digit) 132 := by
  unfold serialDispatchBResult
  rw [serialDispatchBInput_of_registers h i hi]
  iterate 3 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem projectiveResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (i : Fin 256) (hi : E.read (%131) = .value (BitVec.ofNat 64 i.val)) :
    PrefixEq E (projectiveResult E (slots 0) (slots 5) (slots 6) i) 132 := by
  unfold projectiveResult
  rw [projectiveInput_of_registers h i hi]
  apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem cached_subSelectedResult_eq (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 16) :
    cached_subSelectedResult E (slots 3) (slots 5) tableA magnitude =
      (cached_subConvertResult E (slots 3) (slots 5) magnitude)[%142 :=
        .value (tableA.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))] := by
  unfold cached_subSelectedResult
  rw [Env.write_of_read E (%39) h.r39]
  let C := cached_subConvertResult E (slots 3) (slots 5) magnitude
  have h37 : C.read (%37) = .value (slots 5) := by
    simp [C, cached_subConvertResult, cached_subConvertInput, mlir_env]
  have htemp : C.read (%35) = .value (slots 3) := by
    simp [C, cached_subConvertResult, cached_subConvertInput, mlir_env]
  have htable : C.read (%39) = .value tableA := by
    simpa [C, cached_subConvertResult, cached_subConvertInput, mlir_env] using h.r39
  have hindex : C.read (%137) = .value (BitVec.ofNat 64 (magnitude.val / 2)) := by
    simp [C, cached_subConvertResult, cached_subConvertInput, mlir_env]
  change (cached_subInput C (slots 5) (slots 3) tableA _)[%142 := _] = _
  unfold cached_subInput
  rw [Env.write_of_read C (%37) h37, Env.write_of_read C (%35) htemp,
    Env.write_of_read C (%39) htable, Env.write_of_read C (%137) hindex]

theorem cached_subSelectedResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 16)
    (hdigit : E.read (%133) = .value (-BitVec.ofNat 8 magnitude.val)) :
    PrefixEq E (cached_subSelectedResult E (slots 3) (slots 5) tableA magnitude) 132 := by
  rw [cached_subSelectedResult_eq h magnitude]
  unfold cached_subConvertResult
  rw [cached_subConvertInput_of_registers h magnitude hdigit]
  iterate 5 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem cached_addSelectedResult_eq (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 16) :
    cached_addSelectedResult E (slots 4) (slots 5) tableA magnitude =
      (cached_addConvertResult E (slots 4) (slots 5) magnitude)[%143 :=
        .value (tableA.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))] := by
  unfold cached_addSelectedResult
  rw [Env.write_of_read E (%39) h.r39]
  let C := cached_addConvertResult E (slots 4) (slots 5) magnitude
  have h37 : C.read (%37) = .value (slots 5) := by
    simp [C, cached_addConvertResult, cached_addConvertInput, mlir_env]
  have htemp : C.read (%36) = .value (slots 4) := by
    simp [C, cached_addConvertResult, cached_addConvertInput, mlir_env]
  have htable : C.read (%39) = .value tableA := by
    simpa [C, cached_addConvertResult, cached_addConvertInput, mlir_env] using h.r39
  have hindex : C.read (%140) = .value (BitVec.ofNat 64 (magnitude.val / 2)) := by
    simp [C, cached_addConvertResult, cached_addConvertInput, mlir_env]
  change (cached_addInput C (slots 5) (slots 4) tableA _)[%143 := _] = _
  unfold cached_addInput
  rw [Env.write_of_read C (%37) h37, Env.write_of_read C (%36) htemp,
    Env.write_of_read C (%39) htable, Env.write_of_read C (%140) hindex]

theorem cached_addSelectedResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 16)
    (hdigit : E.read (%133) = .value (BitVec.ofNat 8 magnitude.val)) :
    PrefixEq E (cached_addSelectedResult E (slots 4) (slots 5) tableA magnitude) 132 := by
  rw [cached_addSelectedResult_eq h magnitude]
  unfold cached_addConvertResult
  rw [cached_addConvertInput_of_registers h magnitude hdigit]
  iterate 4 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem affine_subSelectedResult_eq (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 128) :
    affine_subSelectedResult E (slots 1) (slots 5) tableB magnitude =
      (affine_subConvertResult E (slots 1) (slots 5) magnitude)[%155 :=
        .value (tableB.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))] := by
  unfold affine_subSelectedResult
  rw [Env.write_of_read E (%29) h.r29]
  let C := affine_subConvertResult E (slots 1) (slots 5) magnitude
  have h37 : C.read (%37) = .value (slots 5) := by
    simp [C, affine_subConvertResult, affine_subConvertInput, mlir_env]
  have htemp : C.read (%33) = .value (slots 1) := by
    simp [C, affine_subConvertResult, affine_subConvertInput, mlir_env]
  have htable : C.read (%29) = .value tableB := by
    simpa [C, affine_subConvertResult, affine_subConvertInput, mlir_env] using h.r29
  have hindex : C.read (%149) = .value (BitVec.ofNat 64 (magnitude.val / 2)) := by
    simp [C, affine_subConvertResult, affine_subConvertInput, mlir_env]
  change (affine_subInput C (slots 5) (slots 1) tableB _)[%155 := _] = _
  unfold affine_subInput
  rw [Env.write_of_read C (%37) h37, Env.write_of_read C (%33) htemp,
    Env.write_of_read C (%29) htable, Env.write_of_read C (%149) hindex]

theorem affine_subSelectedResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 128)
    (hdigit : E.read (%145) = .value (-BitVec.ofNat 8 magnitude.val)) :
    PrefixEq E (affine_subSelectedResult E (slots 1) (slots 5) tableB magnitude) 132 := by
  rw [affine_subSelectedResult_eq h magnitude]
  unfold affine_subConvertResult
  rw [affine_subConvertInput_of_registers h magnitude hdigit]
  iterate 5 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

theorem affine_addSelectedResult_eq (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 128) :
    affine_addSelectedResult E (slots 2) (slots 5) tableB magnitude =
      (affine_addConvertResult E (slots 2) (slots 5) magnitude)[%156 :=
        .value (tableB.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))] := by
  unfold affine_addSelectedResult
  rw [Env.write_of_read E (%29) h.r29]
  let C := affine_addConvertResult E (slots 2) (slots 5) magnitude
  have h37 : C.read (%37) = .value (slots 5) := by
    simp [C, affine_addConvertResult, affine_addConvertInput, mlir_env]
  have htemp : C.read (%34) = .value (slots 2) := by
    simp [C, affine_addConvertResult, affine_addConvertInput, mlir_env]
  have htable : C.read (%29) = .value tableB := by
    simpa [C, affine_addConvertResult, affine_addConvertInput, mlir_env] using h.r29
  have hindex : C.read (%153) = .value (BitVec.ofNat 64 (magnitude.val / 2)) := by
    simp [C, affine_addConvertResult, affine_addConvertInput, mlir_env]
  change (affine_addInput C (slots 5) (slots 2) tableB _)[%156 := _] = _
  unfold affine_addInput
  rw [Env.write_of_read C (%37) h37, Env.write_of_read C (%34) htemp,
    Env.write_of_read C (%29) htable, Env.write_of_read C (%153) hindex]

theorem affine_addSelectedResult_frame (h : SerialLadderRegisters slots tableA tableB da db E)
    (magnitude : Fin 128)
    (hdigit : E.read (%145) = .value (BitVec.ofNat 8 magnitude.val)) :
    PrefixEq E (affine_addSelectedResult E (slots 2) (slots 5) tableB magnitude) 132 := by
  rw [affine_addSelectedResult_eq h magnitude]
  unfold affine_addConvertResult
  rw [affine_addConvertInput_of_registers h magnitude hdigit]
  iterate 4 apply PrefixEq.write (hi := by decide)
  exact PrefixEq.refl _ _

end Agave.Ed25519.DoubleBase.RIR
