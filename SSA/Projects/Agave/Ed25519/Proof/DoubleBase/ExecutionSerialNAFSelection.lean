import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConversionCalls
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialDispatch

/-! Source-derived byte magnitude and exact signed-digit dispatch. These
bridges consume bytes produced by the actual NAF loops, so no future digit or
table index bound is an input assumption. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

theorem nafByte_positive (w n i : Nat) (hw : NAF.Supported w)
    (h : 0 ≤ nafDigits w n i) :
    Execution.nafByte w n i = BitVec.ofNat 8 (nafMagnitude w n i hw).val := by
  have hn := Int.natAbs_of_nonneg h
  unfold Execution.nafByte
  change BitVec.ofInt 8 (nafDigits w n i) = BitVec.ofNat 8 (nafDigits w n i).natAbs
  rw [← hn]
  rfl

theorem nafByte_negative (w n i : Nat) (hw : NAF.Supported w)
    (h : nafDigits w n i < 0) :
    Execution.nafByte w n i = -BitVec.ofNat 8 (nafMagnitude w n i hw).val := by
  have hn := Int.ofNat_natAbs_of_nonpos (Int.le_of_lt h)
  have hneg : nafDigits w n i = -((nafDigits w n i).natAbs : Int) := by omega
  unfold Execution.nafByte
  change BitVec.ofInt 8 (nafDigits w n i) = -BitVec.ofNat 8 (nafDigits w n i).natAbs
  conv_lhs => rw [hneg, BitVec.ofInt_neg]
  rfl

theorem nafByte_zero_iff (w n i : Nat) (hw : NAF.Supported w) :
    Execution.nafByte w n i = 0#8 ↔ nafDigits w n i = 0 := by
  constructor
  · intro h
    have hr := Execution.nafByte_toInt w hw n i
    rw [h] at hr
    exact hr.symm
  · intro h
    simp [Execution.nafByte, h]

/-- The exact negative/zero/positive B switch follows the source digit. -/
theorem serial_dispatchB_naf (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (digits : Pointer) (n : Nat) (i : Fin 256) (s : GlobalState)
    (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (NAF.sourceDigits 8 n i)) :
    (serialKernel p g).runFrom (serialDispatchBInput E digits i) 26 s =
      (serialKernel p g).runFrom
        (serialDispatchBResult E digits i (Execution.nafByte 8 n i.val))
        (if nafDigits 8 n i.val < 0 then 27 else if nafDigits 8 n i.val = 0 then 28 else 29) s := by
  have hbyte : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = Execution.nafByte 8 n i.val := hread
  simp only [serial_dispatchB_run p g E digits i _ s hbuffer hbyte,
    Execution.nafByte_toInt 8 (Or.inr rfl), nafByte_zero_iff 8 n i.val (Or.inr rfl)]

/-- The A switch after doubling follows the same source-derived byte. Only the
single named doubling helper is supplied as a mathematical call contract. -/
theorem serial_dispatchA_naf (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hdouble : SerialContracts.UnaryPointContract p.call1 120
      SerialContracts.readProjective SerialPoint.doubleCompleted)
    (E : ⟪serialKernel.Γ⟫) (digits completed projective : Pointer)
    (n : Nat) (i : Fin 256) (s : GlobalState) (hwf : s.WF)
    (hd : Buffer s.mem digits 256) (hc : Buffer s.mem completed 160)
    (hp : Buffer s.mem projective 120)
    (hdisjoint : SerialContracts.Disjoint completed 160 projective 120)
    (hne : digits.id ≠ completed.id)
    (hP : SerialPoint.PointTight (SerialContracts.readProjective s projective))
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 =
      BitVec.ofInt 8 (NAF.sourceDigits 5 n i)) :
    ∃ final,
      (serialKernel p g).runFrom (serialDispatchAInput E digits completed projective i) 18 s =
        (serialKernel p g).runFrom
          (serialDispatchAResult E digits completed projective i (Execution.nafByte 5 n i.val))
          (if nafDigits 5 n i.val < 0 then 20 else if nafDigits 5 n i.val = 0 then 26 else 21) final ∧
      SerialContracts.WritesOnly completed 160 s final ∧
      SerialContracts.readPoint final completed =
        SerialPoint.doubleCompleted (SerialContracts.readProjective s projective) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) := by
  obtain ⟨final, hcall, hframe, hpoint, hbound⟩ :=
    hdouble s completed projective hwf hc hp hdisjoint hP
  have hbyte : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = Execution.nafByte 5 n i.val := hread
  refine ⟨final, ?_, hframe, hpoint, hbound⟩
  simp only [serial_dispatchA_run p g E digits completed projective i _ s final hd hbyte hcall hframe hne,
    Execution.nafByte_toInt 5 (Or.inl rfl), nafByte_zero_iff 5 n i.val (Or.inl rfl)]

/-- The byte operand produced by the emitter matches the exact conversion
input encoding on either sign path, for both table widths. -/
theorem nafByte_magnitude (w n i : Nat) (hw : NAF.Supported w) :
    Execution.nafByte w n i =
      if nafDigits w n i < 0 then -BitVec.ofNat 8 (nafMagnitude w n i hw).val
      else BitVec.ofNat 8 (nafMagnitude w n i hw).val := by
  by_cases h : nafDigits w n i < 0
  · rw [if_pos h]
    exact nafByte_negative w n i hw h
  · rw [if_neg h]
    exact nafByte_positive w n i hw (by omega)

end Agave.Ed25519.DoubleBase.RIR
