import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialMemory
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Group

/-! Exact readback and representation of the actual serial return block.
Its input is the three-coordinate projective accumulator; validity is carried
by an extended representative with those same three coordinates. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (readField readPoint readProjective)
set_option maxRecDepth 10000

def returnAsExtended (P : SerialPoint.LimbPoint) : SerialPoint.LimbPoint :=
  ⟨SerialPoint.mul P.X P.Z, SerialPoint.mul P.Y P.Z,
    SerialPoint.sq P.Z, SerialPoint.mul P.X P.Y⟩

theorem returnAsExtended_value (P : SerialPoint.LimbPoint) :
    SerialPoint.pointValue (returnAsExtended P) =
      PointArithmetic.projectiveAsExtended (SerialPoint.pointValue P) := by
  apply PointArithmetic.Extended.ext <;>
    simp [returnAsExtended, SerialPoint.pointValue, PointArithmetic.projectiveAsExtended,
      SerialPoint.mul, SerialPoint.sq, SerialPoint.mul_value, SerialPoint.square_value]

theorem returnAsExtended_tight (P : SerialPoint.LimbPoint)
    (h : SerialPoint.PointBounded P) : SerialPoint.PointTight (returnAsExtended P) :=
  ⟨SerialPoint.mul_tight _ _ h.1 h.2.2.1, SerialPoint.mul_tight _ _ h.2.1 h.2.2.1,
    SerialPoint.sq_tight _ h.2.2.1, SerialPoint.mul_tight _ _ h.1 h.2.1⟩

theorem serialReturnState_readPoint (s : GlobalState) (out input : Pointer)
    (hout : Buffer s.mem out 160) (hinput : Buffer s.mem input 120)
    (hne : out.id ≠ input.id)
    (hP : SerialPoint.PointBounded (readProjective s input)) :
    readPoint (serialReturnState s out input) out = returnAsExtended (readProjective s input) := by
  let s₁ := fieldState s out input (input.add 80)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := squareState s₂ (out.add 80) (input.add 80)
  have ho₁ := fieldState_buffer hout out input (input.add 80)
  have ho₂ := fieldState_buffer ho₁ (out.add 40) (input.add 40) (input.add 80)
  have ho₃ := squareState_buffer ho₂ (out.add 80) (input.add 80)
  have hr₁ : readProjective s₁ input = readProjective s input := fieldState_readProjective_ne _ _ _ _ _ hne
  have hr₂ : readProjective s₂ input = readProjective s input :=
    (fieldState_readProjective_ne _ _ _ _ _ (by simpa only [Pointer.add_id] using hne)).trans hr₁
  have hr₃ : readProjective s₃ input = readProjective s input :=
    (squareState_readProjective_ne _ _ _ _ (by simpa only [Pointer.add_id] using hne)).trans hr₂
  have hb₁ : SerialPoint.PointBounded (readProjective s₁ input) := hr₁.symm ▸ hP
  have hb₂ : SerialPoint.PointBounded (readProjective s₂ input) := hr₂.symm ▸ hP
  have hb₃ : SerialPoint.PointBounded (readProjective s₃ input) := hr₃.symm ▸ hP
  have readX₁ : readField s₁ input = readField s input := congrArg PointArithmetic.Extended.X hr₁
  have readY₁ : readField s₁ (input.add 40) = readField s (input.add 40) := congrArg PointArithmetic.Extended.Y hr₁
  have readZ₁ : readField s₁ (input.add 80) = readField s (input.add 80) := congrArg PointArithmetic.Extended.Z hr₁
  have readZ₂ : readField s₂ (input.add 80) = readField s (input.add 80) := congrArg PointArithmetic.Extended.Z hr₂
  have readX₃ : readField s₃ input = readField s input := congrArg PointArithmetic.Extended.X hr₃
  have readY₃ : readField s₃ (input.add 40) = readField s (input.add 40) := congrArg PointArithmetic.Extended.Y hr₃
  have hd (a b : Fin 4) (hab : a ≠ b) :
      (Range.of (out.add (BitVec.ofNat 64 (40 * a.val))) 320).Disjoint
        (Range.of (out.add (BitVec.ofNat 64 (40 * b.val))) 320) := by
    apply SerialPoint.Execution.subranges_disjoint hout (ni := 40) (nj := 40)
      (by have := a.isLt; omega) (by have := b.isLt; omega)
    have : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  have h0 := hout.slice 0 40 (by decide)
  have h0₁ := ho₁.slice 0 40 (by decide)
  have h0₂ := ho₂.slice 0 40 (by decide)
  have h0₃ := ho₃.slice 0 40 (by decide)
  simp only [Pointer.add_zero] at h0 h0₁ h0₂ h0₃
  have hX₁ : readField s₁ out = SerialPoint.mul (readField s input) (readField s (input.add 80)) :=
    fieldState_readField_correct s out input (input.add 80) h0 hP.1 hP.2.2.1
  have hX₂ : readField s₂ out = readField s₁ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₁.slice 40 40 (by decide)) h0₁
      (by simpa using hd 0 1 (by decide))
  have hX₃ : readField s₃ out = readField s₂ out :=
    squareState_readField_frame _ _ _ _ (ho₂.slice 80 40 (by decide)) h0₂
      (by simpa using hd 0 2 (by decide))
  have hX₄ : readField (serialReturnState s out input) out = readField s₃ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₃.slice 120 40 (by decide)) h0₃
      (by simpa using hd 0 3 (by decide))
  have hY₂ : readField s₂ (out.add 40) = SerialPoint.mul (readField s (input.add 40)) (readField s (input.add 80)) := by
    simpa only [readY₁, readZ₁] using fieldState_readField_correct
      s₁ (out.add 40) (input.add 40) (input.add 80)
      (ho₁.slice 40 40 (by decide)) hb₁.2.1 hb₁.2.2.1
  have hY₃ : readField s₃ (out.add 40) = readField s₂ (out.add 40) :=
    squareState_readField_frame _ _ _ _ (ho₂.slice 80 40 (by decide)) (ho₂.slice 40 40 (by decide))
      (by simpa using hd 1 2 (by decide))
  have hY₄ : readField (serialReturnState s out input) (out.add 40) = readField s₃ (out.add 40) :=
    fieldState_readField_frame _ _ _ _ _ (ho₃.slice 120 40 (by decide)) (ho₃.slice 40 40 (by decide))
      (by simpa using hd 1 3 (by decide))
  have hZ₃ : readField s₃ (out.add 80) = SerialPoint.sq (readField s (input.add 80)) := by
    simpa only [readZ₂] using squareState_readField_correct
      s₂ (out.add 80) (input.add 80) (ho₂.slice 80 40 (by decide)) hb₂.2.2.1
  have hZ₄ : readField (serialReturnState s out input) (out.add 80) = readField s₃ (out.add 80) :=
    fieldState_readField_frame _ _ _ _ _ (ho₃.slice 120 40 (by decide)) (ho₃.slice 80 40 (by decide))
      (by simpa using hd 2 3 (by decide))
  have hT₄ : readField (serialReturnState s out input) (out.add 120) =
      SerialPoint.mul (readField s input) (readField s (input.add 40)) := by
    change readField (fieldState s₃ (out.add 120) input (input.add 40)) (out.add 120) = _
    simpa only [readX₃, readY₃] using fieldState_readField_correct
      s₃ (out.add 120) input (input.add 40)
      (ho₃.slice 120 40 (by decide)) hb₃.1 hb₃.2.1
  apply PointArithmetic.Extended.ext
  · exact hX₄.trans (hX₃.trans (hX₂.trans hX₁))
  · exact hY₄.trans (hY₃.trans hY₂)
  · exact hZ₄.trans hZ₃
  · exact hT₄

/-- Input validity does not manufacture a fourth field in the 120-byte
projective buffer. It records an extended representative of the same X,Y,Z. -/
def ProjectiveRepresents (P : SerialPoint.LimbPoint) (V : GroupPoint) : Prop :=
  ∃ Q : PointArithmetic.Extended Tables.F, Tables.Represents Q V ∧
    (SerialPoint.pointValue P).X = Q.X ∧
    (SerialPoint.pointValue P).Y = Q.Y ∧
    (SerialPoint.pointValue P).Z = Q.Z

theorem returnAsExtended_represents (P : SerialPoint.LimbPoint) (V : GroupPoint)
    (h : ProjectiveRepresents P V) :
    Tables.Represents (SerialPoint.pointValue (returnAsExtended P)) V := by
  obtain ⟨Q, hQ, hX, hY, hZ⟩ := h
  rw [returnAsExtended_value]
  have heq : PointArithmetic.projectiveAsExtended (SerialPoint.pointValue P) =
      PointArithmetic.projectiveAsExtended Q := by
    apply PointArithmetic.Extended.ext <;>
      simp only [PointArithmetic.projectiveAsExtended, hX, hY, hZ] <;> rfl
  rw [heq]
  exact represents_projectiveAsExtended hQ

/-- The imported output block succeeds, writes only its 160-byte result,
produces tight limbs, and preserves the represented group point. -/
theorem serial_return_run_represents (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (hfield : p.call2 = SerialFieldMul.kernel.call)
    (hsquare : p.call8 = Encoding.Decompress.Execution.Pow2k.program.call)
    (E : ⟪serialKernel.Γ⟫) (out projective : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : Buffer s.mem out 160) (hp : Buffer s.mem projective 120)
    (hne : out.id ≠ projective.id) (harg : E.read (%arg0) = .value out)
    (hbound : SerialPoint.PointBounded (readProjective s projective))
    (V : GroupPoint) (hpoint : ProjectiveRepresents (readProjective s projective) V) :
    (serialKernel p g).runFrom (serialReturnInput E projective) 34 s =
      .value (.nil, serialReturnState s out projective) ∧
    SerialContracts.WritesOnly out 160 s (serialReturnState s out projective) ∧
    SerialPoint.PointTight (readPoint (serialReturnState s out projective) out) ∧
    Tables.Represents (SerialPoint.pointValue (readPoint (serialReturnState s out projective) out)) V := by
  refine ⟨serial_return_run p g hfield hsquare E out projective s hwf hout hp harg,
    serialReturnState_writesOnly s out projective hwf hout, ?_, ?_⟩
  · rw [serialReturnState_readPoint s out projective hout hp hne hbound]
    exact returnAsExtended_tight _ hbound
  · rw [serialReturnState_readPoint s out projective hout hp hne hbound]
    exact returnAsExtended_represents _ V hpoint

end Agave.Ed25519.DoubleBase.RIR
