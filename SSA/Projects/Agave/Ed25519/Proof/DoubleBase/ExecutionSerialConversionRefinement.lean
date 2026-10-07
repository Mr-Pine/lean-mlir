import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialConversionCalls
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.FieldCall
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointMemory

/-! Mathematical readback of the four actual field calls. The only numeric
premise is the preceding completed point's limb bound. The extended result is
derived from real final memory and is tight for the next point helper. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open SerialContracts (readField readPoint)
set_option maxRecDepth 10000

theorem fieldState_readField_ne (s : GlobalState) (out a b q : Pointer)
    (hne : out.id ≠ q.id) :
    readField (fieldState s out a b) q = readField s q := by
  unfold readField
  rw [show SerialFieldMul.readLimbs (fieldState s out a b) q = SerialFieldMul.readLimbs s q from
    SerialPoint.Execution.readLimbs_storeLimbs_ne s out q _ hne]

theorem fieldState_readField_frame (s : GlobalState) (out a b q : Pointer)
    (ho : Buffer s.mem out 40) (hq : Buffer s.mem q 40)
    (hd : (Range.of q 320).Disjoint (Range.of out 320)) :
    readField (fieldState s out a b) q = readField s q := by
  unfold readField
  rw [show SerialFieldMul.readLimbs (fieldState s out a b) q = SerialFieldMul.readLimbs s q from
    SerialPoint.Execution.readLimbs_storeLimbs_frame s out q _ ho hq hd]

theorem fieldState_readField_correct (s : GlobalState) (out a b : Pointer)
    (ho : Buffer s.mem out 40)
    (ha : SerialFieldMul.Bounded (readField s a))
    (hb : SerialFieldMul.Bounded (readField s b)) :
    readField (fieldState s out a b) out = SerialPoint.mul (readField s a) (readField s b) :=
  (SerialPoint.Execution.mulPost_correct s out a b ho ha hb).1

theorem fieldState_readPoint_ne (s : GlobalState) (out a b q : Pointer)
    (hne : out.id ≠ q.id) :
    readPoint (fieldState s out a b) q = readPoint s q := by
  apply PointArithmetic.Extended.ext
  all_goals
    apply fieldState_readField_ne
    simpa only [Pointer.add_id] using hne

/-- Completed-to-extended conversion has no point-arithmetic callback: it is
four exact field kernels, with coordinate separation derived from the output
object's size. Different input/output allocation ids follow at each actual
call site from the serial function's own stack allocations. -/
theorem completedState_readPoint (s : GlobalState) (out input : Pointer)
    (hout : Buffer s.mem out 160) (hinput : Buffer s.mem input 160)
    (hne : out.id ≠ input.id)
    (hP : SerialPoint.PointBounded (readPoint s input)) :
    readPoint (completedState s out input) out = SerialPoint.asExtended (readPoint s input) := by
  let s₁ := fieldState s out input (input.add 120)
  let s₂ := fieldState s₁ (out.add 40) (input.add 40) (input.add 80)
  let s₃ := fieldState s₂ (out.add 80) (input.add 80) (input.add 120)
  have ho₁ := fieldState_buffer hout out input (input.add 120)
  have ho₂ := fieldState_buffer ho₁ (out.add 40) (input.add 40) (input.add 80)
  have ho₃ := fieldState_buffer ho₂ (out.add 80) (input.add 80) (input.add 120)
  have hr₁ : readPoint s₁ input = readPoint s input := fieldState_readPoint_ne _ _ _ _ _ hne
  have hr₂ : readPoint s₂ input = readPoint s input :=
    (fieldState_readPoint_ne _ _ _ _ _ (by simpa only [Pointer.add_id] using hne)).trans hr₁
  have hr₃ : readPoint s₃ input = readPoint s input :=
    (fieldState_readPoint_ne _ _ _ _ _ (by simpa only [Pointer.add_id] using hne)).trans hr₂
  have hb₁ : SerialPoint.PointBounded (readPoint s₁ input) := hr₁.symm ▸ hP
  have hb₂ : SerialPoint.PointBounded (readPoint s₂ input) := hr₂.symm ▸ hP
  have hb₃ : SerialPoint.PointBounded (readPoint s₃ input) := hr₃.symm ▸ hP
  have readX₁ : readField s₁ input = readField s input := congrArg PointArithmetic.Extended.X hr₁
  have readY₁ : readField s₁ (input.add 40) = readField s (input.add 40) := congrArg PointArithmetic.Extended.Y hr₁
  have readZ₁ : readField s₁ (input.add 80) = readField s (input.add 80) := congrArg PointArithmetic.Extended.Z hr₁
  have readZ₂ : readField s₂ (input.add 80) = readField s (input.add 80) := congrArg PointArithmetic.Extended.Z hr₂
  have readT₂ : readField s₂ (input.add 120) = readField s (input.add 120) := congrArg PointArithmetic.Extended.T hr₂
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
  have hX₁ : readField s₁ out = SerialPoint.mul (readField s input) (readField s (input.add 120)) :=
    fieldState_readField_correct s out input (input.add 120) h0 hP.1 hP.2.2.2
  have hX₂ : readField s₂ out = readField s₁ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₁.slice 40 40 (by decide)) h0₁
      (by simpa using hd 0 1 (by decide))
  have hX₃ : readField s₃ out = readField s₂ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₂.slice 80 40 (by decide)) h0₂
      (by simpa using hd 0 2 (by decide))
  have hX₄ : readField (completedState s out input) out = readField s₃ out :=
    fieldState_readField_frame _ _ _ _ _ (ho₃.slice 120 40 (by decide)) h0₃
      (by simpa using hd 0 3 (by decide))
  have hY₂ : readField s₂ (out.add 40) = SerialPoint.mul (readField s (input.add 40)) (readField s (input.add 80)) := by
    simpa only [readY₁, readZ₁] using fieldState_readField_correct
      s₁ (out.add 40) (input.add 40) (input.add 80)
      (ho₁.slice 40 40 (by decide)) hb₁.2.1 hb₁.2.2.1
  have hY₃ : readField s₃ (out.add 40) = readField s₂ (out.add 40) :=
    fieldState_readField_frame _ _ _ _ _ (ho₂.slice 80 40 (by decide)) (ho₂.slice 40 40 (by decide))
      (by simpa using hd 1 2 (by decide))
  have hY₄ : readField (completedState s out input) (out.add 40) = readField s₃ (out.add 40) :=
    fieldState_readField_frame _ _ _ _ _ (ho₃.slice 120 40 (by decide)) (ho₃.slice 40 40 (by decide))
      (by simpa using hd 1 3 (by decide))
  have hZ₃ : readField s₃ (out.add 80) = SerialPoint.mul (readField s (input.add 80)) (readField s (input.add 120)) := by
    simpa only [readZ₂, readT₂] using fieldState_readField_correct
      s₂ (out.add 80) (input.add 80) (input.add 120)
      (ho₂.slice 80 40 (by decide)) hb₂.2.2.1 hb₂.2.2.2
  have hZ₄ : readField (completedState s out input) (out.add 80) = readField s₃ (out.add 80) :=
    fieldState_readField_frame _ _ _ _ _ (ho₃.slice 120 40 (by decide)) (ho₃.slice 80 40 (by decide))
      (by simpa using hd 2 3 (by decide))
  have hT₄ : readField (completedState s out input) (out.add 120) =
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

theorem completedState_pointTight (s : GlobalState) (out input : Pointer)
    (hout : Buffer s.mem out 160) (hinput : Buffer s.mem input 160)
    (hne : out.id ≠ input.id) (hP : SerialPoint.PointBounded (readPoint s input)) :
    SerialPoint.PointTight (readPoint (completedState s out input) out) := by
  rw [completedState_readPoint s out input hout hinput hne hP]
  exact SerialPoint.asExtended_tight _ hP


theorem completedState_readField_ne (s : GlobalState) (out input q : Pointer)
    (hne : out.id ≠ q.id) :
    readField (completedState s out input) q = readField s q := by
  unfold completedState
  rw [fieldState_readField_ne _ _ _ _ q (by simpa only [Pointer.add_id] using hne),
    fieldState_readField_ne _ _ _ _ q (by simpa only [Pointer.add_id] using hne),
    fieldState_readField_ne _ _ _ _ q (by simpa only [Pointer.add_id] using hne),
    fieldState_readField_ne _ _ _ _ q hne]

theorem completedState_readCached_ne (s : GlobalState) (out input q : Pointer)
    (hne : out.id ≠ q.id) :
    SerialContracts.readCached (completedState s out input) q = SerialContracts.readCached s q := by
  apply PointArithmetic.Extended.ext
  all_goals
    apply completedState_readField_ne
    simpa only [Pointer.add_id] using hne

theorem completedState_readAffineCached_ne (s : GlobalState) (out input q : Pointer)
    (hne : out.id ≠ q.id) :
    SerialContracts.readAffineCached (completedState s out input) q = SerialContracts.readAffineCached s q := by
  apply PointArithmetic.Extended.ext
  all_goals first | rfl |
    (apply completedState_readField_ne; simpa only [Pointer.add_id] using hne)

/-- Pair the exact call result with its natural-limb interpretation, rather
than accepting a caller-supplied successful-conversion predicate. -/
theorem completedCalls_correct (s : GlobalState) (out input : Pointer) (hwf : s.WF)
    (hout : Buffer s.mem out 160) (hinput : Buffer s.mem input 160)
    (hne : out.id ≠ input.id) (hP : SerialPoint.PointBounded (readPoint s input)) :
    completedCalls SerialFieldMul.kernel.call out input s = .value (.nil, completedState s out input) ∧
      readPoint (completedState s out input) out = SerialPoint.asExtended (readPoint s input) ∧
      SerialPoint.PointTight (readPoint (completedState s out input) out) :=
  ⟨completedCalls_kernel s out input hwf hout hinput,
    completedState_readPoint s out input hout hinput hne hP,
    completedState_pointTight s out input hout hinput hne hP⟩

end Agave.Ed25519.DoubleBase.RIR
