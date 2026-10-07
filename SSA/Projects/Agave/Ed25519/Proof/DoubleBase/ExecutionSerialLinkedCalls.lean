import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialLinked
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialSelectedCalls
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SerialContractsLink
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.LinkedHelperContracts

/-! Concrete point-call composition for the linked serial function. This layer
uses the imported cached-add and projective-double contracts directly. All five
point operations resolve to their independently checked imported helper bodies.
These local compositions do not assert constructor or whole-function correctness. -/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR
open NAF.Memory (Buffer)

/-- This A dispatch has no successful-double or arithmetic-helper premise:
the point contract resolves to the imported double body and pow2k(1) calls. -/
theorem serialLinked_dispatchA_naf (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
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
      (serialLinkedKernel g d2 panic).runFrom
        (serialDispatchAInput E digits completed projective i) (18 : Fin 36) s =
        (serialLinkedKernel g d2 panic).runFrom
          (serialDispatchAResult E digits completed projective i (Execution.nafByte 5 n i.val))
          ((if nafDigits 5 n i.val < 0 then 20 else if nafDigits 5 n i.val = 0 then 26 else 21) : Fin 36) final ∧
      SerialContracts.WritesOnly completed 160 s final ∧
      SerialContracts.readPoint final completed =
        SerialPoint.doubleCompleted (SerialContracts.readProjective s projective) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) :=
  serial_dispatchA_naf (serialLinkedPrimitives d2 panic) g
    SerialPoint.Execution.double_contract E digits completed projective n i s hwf hd hc hp
    hdisjoint hne hP hread

/-- Four real multiplication calls, the compiler guard and scaled GEP, and the
real cached-add body compose without a successful-helper premise. -/
theorem serialLinked_cached_add_converted_call (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 16)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 1280)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readCached s
      (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2)))))) :
    ∃ (final : GlobalState) (resultEnv : ⟪serialKernel.Γ⟫),
      (serialLinkedKernel g d2 panic).runFrom (cached_addConvertInput
        (E[%39 := .value table]) temporary completed magnitude) (21 : Fin 36) s =
          (serialLinkedKernel g d2 panic).runFrom resultEnv (26 : Fin 36) final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = SerialPoint.cachedAddCompleted
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) :=
  serial_cached_add_converted_call (serialLinkedPrimitives d2 panic) g rfl
    SerialPoint.Execution.cached_add_contract E temporary completed table magnitude s hwf
    ht hc htable htc htt hct hP hC

/-- The negative width-five branch resolves to the imported cached-sub body. -/
theorem serialLinked_cached_sub_converted_call (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 16)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 1280)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readCached s
      (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2)))))) :
    ∃ (final : GlobalState) (resultEnv : ⟪serialKernel.Γ⟫),
      (serialLinkedKernel g d2 panic).runFrom (cached_subConvertInput
        (E[%39 := .value table]) temporary completed magnitude) (20 : Fin 36) s =
          (serialLinkedKernel g d2 panic).runFrom resultEnv (26 : Fin 36) final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = SerialPoint.cachedSubCompleted
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readCached s (table.add (BitVec.ofNat 64 (160 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) :=
  serial_cached_sub_converted_call (serialLinkedPrimitives d2 panic) g rfl
    serialResidualPointContracts.cachedSub E temporary completed table magnitude s hwf
    ht hc htable htc htt hct hP hC

/-- The negative width-eight branch resolves to the imported affine-sub body. -/
theorem serialLinked_affine_sub_converted_call (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 128)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 7680)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readAffineCached s
      (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2)))))) :
    ∃ (final : GlobalState) (resultEnv : ⟪serialKernel.Γ⟫),
      (serialLinkedKernel g d2 panic).runFrom (affine_subConvertInput
        (E[%29 := .value table]) temporary completed magnitude) (27 : Fin 36) s =
          (serialLinkedKernel g d2 panic).runFrom resultEnv (28 : Fin 36) final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = (fun P C : SerialPoint.LimbPoint => SerialPoint.affineSubCompleted P C.X C.Y C.T)
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readAffineCached s (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) :=
  serial_affine_sub_converted_call (serialLinkedPrimitives d2 panic) g rfl
    serialResidualPointContracts.affineSub E temporary completed table magnitude s hwf
    ht hc htable htc htt hct hP hC

/-- The positive width-eight branch resolves to the imported affine-add body. -/
theorem serialLinked_affine_add_converted_call (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (E : ⟪serialKernel.Γ⟫) (temporary completed table : Pointer) (magnitude : Fin 128)
    (s : GlobalState) (hwf : s.WF)
    (ht : Buffer s.mem temporary 160) (hc : Buffer s.mem completed 160)
    (htable : Buffer s.mem table 7680)
    (htc : temporary.id ≠ completed.id) (htt : temporary.id ≠ table.id)
    (hct : completed.id ≠ table.id)
    (hP : SerialPoint.PointBounded (SerialContracts.readPoint s completed))
    (hC : SerialPoint.PointBounded (SerialContracts.readAffineCached s
      (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2)))))) :
    ∃ (final : GlobalState) (resultEnv : ⟪serialKernel.Γ⟫),
      (serialLinkedKernel g d2 panic).runFrom (affine_addConvertInput
        (E[%29 := .value table]) temporary completed magnitude) (29 : Fin 36) s =
          (serialLinkedKernel g d2 panic).runFrom resultEnv (28 : Fin 36) final ∧
      SerialContracts.WritesOnly completed 160 (completedState s temporary completed) final ∧
      SerialContracts.readPoint final completed = (fun P C : SerialPoint.LimbPoint => SerialPoint.affineAddCompleted P C.X C.Y C.T)
        (SerialPoint.asExtended (SerialContracts.readPoint s completed))
        (SerialContracts.readAffineCached s (table.add (BitVec.ofNat 64 (120 * (magnitude.val / 2))))) ∧
      SerialPoint.PointBounded (SerialContracts.readPoint final completed) :=
  serial_affine_add_converted_call (serialLinkedPrimitives d2 panic) g rfl
    serialResidualPointContracts.affineAdd E temporary completed table magnitude s hwf
    ht hc htable htc htt hct hP hC

end Agave.Ed25519.DoubleBase.RIR
