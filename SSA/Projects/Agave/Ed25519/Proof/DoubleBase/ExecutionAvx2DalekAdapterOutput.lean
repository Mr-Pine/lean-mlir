import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapterFrame
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialValidPoint

/-! The actual AVX2 return words satisfy the verifier's tight representation
invariant. These lemmas retain the imported store trace and its exact bytes. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Reduce64.Execution (SmallRange)
open Avx2PointAdd.Phases (packPoint)
open Verifier.Execution
set_option maxRecDepth 10000

theorem unpackSerial_tight {P : Avx2PointAdd.Point}
    (hP : Avx2PointAdd.pointReduced P) (c : Fin 4) :
    SerialPoint.Tight (SerialFieldMul.unsigned (unpackSerial (packPoint P) c)) := by
  intro k
  have hbound (a : Avx2FieldMul.Limbs) (ha : Avx2PointAdd.reduced a) :
      (unpackPair (Avx2PointAdd.word (a (Avx2PointAdd.Phases.evenIndex k)))
        (Avx2PointAdd.word (a (Avx2PointAdd.Phases.oddIndex k)))).toNat < 2^52 := by
    have he := ha (Avx2PointAdd.Phases.evenIndex k)
    have ho := ha (Avx2PointAdd.Phases.oddIndex k)
    have hk := k.isLt
    simp only [Avx2PointAdd.radix, Avx2PointAdd.Phases.evenIndex,
      Avx2PointAdd.Phases.oddIndex, Nat.mul_mod_right, Nat.reduceEqDiff, ite_true,
      Nat.add_mod, Nat.mul_mod_right, Nat.reduceMod, zero_add, ite_false] at he ho
    rw [unpackPair_toNat]
    simp only [Avx2PointAdd.word, BitVec.toNat_ofNat]
    have hem : a (Avx2PointAdd.Phases.evenIndex k) < 2^32 := by
      simpa only [Avx2PointAdd.Phases.evenIndex] using (show a ⟨2*k.val, by omega⟩ < 2^32 by omega)
    have hom : a (Avx2PointAdd.Phases.oddIndex k) < 2^32 := by
      simpa only [Avx2PointAdd.Phases.oddIndex] using (show a ⟨2*k.val+1, by omega⟩ < 2^32 by omega)
    rw [Nat.mod_eq_of_lt hem, Nat.mod_eq_of_lt hom]
    simp only [Avx2PointAdd.Phases.evenIndex, Avx2PointAdd.Phases.oddIndex]
    omega
  fin_cases c
  · exact hbound P.X hP.1
  · exact hbound P.Y hP.2.1
  · exact hbound P.Z hP.2.2.1
  · exact hbound P.T hP.2.2.2

theorem serial_readPoint_value (s : GlobalState) (r : Pointer) :
    SerialPoint.pointValue (SerialContracts.readPoint s r) =
      Conformance.BackendExecution.readPoint s r := by
  have hcoord (c : Fin 4) :
      (SerialPoint.value (SerialFieldMul.unsigned
        (SerialFieldMul.readLimbs s (r.add (BitVec.ofNat 64 (40*c.val))))) : Tables.F) =
      Conformance.BackendExecution.readCoordinate s r c := by
    unfold SerialPoint.value Conformance.BackendExecution.readCoordinate Field.serialValue
    congr 1
    fin_cases c <;>
      simp [SerialFieldMul.decode, Field.decode51, SerialFieldMul.radix, Fin.sum_univ_succ,
        SerialFieldMul.unsigned, SerialFieldMul.readLimbs, Pointer.add_add] <;> ring
  ext
  · simpa [SerialPoint.pointValue, SerialContracts.readPoint, SerialContracts.readField,
      Conformance.BackendExecution.readPoint] using hcoord 0
  · simpa [SerialPoint.pointValue, SerialContracts.readPoint, SerialContracts.readField,
      Conformance.BackendExecution.readPoint] using hcoord 1
  · simpa [SerialPoint.pointValue, SerialContracts.readPoint, SerialContracts.readField,
      Conformance.BackendExecution.readPoint] using hcoord 2
  · simpa [SerialPoint.pointValue, SerialContracts.readPoint, SerialContracts.readField,
      Conformance.BackendExecution.readPoint] using hcoord 3

theorem unpackStore_pointTight (s : GlobalState) (r : Pointer) (P : Avx2PointAdd.Point)
    (h : SmallRange s.mem r 160) (hP : Avx2PointAdd.pointReduced P) :
    SerialPoint.PointTight (SerialContracts.readPoint
      {s with mem := unpackStore s.mem r (packPoint P)} r) := by
  have hc (c : Fin 4) :
      SerialPoint.Tight (SerialFieldMul.unsigned
        (SerialFieldMul.readLimbs {s with mem := unpackStore s.mem r (packPoint P)}
          (r.add (BitVec.ofNat 64 (40*c.val))))) := by
    have he : SerialFieldMul.readLimbs {s with mem := unpackStore s.mem r (packPoint P)}
        (r.add (BitVec.ofNat 64 (40*c.val))) = unpackSerial (packPoint P) c := by
      funext k
      simpa only [SerialFieldMul.readLimbs, Pointer.add_add, ← BitVec.ofNat_add] using
        unpackStore_word s.mem r (packPoint P) h c k
    rw [he]
    exact unpackSerial_tight hP c
  exact ⟨by simpa [SerialContracts.readPoint, SerialContracts.readField] using hc 0,
    by simpa [SerialContracts.readPoint, SerialContracts.readField] using hc 1,
    by simpa [SerialContracts.readPoint, SerialContracts.readField] using hc 2,
    by simpa [SerialContracts.readPoint, SerialContracts.readField] using hc 3⟩

theorem unpack_run_validPoint (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (r : Pointer) (Q : Extended Tables.F)
    (V : GroupPoint) (hwf : s.WF) (hready : OutputReady E r) (h : SmallRange s.mem r 160)
    (hp : PointAt .afterB E Q) (hr : Tables.Represents Q V) :
    ∃ (P : ValidPoint) (after : GlobalState),
      (avx2Kernel p g).runFrom E 34 s = .value (.nil, after) ∧
      Dalek.OutputFrame s after r 160 ∧ P.curve = V ∧
      Dalek.ReadBytes after r 160 P.bytes := by
  obtain ⟨raw, hraw, hQ, hreads⟩ := hp
  let after : GlobalState := {s with mem := unpackStore s.mem r (packPoint raw)}
  have hout : SmallRange after.mem r 160 := unpackStore_range h _
  have ht := unpackStore_pointTight s r raw h hraw
  have hv : Tables.Represents (SerialPoint.pointValue (SerialContracts.readPoint after r)) V := by
    rw [serial_readPoint_value, unpackStore_readPoint s r raw h hraw, hQ]
    exact hr
  refine ⟨readValidPoint after r V ht hv, after, ?_,
    unpackStore_frame s r (packPoint raw) hwf h, rfl, hout, ?_⟩
  · have hrun := unpack_run p g E r (packPoint raw) s h
    rwa [unpackInput_of_ready hready hreads] at hrun
  · exact (readKeyWords_bytes after r hout).symm

end Agave.Ed25519.DoubleBase.ExecutionAvx2
