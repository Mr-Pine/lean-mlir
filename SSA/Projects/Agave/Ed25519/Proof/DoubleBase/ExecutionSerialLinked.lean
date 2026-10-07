import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialScanPrefix
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialNAFSelection
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialReturn
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructor
import SSA.Projects.Agave.Ed25519.Proof.Tables.ConstructorConstant
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedAddProgram
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CachedSubProgram
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.AffineAddProgram
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.AffineSubProgram
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleProgram

/-!
# Concrete source callees for the serial double-base CFG

Every normal-path primitive is the separately imported function body. The
constructor itself contains the same concrete multiplication, double and
cached-add calls. The panic callback remains explicit, and the NAF-derived
guards prove that normal execution never invokes it. This module links code;
it does not assert the still-unproved whole constructor or ladder refinement.
-/
namespace Agave.Ed25519.DoubleBase.RIR
open LeanMLIR.RIR

abbrev SerialPanic := Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])

def serialConstructorPrimitives : Tables.SerialConstructor.Primitives where
  call0 := SerialFieldMul.kernel.call
  call1 := (SerialPoint.double Encoding.Decompress.Execution.Pow2k.program.call).call
  call2 := SerialPoint.cached_add.call

def serialLinkedPrimitives (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic) :
    SerialCFG.Primitives where
  call0 := (Tables.SerialConstructor.kernel serialConstructorPrimitives d2).call
  call1 := (SerialPoint.double Encoding.Decompress.Execution.Pow2k.program.call).call
  call2 := SerialFieldMul.kernel.call
  call3 := SerialPoint.cached_sub.call
  call4 := panic
  call5 := SerialPoint.cached_add.call
  call6 := SerialPoint.affine_sub.call
  call7 := SerialPoint.affine_add.call
  call8 := Encoding.Decompress.Execution.Pow2k.program.call

/-- The executable object preserves the full original outer CFG and all
separately imported normal-path callees, including the table constructor. -/
def serialLinkedKernel (g : SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (panic : SerialPanic) : Func := serialKernel (serialLinkedPrimitives d2 panic) g

/-- Scalar preparation already executes against the concrete linked program;
its proof is independent of every point helper and panic callback. -/
theorem serialLinked_prepare_scalars (g : SerialCFG.Globals)
    (d2 : Tables.SerialConstructor.Globals) (panic : SerialPanic)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) (inputA inputB : Pointer) (a b : BitVec 256)
    (hwf : s.WF) (hA : NAF.Memory.Buffer s.mem inputA 32)
    (hB : NAF.Memory.Buffer s.mem inputB 32)
    (ha : s.mem.readAt inputA 256 = a) (hb : s.mem.readAt inputB 256 = b)
    (hargA : E.args 1 = .value inputA) (hargB : E.args 3 = .value inputB) :
    ∃ final : ⟪serialKernel.Γ⟫,
      (serialLinkedKernel g d2 panic).runFrom E (0 : Fin 36) s =
        (serialLinkedKernel g d2 panic).runFrom final (16 : Fin 36) (serialNAFState8 s a b) ∧
      final.read (%103) = .value (BitVec.ofNat 64
        (startIndex (nafDigits 5 a.toNat) (nafDigits 8 b.toNat) 255)) ∧
      PrefixEq (serialInitial5 E g s) final 43 ∧
      (∀ i : Fin 256, (serialNAFState8 s a b).mem.readAt
        ((serialStackPtr s 11).add (BitVec.ofNat 64 i.val)) 8 =
          BitVec.ofInt 8 (NAF.sourceDigits 5 a.toNat i)) ∧
      (∀ i : Fin 256, (serialNAFState8 s a b).mem.readAt
        ((serialStackPtr s 10).add (BitVec.ofNat 64 i.val)) 8 =
          BitVec.ofInt 8 (NAF.sourceDigits 8 b.toNat i)) :=
  serial_prepare_scalars (serialLinkedPrimitives d2 panic) g E s inputA inputB a b
    hwf hA hB ha hb hargA hargB

end Agave.Ed25519.DoubleBase.RIR
