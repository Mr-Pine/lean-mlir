import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Avx2CFG
import SSA.Projects.Agave.Ed25519.Proof.Conformance.BackendObservation
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionPacking
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement

/-! Pure state and byte-level contracts at the AVX2 double-base helper boundary.
No imported helper execution theorem is required by these definitions. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR PointArithmetic
open Reduce64.Execution (SmallRange storeOutputs outputWord)
open Conformance.BackendExecution (Invocation readPoint)

abbrev PackedBlocks := Avx2FieldMul.Execution.Blocks

def args2 (r a : Pointer) : Vals [.ptr, .ptr] :=
  .cons (.value r) (.cons (.value a) .nil)

def args3 (r a b : Pointer) : Vals [.ptr, .ptr, .ptr] :=
  .cons (.value r) (.cons (.value a) (.cons (.value b) .nil))

/-- Read the four logical elements using the imported multiplication kernel's
physical A/B/C/D lane layout. -/
def packedPoint (m : MemoryState) (p : Pointer) : Avx2PointAdd.Point :=
  let limbs := Avx2FieldMul.Execution.inputNat (Avx2FieldMul.Execution.readBlocks m p)
  ⟨limbs 0, limbs 1, limbs 2, limbs 3⟩

def serialLimbsBounded (s : GlobalState) (p : Pointer) : Prop :=
  ∀ (coordinate : Fin 4) (limb : Fin 5),
    (s.mem.readAt (p.add (BitVec.ofNat 64
      (40 * coordinate.val + 8 * limb.val))) 64).toNat < 2 ^ 51

/-- Only the four live caller objects need a signed-small allocation witness.
Scalar values are the complete 256-bit memory inputs; no canonical-scalar or
nonzero-digit premise is imposed. -/
structure Input (i : Invocation) (s : GlobalState) : Prop where
  wellFormed : s.WF
  output : SmallRange s.mem i.output 160
  scalarA : SmallRange s.mem i.scalarA 32
  pointA : SmallRange s.mem i.pointA 160
  scalarB : SmallRange s.mem i.scalarB 32
  pointLimbs : serialLimbsBounded s i.pointA

/-- Panic-location pointers are never read on the successful path. The only
loaded global is the certified 10,240-byte basepoint table. -/
structure GlobalsReady (g : Avx2CFG.Globals) (s : GlobalState) : Prop where
  baseAddress : g.address2.offset = 0
  basePresent : Tables.avx2BaseGlobal.Present g.address2.id s.mem

/-- Exact byte-level multiplication behavior, before imposing field bounds.
Reads happen before the five writes, so this contract also admits aliases. -/
def MulContract (call : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (r a b : Pointer) (s : GlobalState), s.WF →
    SmallRange s.mem r 160 → SmallRange s.mem a 160 → SmallRange s.mem b 160 →
    call (args3 r a b) s = .value (.nil, {s with mem := (storeOutputs s.mem r
      (Avx2FieldMul.Execution.rawColumns4
        (Avx2FieldMul.Execution.readBlocks s.mem a)
        (Avx2FieldMul.Execution.readBlocks s.mem b)))})

/-- Exact byte-level square/negative-square behavior. The sign of logical lane
D is built into the concrete column computation, not supplied as a premise. -/
def SquareContract (call : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (r a : Pointer) (s : GlobalState), s.WF →
    SmallRange s.mem r 160 → SmallRange s.mem a 160 →
    call (args2 r a) s = .value (.nil, {s with mem := (storeOutputs s.mem r
      (Avx2SquareNegateD.Execution.signedColumns4
        (Avx2SquareNegateD.Execution.readBlocks s.mem a)))})

/-- Caller-visible frame for the table constructor. It may allocate and release
private stack objects; every prior live range and every byte disjoint from its
output is preserved. This excludes helper corruption of NAF arrays, globals,
and input scalars without prescribing the helper's internal stack layout. -/
structure TableFrame (before after : GlobalState) (output : Pointer) : Prop where
  wellFormed : after.WF
  live : ∀ (q : Pointer) (bytes : Nat),
    SmallRange before.mem q bytes → SmallRange after.mem q bytes
  read : ∀ (q : Pointer) (width : Nat),
    (Range.of q width).Disjoint (Range.of output (1280 * 8)) →
    after.mem.readAt q width = before.mem.readAt q width

/-- Ordinary source-level contract of the separately compiled width-five table
constructor. Every one of the eight output records has a reduced physical limb
representation and decodes to the corresponding concrete cached odd multiple.
The input and output are disjoint, as they are for the kernel's fresh stack
table. No property of the double-base loop appears in this contract. -/
def TableContract (call : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (r a : Pointer) (s : GlobalState), s.WF →
    SmallRange s.mem r 1280 → SmallRange s.mem a 160 →
    (Range.of r (1280 * 8)).Disjoint (Range.of a (160 * 8)) →
    serialLimbsBounded s a →
    ∃ s' : GlobalState,
      call (args2 r a) s = .value (.nil, s') ∧
      TableFrame s s' r ∧
      ∀ k : Fin 8,
        let point := packedPoint s'.mem (r.add (BitVec.ofNat 64 (160 * k.val)))
        Avx2PointAdd.pointReduced point ∧
        Avx2PointAdd.pointValue point =
          avx2Cache (Tables.avx2Width5 (readPoint s a) k)

structure HelperContracts (p : Avx2CFG.Primitives) : Prop where
  table : TableContract p.call0
  square : SquareContract p.call1
  mul : MulContract p.call2


end Agave.Ed25519.DoubleBase.ExecutionAvx2
