import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.SerialCFG
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Contract
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Refinement
import SSA.Projects.Agave.Ed25519.Proof.Tables.Dynamic
import SSA.Projects.Agave.Ed25519.Proof.Tables.Memory
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionGlobals

/-!
# Local contracts for the serial double-base helper calls

Every contract below concerns one named external primitive. None mentions the
double-base CFG, its execution result, the NAF loop, or `serialMath`. These are
the helper boundaries needed by a future whole-CFG composition. Merely
constructing this record is not a proof of that composition.

The memory decoder follows the physical Rust order. Completed/extended points
are X,Y,Z,T; projective points are X,Y,Z; Niels records are Y+X,Y-X,Z,2dT.
The field-multiplication boundary can be linked to the already proved imported
field kernel instead of assuming its arithmetic correctness.
-/
namespace Agave.Ed25519.DoubleBase.SerialContracts

open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul (Limbs Bounded unsigned readLimbs)
open SerialPoint (LimbPoint PointBounded PointTight Tight)
open PointArithmetic

def readField (s : GlobalState) (p : Pointer) : Limbs := unsigned (readLimbs s p)

def readPoint (s : GlobalState) (p : Pointer) : LimbPoint :=
  ⟨readField s p, readField s (p.add 40), readField s (p.add 80),
    readField s (p.add 120)⟩

def readProjective (s : GlobalState) (p : Pointer) : LimbPoint :=
  ⟨readField s p, readField s (p.add 40), readField s (p.add 80), fun _ => 0⟩

/-- Swap the two physical Niels coordinates to match `serialCache`. -/
def readCached (s : GlobalState) (p : Pointer) : LimbPoint :=
  ⟨readField s (p.add 40), readField s p, readField s (p.add 80),
    readField s (p.add 120)⟩

def readAffineCached (s : GlobalState) (p : Pointer) : LimbPoint :=
  ⟨readField s (p.add 40), readField s p, fun _ => 0, readField s (p.add 80)⟩

structure Invocation where
  output : Pointer
  scalarA : Pointer
  pointA : Pointer
  scalarB : Pointer

def Invocation.args (i : Invocation) : Vals [.ptr, .ptr, .ptr, .ptr] :=
  .cons (.value i.output) (.cons (.value i.scalarA)
    (.cons (.value i.pointA) (.cons (.value i.scalarB) .nil)))

/-- Caller facts contain allocation and representation data only. The source
scalar invariant is a 255-bit bound, needed to rule out a surviving terminal
NAF carry. No bound is placed on a future loaded digit or table index. -/
structure InputState (i : Invocation) (s : GlobalState) (a b : BitVec 256)
    (A : LimbPoint) : Prop where
  wellFormed : s.WF
  output : SmallRange s.mem i.output 160
  scalarA : SmallRange s.mem i.scalarA 32
  scalarB : SmallRange s.mem i.scalarB 32
  pointA : SmallRange s.mem i.pointA 160
  bytesA : s.mem.readAt i.scalarA 256 = a
  bytesB : s.mem.readAt i.scalarB 256 = b
  scalarABound : a.toNat < 2 ^ 255
  scalarBBound : b.toNat < 2 ^ 255
  limbsA : readPoint s i.pointA = A
  pointTight : PointTight A

/-- Only the identity field and the basepoint table are read on the normal
path. Addresses 1 and 2 serve panic metadata and need no contents once those
paths have been excluded. Each live global is constrained at its true size. -/
structure GlobalsReady (g : SerialCFG.Globals) (s : GlobalState) : Prop where
  identityOffset : g.address0.offset = 0
  identity : Verifier.Execution.identityOne.Present g.address0.id s.mem
  baseOffset : g.address3.offset = 0
  base : Tables.serialBaseGlobal.Present g.address3.id s.mem

def Disjoint (a : Pointer) (aBytes : Nat) (b : Pointer) (bBytes : Nat) : Prop :=
  (Range.of a (8 * aBytes)).Disjoint (Range.of b (8 * bBytes))

/-- A primitive returns after erasing its own stack frame. It preserves the
shape of every caller allocation and all reads disjoint from its output. -/
structure WritesOnly (out : Pointer) (bytes : Nat) (before after : GlobalState) : Prop where
  wellFormed : after.WF
  allocationMonotone : before.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock
  allocationShape : ∀ (id : BlockId),
    (after.mem[id]?).map MemoryBlock.length = (before.mem[id]?).map MemoryBlock.length
  readFrame : ∀ (q : Pointer) (bits : Nat),
    (Range.of q bits).Disjoint (Range.of out (8 * bytes)) →
    after.mem.readAt q bits = before.mem.readAt q bits

/-- Shape preservation transports a live small-range premise across a call,
including when that range is the primitive's output. -/
theorem WritesOnly.smallRange (h : WritesOnly out bytes before after)
    (hrange : SmallRange before.mem q count) : SmallRange after.mem q count := by
  obtain ⟨block, hblock, hsmall, hsize⟩ := hrange
  have hshape := h.allocationShape q.id
  rw [hblock] at hshape
  cases hafter : after.mem[q.id]? with
  | none => simp [hafter] at hshape
  | some block' =>
      have hlength : block'.length = block.length := by
        simpa [hafter] using hshape
      exact ⟨block', hafter, by omega, by omega⟩

/-- Physical output equality with the proved natural-number point schedule. -/
def UnaryPointContract (helper : Vals [.ptr, .ptr] → EffectM (Vals []))
    (inputBytes : Nat) (readInput : GlobalState → Pointer → LimbPoint)
    (formula : LimbPoint → LimbPoint) : Prop :=
  ∀ (s : GlobalState) (out input : Pointer), s.WF → SmallRange s.mem out 160 →
    SmallRange s.mem input inputBytes → Disjoint out 160 input inputBytes →
    PointTight (readInput s input) →
    ∃ final, helper (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, final) ∧ WritesOnly out 160 s final ∧
      readPoint final out = formula (readInput s input) ∧
      PointBounded (readPoint final out)

def BinaryPointContract (helper : Vals [.ptr, .ptr, .ptr] → EffectM (Vals []))
    (cachedBytes : Nat) (readCache : GlobalState → Pointer → LimbPoint)
    (formula : LimbPoint → LimbPoint → LimbPoint) : Prop :=
  ∀ (s : GlobalState) (out input cached : Pointer), s.WF → SmallRange s.mem out 160 →
    SmallRange s.mem input 160 → SmallRange s.mem cached cachedBytes →
    Disjoint out 160 input 160 → Disjoint out 160 cached cachedBytes →
    PointTight (readPoint s input) → PointBounded (readCache s cached) →
    ∃ final, helper (.cons (.value out) (.cons (.value input)
      (.cons (.value cached) .nil))) s = .value (.nil, final) ∧
      WritesOnly out 160 s final ∧
      readPoint final out = formula (readPoint s input) (readCache s cached) ∧
      PointBounded (readPoint final out)

/-- Exactly `pow2k(1)`, the only exponent passed by this caller. -/
def SquareContract (helper : Vals [.ptr, .ptr, .bv 32] → EffectM (Vals [])) : Prop :=
  ∀ (s : GlobalState) (out input : Pointer), s.WF → SmallRange s.mem out 40 →
    SmallRange s.mem input 40 → Disjoint out 40 input 40 →
    Bounded (readField s input) →
    ∃ final, helper (.cons (.value out) (.cons (.value input)
      (.cons (.value 1#32) .nil))) s = .value (.nil, final) ∧
      WritesOnly out 40 s final ∧
      readField final out = SerialPoint.sq (readField s input) ∧
      Tight (readField final out)

/-- Only the eight dynamic records are supplied by the constructor. The
width-eight basepoint table remains an explicit caller global. -/
def TableContract (helper : Vals [.ptr, .ptr] → EffectM (Vals [])) : Prop :=
  ∀ (s : GlobalState) (out input : Pointer), s.WF → SmallRange s.mem out 1280 →
    SmallRange s.mem input 160 → Disjoint out 1280 input 160 →
    PointTight (readPoint s input) →
    ∃ final, helper (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, final) ∧ WritesOnly out 1280 s final ∧
      ∀ k : Fin 8,
        PointBounded (readCached final (out.add (BitVec.ofNat 64 (160 * k.val)))) ∧
        SerialPoint.pointValue (readCached final (out.add (BitVec.ofNat 64 (160 * k.val)))) =
          serialCache _root_.Ed25519.d
            (Tables.serialWidth5 _root_.Ed25519.d (SerialPoint.pointValue (readPoint s input)) k)

/-- Explicit, non-circular helper assumptions. No panic contract is needed:
the caller must prove its panic blocks unreachable from the NAF construction. -/
structure Helpers (p : SerialCFG.Primitives) : Prop where
  table : TableContract p.call0
  double : UnaryPointContract p.call1 120 readProjective SerialPoint.doubleCompleted
  multiply : p.call2 = SerialFieldMul.kernel.call
  cachedSub : BinaryPointContract p.call3 160 readCached SerialPoint.cachedSubCompleted
  cachedAdd : BinaryPointContract p.call5 160 readCached SerialPoint.cachedAddCompleted
  affineSub : BinaryPointContract p.call6 120 readAffineCached
    (fun P C => SerialPoint.affineSubCompleted P C.X C.Y C.T)
  affineAdd : BinaryPointContract p.call7 120 readAffineCached
    (fun P C => SerialPoint.affineAddCompleted P C.X C.Y C.T)
  square : SquareContract p.call8

/-- The multiplication assumption resolves a named call to an independently
proved kernel. The arithmetic and result bounds come from `kernel_correct`. -/
theorem field_helper_correct (p : SerialCFG.Primitives)
    (hlink : p.call2 = SerialFieldMul.kernel.call)
    (out a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hout : SmallRange s.mem out 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40) (hA : Bounded (readField s a))
    (hB : Bounded (readField s b)) :
    ∃ output : Fin 5 → BitVec 64,
      p.call2 (.cons (.value out) (.cons (.value a) (.cons (.value b) .nil))) s =
        .value (.nil, {s with mem := SerialFieldMul.storeLimbs s.mem out output}) ∧
      SerialFieldMul.decode (unsigned output) % SerialFieldMul.modulus =
        (SerialFieldMul.decode (readField s a) *
          SerialFieldMul.decode (readField s b)) % SerialFieldMul.modulus ∧
      (∀ i, i ≠ 1 → unsigned output i < SerialFieldMul.radix) ∧
      unsigned output 1 < SerialFieldMul.radix + 2^13 ∧ Bounded (unsigned output) := by
  rw [hlink]
  exact SerialFieldMul.kernel_correct out a b s hwf hout ha hb hA hB

end Agave.Ed25519.DoubleBase.SerialContracts
