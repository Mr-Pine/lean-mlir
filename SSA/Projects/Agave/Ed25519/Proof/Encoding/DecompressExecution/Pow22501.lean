import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Pow2kWords
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionMemory

/-! The exact addition-chain limb schedule, its caller bounds, and field value.
The imported pointer program is linked separately in Pow22501Execution. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
open LeanMLIR.RIR
open SerialFieldMul
open Reduce64.Execution (SmallRange)

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Limb values paired with the invariant restored by each field kernel. -/
structure TightWords where
  limbs : Words
  tight : SerialPoint.Tight (unsigned limbs)

namespace TightWords

def square (a : TightWords) (n : Nat) : TightWords :=
  ⟨Pow2k.iterateSquare n a.limbs, Pow2k.iterateSquare_tight n a.limbs a.tight⟩

def mul (a b : TightWords) : TightWords :=
  ⟨machine a.limbs b.limbs, machine_tight a.limbs b.limbs
    (SerialPoint.tight_bounded _ a.tight) (SerialPoint.tight_bounded _ b.tight)⟩

theorem square_value (a : TightWords) (n : Nat) :
    wordValue (a.square n).limbs = wordValue a.limbs ^ (2 ^ n) :=
  Pow2k.iterateSquare_value n a.limbs a.tight

theorem mul_value (a b : TightWords) :
    wordValue (a.mul b).limbs = wordValue a.limbs * wordValue b.limbs :=
  machine_value a.limbs b.limbs
    (SerialPoint.tight_bounded _ a.tight) (SerialPoint.tight_bounded _ b.tight)

end TightWords

/-- The same exact limb schedule without bound witnesses. Its machine execution
is valid for arbitrary u64 limbs; field interpretation adds the tight invariant. -/
def rawWordChain (x : Words) : Words × Words :=
  let t0 := Pow2k.iterateSquare 1 x
  let t1a := Pow2k.iterateSquare 1 t0
  let t1 := Pow2k.iterateSquare 1 t1a
  let t2 := machine x t1
  let t3 := machine t0 t2
  let t4 := Pow2k.iterateSquare 1 t3
  let t5 := machine t2 t4
  let t6 := Pow2k.iterateSquare 5 t5
  let t7 := machine t6 t5
  let t8 := Pow2k.iterateSquare 10 t7
  let t9 := machine t8 t7
  let t10 := Pow2k.iterateSquare 20 t9
  let t11 := machine t10 t9
  let t12 := Pow2k.iterateSquare 10 t11
  let t13 := machine t12 t7
  let t14 := Pow2k.iterateSquare 50 t13
  let t15 := machine t14 t13
  let t16 := Pow2k.iterateSquare 100 t15
  let t17 := machine t16 t15
  let t18 := Pow2k.iterateSquare 50 t17
  let t19 := machine t18 t13
  (t19, t3)

/-- The order and operand dependencies of all actual helper calls in bb0. -/
def wordChain (x : TightWords) : TightWords × TightWords :=
  let t0 := x.square 1
  let t1a := t0.square 1
  let t1 := t1a.square 1
  let t2 := x.mul t1
  let t3 := t0.mul t2
  let t4 := t3.square 1
  let t5 := t2.mul t4
  let t6 := t5.square 5
  let t7 := t6.mul t5
  let t8 := t7.square 10
  let t9 := t8.mul t7
  let t10 := t9.square 20
  let t11 := t10.mul t9
  let t12 := t11.square 10
  let t13 := t12.mul t7
  let t14 := t13.square 50
  let t15 := t14.mul t13
  let t16 := t15.square 100
  let t17 := t16.mul t15
  let t18 := t17.square 50
  let t19 := t18.mul t13
  (t19, t3)

/-- The word schedule denotes the same chain proved in DecompressSqrt. -/
theorem wordChain_value (x : TightWords) :
    (wordValue (wordChain x).1.limbs, wordValue (wordChain x).2.limbs) =
      Decompress.pow22501 (wordValue x.limbs) := by
  simp only [wordChain, TightWords.square_value, TightWords.mul_value,
    Decompress.pow22501, show (2 : Nat) ^ 1 = 2 from rfl]

attribute [local irreducible] SerialFieldMul.machine Pow2k.iterateSquare

theorem rawWordChain_eq (x : TightWords) :
    rawWordChain x.limbs = ((wordChain x).1.limbs, (wordChain x).2.limbs) := rfl

/-- Both returned fields restore the bounds required by all subsequent calls. -/
theorem wordChain_tight (x : TightWords) :
    SerialPoint.Tight (unsigned (wordChain x).1.limbs) ∧
      SerialPoint.Tight (unsigned (wordChain x).2.limbs) :=
  ⟨(wordChain x).1.tight, (wordChain x).2.tight⟩

end Agave.Ed25519.Encoding.Decompress.Execution.Pow22501
