import Mathlib.Data.Fin.VecNotation
import SSA.Projects.Firedancer.Curve
import SSA.Projects.Firedancer.Ed25519
import SSA.Projects.SLLVM.Dialect

namespace Firedancer.Ref
open LeanMLIR SLLVM

def decodeFieldElem (limbs: Fin 5 → ℕ) :=
  let limbValue (i: Fin 5): ZMod p := limbs i * ((2)^(51 * i.toNat))
  limbValue 0 + limbValue 1 + limbValue 2 + limbValue 3 + limbValue 4

def readLimb? (p: Pointer) (i: Fin 5) (m: MemoryState) := do
  let liveBlock ← m.live? p.id
  let limb := liveBlock.bytes.extractLsb' (p.offsetInBits + 64 * i.toNat) 64
  return limb.toNat

def readFieldElem? (p: Pointer) (m: MemoryState) := do
  let l0 ← readLimb? p 0 m
  let l1 ← readLimb? p 1 m
  let l2 ← readLimb? p 2 m
  let l3 ← readLimb? p 3 m
  let l4 ← readLimb? p 4 m
  return decodeFieldElem ![l0, l1, l2, l3, l4]

/-- Equivalent states have the same live blocks, and a limb read looks at
nothing else. -/
theorem readLimb?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) (i : Fin 5) :
    readLimb? p i s.mem = readLimb? p i s'.mem := by
  simp only [readLimb?, h.2 p.id]

theorem readFieldElem?_of_equiv {s s' : GlobalState} (h : s ≈ s') (p : Pointer) :
    readFieldElem? p s.mem = readFieldElem? p s'.mem := by
  simp only [readFieldElem?, readLimb?_of_equiv h]

end Firedancer.Ref
