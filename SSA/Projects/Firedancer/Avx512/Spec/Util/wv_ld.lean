/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Mlir.Util.wv_ld
public import SSA.Projects.Firedancer.Avx512.Spec.Quad

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev IsWvPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (4 * 64) ∧ p.offset.toNat + 32 ≤ 2 ^ 64

def readWv? (p : Pointer) (m : MemoryState) : Option (Vector (BitVec 64) 4) := do
  let block ← m.live? p.id
  return Vector.ofFn fun j => block.bytes.extractLsb' (p.offsetInBits + 64 * j.val) 64

theorem readWv?_isSome {m : MemoryState} {p : Pointer} (h : IsWvPtr m p) :
    (readWv? p m).isSome := by
  obtain ⟨⟨block, hblk, -⟩, -⟩ := h
  have hlive : m.live? p.id = some block := by simp only [MemoryState.live?, hblk]
  simp [readWv?, hlive]

def readWv {p : Pointer} {m : MemoryState} (h : IsWvPtr m p) : Vector (BitVec 64) 4 :=
  (readWv? p m).get (readWv?_isSome h)

abbrev wv_ld_spec (p : Pointer) (s : GlobalState) (hp : IsWvPtr s.mem p) : Prop :=
  let invocation := runFunction (wv_ld.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s

  ∃ s' : GlobalState,
    result = .value ([(readWv hp).map PoisonOr.value]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512
