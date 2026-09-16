/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.F25519
import SSA.Projects.Firedancer.Proof.Memory

/-!
# A ref region's frame

Every `ref` region opens with a run of `alloca`s for its `fd_f25519_t`
locals, all 40 bytes, in declaration order. `fieldLocal` names them: block
ids consecutive from the entry counter, each at offset 0. A walk indexes them
by `Fin n` for its own `n` and uses the three lemmas below to keep them apart
from each other and from the caller's blocks.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- The width of one local, in bits, as `GlobalState.allocaChain` takes it. -/
def fieldW (_ : Nat) : Nat :=
  320

/-- The `n` locals of a frame, as the chain's pointers. -/
def fieldLocal (s : GlobalState) {n : Nat} (i : Fin n) : Pointer :=
  s.chainPtr fieldW i.val

@[simp]
theorem fieldLocal_id (s : GlobalState) {n : Nat} (k : Fin n) :
    (fieldLocal s k).id.id = s.alloc.nextFreeBlock + k.val := by simp [fieldLocal]

/-- Distinct locals are distinct blocks. -/
theorem fieldLocal_ne {s : GlobalState} {n : Nat} {j k : Fin n} (h : j ≠ k) :
    (fieldLocal s j).id ≠ (fieldLocal s k).id := fun he => by
  have hid := congrArg BlockId.id he
  rw [fieldLocal_id, fieldLocal_id] at hid
  exact h (Fin.val_injective (by omega))

/-- ... and no local is a block the caller holds. -/
theorem fieldLocal_ne_below {s : GlobalState} {n : Nat} {k : Fin n} {b : BlockId}
    (hb : b.id < s.alloc.nextFreeBlock) : (fieldLocal s k).id ≠ b := fun he => by
  have hid := congrArg BlockId.id he
  rw [fieldLocal_id] at hid
  omega

/-- A fresh 40-byte local reads back as five zero limbs. -/
theorem readLimb?_afterAlloca_self (s : GlobalState) (i : Fin 5) :
    readLimb? (⟨⟨s.alloc.nextFreeBlock⟩, 0⟩ : Pointer) i (s.afterAlloca (5 * 64)).mem = some 0 := by
  simp [readLimb?, live?_afterAlloca_self, Pointer.offsetInBits]

end Firedancer.Ref
