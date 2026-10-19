module

public import MLIR.Run.Tactic
public import Examples.Mlir.swap_elements

namespace Examples.Mlir

open MLIR

/-! ## Specification -/

@[expose] public section

/-- The byte offset of `array[i]`, for `i ≥ 0`. -/
abbrev swap_elements.off (i : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 ((i.signExtend 64).toNat * 4)

/-- `&array[i]`. -/
abbrev swap_elements.elem (array : Pointer) (i : BitVec 32) : Pointer :=
  array.add (swap_elements.off i)

/-- `array[index_a]` and `array[index_b]` swapped. -/
abbrev swap_elements.spec (m : MemoryState) (array : Pointer) (index_a index_b : BitVec 32) :
    MemoryState :=
  let a := swap_elements.elem array index_a
  let b := swap_elements.elem array index_b
  (m.storeAt a (m.readAt b 32)).storeAt b (m.readAt a 32)

end

/-! ## Proof -/

/-! ## Memory
To reason about memory, we have the `GlobalState` which holds two things:
- A global allocation counter
- The memory data itself, as a HashMap from blocks to `BitVec`s

We also carry a well-formedness hypothesis `s.WF` which states
- No block above the allocation counter is allocated
- The `0` block is not allocated
- Stuff about loaded globals

Most of the time, you will probably want to reason about allocated memory with enough space.
The following predicates exist (`m : MemoryState`, `p: Pointer`, `w: Nat` (width of accessed memory)):
- `InBounds m p w`: `p` is allocated in `m` with at least `w` bits.
- `Live m p w`: `InBounds m p w` ∧ the block is live (after `llvm.intr.lifetime_begin)
- `Writable m p`: `p` is allocated a writable block
- `Fits m p w`: `Live m p w` and all `w` bits are allocated
- `Room m p w`: `Live m p w ∧ Writable m p`

The `step_*` tactics try to transport these facts to the new state for state-changing instructions.
-/

/-- `swap_elements` swaps `array[index_a]` and `array[index_b]`; the indices may be equal. -/
public theorem swap_elements.call_eq (array : Pointer) (index_a index_b : BitVec 32)
    (s : GlobalState) (hwf : s.WF)
    (hla : (index_a.signExtend 64).toNat * 4 < 2 ^ 63)
    (hlb : (index_b.signExtend 64).toNat * 4 < 2 ^ 63)
    (hova : ¬array.offset.uaddOverflow (swap_elements.off index_a))
    (hovb : ¬array.offset.uaddOverflow (swap_elements.off index_b))
    (ha : Fits s.mem (swap_elements.elem array index_a) 32)
    (hb : Fits s.mem (swap_elements.elem array index_b) 32)
    (ha : Writable s.mem array) :
    swap_elements.call
        (swap_elements.args (.value array) (.value index_a) (.value index_b)) s =
      .value (.nil, { s with mem := swap_elements.spec s.mem array index_a index_b }) := by
  func_init
  block_init
  -- `int temp = array[index_a];`
  step_pure
  step_pure [hla]
  step_load with transparent temp
  -- `array[index_b]`
  step_pure
  step_pure [hlb]
  step_load
  -- `array[index_a] = array[index_b];`
  step_store
  -- `array[index_b] = temp;`
  step_store
  finish_block
  simp [hS]

end Examples.Mlir
