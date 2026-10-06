module

public import SSA.Projects.RIR.Semantics.Operations.Memory
import Init.Data.List.Scan.Lemmas

/-!
Restricted `inbounds nusw nuw` semantics for allocations still represented in `MemoryState`.
This is exact only on live, non-wrapping allocations smaller than 2^63 bytes.
LLVM also permits some GEPs into dead objects; those executions are outside this
module's refinement contract. In particular, this is not an unconditional LLVM
semantics for dangling pointers or arbitrary machine addresses.
-/

namespace LeanMLIR.RIR.Operation

@[expose] public section

/-- The signed range of the default address space's 64-bit pointer index type. -/
def GepSignedRange (x : Int) : Prop := -(2^63) ≤ x ∧ x < 2^63

instance (x : Int) : Decidable (GepSignedRange x) := by
  unfold GepSignedRange
  infer_instance

/-- Preserve both signed and unsigned values when truncating a wide index, and
check both signed and unsigned scaling. Smaller indices are still sign-extended. -/
def gepInboundsIndex (stride : Nat) (index : PoisonOr (BitVec w)) : PoisonOr Int := do
  let index ← index
  let signed := index.toInt
  if GepSignedRange signed ∧ GepSignedRange (signed * stride) ∧
      index.toNat < 2^64 ∧ (BitVec.ofInt 64 signed).toNat * stride < 2^64 then
    return signed * stride
  else .poison

/-- All scaled offsets and cumulative offsets fit the signed index width. Every
intermediate object-relative address, including the base, lies in [0, length].
The closed upper endpoint deliberately admits one-past pointers. Nonnegative
steps capture `nuw` address addition: a negative signed step, interpreted unsigned,
would wrap when both its source and target remain in this same allocation. -/
def GepInboundsOffsets (length base : Nat) (offsets : List Int) : Prop :=
  (∀ off ∈ offsets, 0 ≤ off ∧ GepSignedRange off) ∧
  (∀ off ∈ offsets.scanl (· + ·) 0,
    GepSignedRange off ∧ 0 ≤ (base : Int) + off ∧ (base : Int) + off ≤ length)

instance (length base : Nat) (offsets : List Int) :
    Decidable (GepInboundsOffsets length base offsets) := by
  unfold GepInboundsOffsets
  infer_instance

/-- The common compiler-generated single-index case needs only a nonnegative
offset and an endpoint inside the small live allocation. -/
theorem gepInboundsOffsets_singleton {length base : Nat} {off : Int}
    (hsize : length < 2^63) (hoff : 0 ≤ off)
    (hwithin : (base : Int) + off ≤ length) :
    GepInboundsOffsets length base [off] := by
  simp [GepInboundsOffsets, GepSignedRange, List.scanl_cons, List.scanl_nil]
  omega

/-- The live-allocation subset of `inbounds`. Failures produce a poison pointer,
not immediate UB; consuming it in a load/store will then cause UB as usual.
The explicit allocation lookup is also satisfied by installed byte globals. -/
def gepInboundsLive (mem : MemoryState) (ptr : PoisonOr Pointer)
    (offsets : List (PoisonOr Int)) : PoisonOr Pointer := do
  let ptr ← ptr
  let offsets ← offsets.mapM id
  let some block := mem[ptr.id]? | .poison
  if block.length < 2^63 ∧ GepInboundsOffsets block.length ptr.offset.toNat offsets then
    return ptr.add (BitVec.ofInt 64 offsets.sum)
  else .poison

theorem gepInboundsIndex_eq (stride : Nat) (index : BitVec w)
    (hindex : GepSignedRange index.toInt)
    (hmul : GepSignedRange (index.toInt * stride))
    (htrunc : index.toNat < 2^64)
    (humul : (BitVec.ofInt 64 index.toInt).toNat * stride < 2^64) :
    gepInboundsIndex stride (.value index) = .value (index.toInt * stride) := by
  simp only [gepInboundsIndex, PoisonOr.value_bind]
  exact ite_eq_left ⟨hindex, hmul, htrunc, humul⟩

private theorem collect_values (offsets : List Int) :
    List.mapM id (offsets.map PoisonOr.value) = PoisonOr.value offsets := by
  induction offsets with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, ih]

/-- Conditional exactness of address formation in the live-object model. The
premises expose the live allocation, its size, arithmetic limits and every
intermediate in-object address; none are hidden in an uninterpreted contract. -/
theorem gepInboundsLive_eq {mem : MemoryState} {ptr : Pointer} {block : MemoryBlock}
    {offsets : List Int} (hlive : mem[ptr.id]? = some block)
    (hsize : block.length < 2^63)
    (hwithin : GepInboundsOffsets block.length ptr.offset.toNat offsets) :
    gepInboundsLive mem (.value ptr) (offsets.map .value) =
      .value (ptr.add (BitVec.ofInt 64 offsets.sum)) := by
  simp only [gepInboundsLive, PoisonOr.value_bind, collect_values, hlive]
  exact ite_eq_left ⟨hsize, hwithin⟩

/-- An out-of-object intermediate address poisons the result even if a later
offset would return the final pointer to the object. -/
theorem gepInboundsLive_poison_of_invalid {mem : MemoryState} {ptr : Pointer}
    {block : MemoryBlock} {offsets : List Int} (hlive : mem[ptr.id]? = some block)
    (hbad : ¬GepInboundsOffsets block.length ptr.offset.toNat offsets) :
    gepInboundsLive mem (.value ptr) (offsets.map .value) = .poison := by
  simp only [gepInboundsLive, PoisonOr.value_bind, collect_values, hlive]
  exact ite_eq_right (fun h => hbad h.2)

/-- A concrete, non-wrapping placement of an allocation makes every accepted
nonnegative in-object step satisfy LLVM's unsigned machine-address addition rule.
Physical allocation placement is an explicit premise, not part of `Pointer`. -/
theorem gepInbounds_address_no_wrap {address length base delta : Nat}
    (hlayout : address + length < 2^64) (hwithin : base + delta ≤ length) :
    address + base + delta < 2^64 := by
  omega

/-- Conversely, moving backwards within the object wraps unsigned addition of
the sign-extended negative offset. This explains why the combined flags poison
such a step even though `inbounds` alone could allow it. -/
theorem gepInbounds_negative_wrap {address base delta : Nat}
    (hdelta : 0 < delta) (hwithin : delta ≤ base) (hsmall : delta < 2^64) :
    2^64 ≤ address + base + (2^64 - delta) := by
  omega

end
end LeanMLIR.RIR.Operation
