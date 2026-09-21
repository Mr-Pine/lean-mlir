module

import MLIR.Semantics.Operations.Memory
meta import MLIR.Semantics.Operations.Memory

/-! # Execution tests for `load`/`store`

Everything is run against a single 8-byte block with id `0`; block `1` is never
allocated, so it is the "dead pointer" case. -/

namespace MLIR.Tests

private abbrev Γ0 : Ctx :=
  ⟨[], []⟩

private def env0 : ⟪Γ0⟫ :=
  Env.init (fun i => nomatch i)

/-- A state with one live 8-byte block (id `0`), zero-filled. -/
private def s0 : GlobalState :=
  ⟨⟨1⟩, ⟨Std.HashMap.ofList [(⟨0⟩, ⟨8, 0⟩)]⟩⟩

/-- Pointer into block `0` at byte offset `off`. -/
private def p (off : Nat) : Pointer :=
  ⟨⟨0⟩, BitVec.ofNat 64 off⟩

/-- Pointer into the never-allocated block `1`. -/
private def pDead : Pointer :=
  ⟨⟨1⟩, 0⟩

/-- The state after a store, or `none` for UB. -/
private def store? {τ : Ty} (ptr : ⟦Ty.ptr⟧) (v : ⟦τ⟧) (s : GlobalState := s0) :
    Option GlobalState :=
  match Operation.store ptr v env0 s with
  | .value (_, s') => some s'
  | .poison => none

/-- The bits at `q`, read out of the state after a store; `none` for UB. -/
private def storeThenRead? {τ : Ty} (ptr : ⟦Ty.ptr⟧) (v : ⟦τ⟧) (q : Pointer) (w : Nat)
    (s : GlobalState := s0) : Option (BitVec w) :=
  (store? ptr v s).map (fun s' => s'.mem.readAt q w)

/-- A context with one value register of type `τ`, for `load`'s destination. -/
private abbrev Γ1 (τ : Ty) : Ctx :=
  ⟨[], [τ]⟩

/-- `load`'s result, or `none` for UB. -/
private def load? (τ : Ty) (ptr : ⟦Ty.ptr⟧) (s : GlobalState := s0) : Option ⟦τ⟧ :=
  match Operation.load (Γ := Γ1 τ) ⟨0, rfl⟩ ptr (Env.init (fun i => nomatch i)) s with
  | .value (env, _) => some (env.read (.val 0 rfl))
  | .poison => none

/-! ## Stores land where they should -/

-- a store is read back exactly
#guard
  storeThenRead? (τ := .bv 64) (.value (p 0)) (.value 0xdeadbeef#64) (p 0) 64 == some 0xdeadbeef#64

-- a store at a non-zero offset lands at that offset, and leaves byte 0 alone
#guard storeThenRead? (τ := .bv 8) (.value (p 1)) (.value 0xab#8) (p 1) 8 == some 0xab#8

#guard storeThenRead? (τ := .bv 8) (.value (p 1)) (.value 0xab#8) (p 0) 8 == some 0x00#8

-- the second store to the same place wins
#guard
  ((store? (τ := .bv 64) (.value (p 0)) (.value 1#64)).bind
          (fun s => store? (τ := .bv 64) (.value (p 0)) (.value 2#64) s)).map
      (fun s => s.mem.readAt (p 0) 64) ==
    some 2#64

-- a store to a disjoint range leaves the first one alone
#guard
  ((store? (τ := .bv 8) (.value (p 0)) (.value 0x11#8)).bind
          (fun s => store? (τ := .bv 8) (.value (p 1)) (.value 0x22#8) s)).map
      (fun s => s.mem.readAt (p 0) 16) ==
    some 0x2211#16

/-! ## UB cases -/

-- poison pointer, poison value
#guard (store? (τ := .bv 64) .poison (.value 0#64)).isNone

#guard (store? (τ := .bv 64) (.value (p 0)) .poison).isNone

-- a pointer at a type with no bit pattern cannot be stored
#guard (store? (τ := .ptr) (.value (p 0)) (.value (p 0))).isNone

-- the block does not exist
#guard (store? (τ := .bv 64) (.value pDead) (.value 0#64)).isNone

-- out of bounds: 64 bits from byte 7 of an 8-byte block
#guard (store? (τ := .bv 64) (.value (p 7)) (.value 0#64)).isNone

-- exactly in bounds: 8 bits from byte 7
#guard (store? (τ := .bv 8) (.value (p 7)) (.value 0xff#8)).isSome

/-! ## Loads -/

-- load after store returns what was stored
#guard
  ((store? (τ := .bv 64) (.value (p 0)) (.value 0x1234#64)).bind
      (fun s => load? (.bv 64) (.value (p 0)) s)) ==
    some (.value 0x1234#64)

-- a fresh block reads as zero
#guard load? (.bv 64) (.value (p 0)) == some (.value 0#64)

-- load UB: poison pointer, dead block, out of bounds, and at `ptr` type
#guard load? (.bv 64) .poison == none

#guard load? (.bv 64) (.value pDead) == none

#guard load? (.bv 64) (.value (p 7)) == none

#guard load? .ptr (.value (p 0)) == none

end MLIR.Tests
