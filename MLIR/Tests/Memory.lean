module

import MLIR.Semantics.Operations.Memory
meta import MLIR.Semantics.Operations.Memory

/-! # Execution tests for `load`/`store`, `memset`/`memcpy`, lifetimes and `assume`

Everything is run against a single 8-byte block with id `0`, zeroed and defined; block `1` is not
allocated, so it is the "dangling pointer" case, until an `alloca` adds it, undefined. `memcpy`
adds block `2`, holding the bytes `01 … 08`. -/

namespace MLIR.Tests

private abbrev Γ0 : Ctx :=
  ⟨0, [], [], rfl, 0, 0⟩

private def env0 : ⟪Γ0⟫ :=
  Env.init (fun i => nomatch i)

/-- A state with one live 8-byte block (id `0`), zero-filled and defined. -/
private def s0 : GlobalState :=
  ⟨⟨1⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, .ofBytes 8 0)]⟩⟩

/-- Pointer into block `0` at byte offset `off`. -/
private def p (off : Nat) : Pointer :=
  ⟨⟨0⟩, BitVec.ofNat 64 off⟩

/-- Pointer into the unallocated block `1`. -/
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
  ⟨1, [], [τ], rfl, 0, 0⟩

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

-- a zeroed block reads as zero
#guard load? (.bv 64) (.value (p 0)) == some (.value 0#64)

-- load UB: poison pointer, dead block, out of bounds
#guard load? (.bv 64) .poison == none

#guard load? (.bv 64) (.value pDead) == none

#guard load? (.bv 64) (.value (p 7)) == none

-- a load at `ptr` type of integer bits is poison
#guard load? .ptr (.value (p 0)) == some .poison

/-! ## `memset` -/

/-- The 8 bytes of block `0` after `memset dst val len`, or `none` for UB. -/
private def memset? {w : Nat} (dst : ⟦Ty.ptr⟧) (val : ⟦Ty.bv 8⟧) (len : ⟦Ty.bv w⟧) :
    Option (BitVec 64) :=
  match Operation.memset dst val len env0 s0 with
  | .value (_, s') => some (s'.mem.readAt (p 0) 64)
  | .poison => none

-- bytes 1 … 3 are set, the others stay zero
#guard memset? (.value (p 1)) (.value 0x7f#8) (.value 3#64) == some 0x7f7f7f00#64

-- the length may have any width
#guard memset? (.value (p 0)) (.value 0xff#8) (.value 8#32) == some 0xffffffffffffffff#64

#guard memset? (.value (p 0)) (.value 0x7f#8) (.value 0#64) == some 0#64

-- UB: past the block, dead block, poison pointer or length; poison bytes too (stricter than
-- LLVM, which stores them)
#guard memset? (.value (p 4)) (.value 0x7f#8) (.value 5#64) == none

#guard memset? (.value pDead) (.value 0x7f#8) (.value 1#64) == none

#guard memset? .poison (.value 0x7f#8) (.value 1#64) == none

#guard memset? (.value (p 0)) (.value 0x7f#8) (.poison : ⟦Ty.bv 64⟧) == none

#guard memset? (.value (p 0)) .poison (.value 1#64) == none

/-! ## `memcpy` -/

/-- Blocks `0` (zeroed) and `2` (bytes `01 … 08`). -/
private def s2 : GlobalState :=
  ⟨⟨3⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, .ofBytes 8 0), (⟨2⟩, .ofBytes 8 0x0807060504030201#64)]⟩⟩

/-- Pointer into block `2` at byte offset `off`. -/
private def q (off : Nat) : Pointer :=
  ⟨⟨2⟩, BitVec.ofNat 64 off⟩

/-- Blocks `0` and `2` after `memcpy dst src len`, or `none` for UB. -/
private def memcpy? (dst src : ⟦Ty.ptr⟧) (len : ⟦Ty.bv 64⟧) : Option (BitVec 64 × BitVec 64) :=
  match Operation.memcpy dst src len env0 s2 with
  | .value (_, s') => some (s'.mem.readAt (p 0) 64, s'.mem.readAt (q 0) 64)
  | .poison => none

-- three bytes into block `0` at offset 2; the source is unchanged
#guard
  memcpy? (.value (p 2)) (.value (q 0)) (.value 3#64) ==
    some (0x0000000302010000#64, 0x0807060504030201#64)

-- from a source offset
#guard
  memcpy? (.value (p 0)) (.value (q 4)) (.value 2#64) == some (0x0605#64, 0x0807060504030201#64)

-- adjacent ranges in one block do not overlap
#guard memcpy? (.value (q 0)) (.value (q 4)) (.value 4#64) == some (0#64, 0x0807060508070605#64)

-- UB: overlapping ranges, and, stricter than LLVM, equal ones
#guard memcpy? (.value (q 0)) (.value (q 2)) (.value 4#64) == none

#guard memcpy? (.value (q 0)) (.value (q 0)) (.value 4#64) == none

-- UB: past either block, dead block, poison pointer or length
#guard memcpy? (.value (p 0)) (.value (q 6)) (.value 4#64) == none

#guard memcpy? (.value (p 6)) (.value (q 0)) (.value 4#64) == none

#guard memcpy? (.value (p 0)) (.value pDead) (.value 1#64) == none

#guard memcpy? .poison (.value (q 0)) (.value 1#64) == none

#guard memcpy? (.value (p 0)) (.value (q 0)) .poison == none

/-! ## Undefined bits -/

/-- `s0` with block `1`, 8 bytes, fresh from an `alloca`: live, its bits undefined. -/
private def sA : GlobalState :=
  s0.alloca 8

/-- Pointer into block `1` at byte offset `off`. -/
private def a (off : Nat) : Pointer :=
  ⟨⟨1⟩, BitVec.ofNat 64 off⟩

-- a load of an uninitialized `alloca` is poison, not UB
#guard load? (.bv 64) (.value (a 0)) sA == some .poison

-- stored bits are defined, the others stay undefined
#guard
  ((store? (τ := .bv 32) (.value (a 0)) (.value 7#32) sA).bind (load? (.bv 32) (.value (a 0)) ·)) ==
    some (.value 7#32)

#guard
  ((store? (τ := .bv 32) (.value (a 0)) (.value 7#32) sA).bind (load? (.bv 64) (.value (a 0)) ·)) ==
    some .poison

-- storing poison stores undefined bits, as LLVM does
#guard
  ((store? (τ := .bv 64) (.value (p 0)) .poison).bind (load? (.bv 8) (.value (p 3)) ·)) ==
    some .poison

-- a vector with a poison lane: that lane alone reads back poison
#guard
  ((store? (τ := .vec 2 32) (.value (p 0)) #v[.value 5#32, .poison]).bind
      (load? (.vec 2 32) (.value (p 0)) ·)) ==
    some #v[.value 5#32, .poison]

/-- A `struct<(i8, i32)>`: the `i8` at bit `0`, 24 bits of padding, the `i32` at bit `32`. -/
private def pair : ⟦Ty.struct [.bv 8, .bv 32]⟧ :=
  (.value 1#8, .value 2#32)

-- a struct's padding is undefined: a load across it is poison, the fields read back
#guard
  ((store? (τ := .struct [.bv 8, .bv 32]) (.value (p 0)) pair).bind
      (load? (.bv 64) (.value (p 0)) ·)) ==
    some .poison

#guard
  ((store? (τ := .struct [.bv 8, .bv 32]) (.value (p 0)) pair).bind
      (load? (.struct [.bv 8, .bv 32]) (.value (p 0)) ·)) ==
    some pair

#guard
  ((store? (τ := .struct [.bv 8, .bv 32]) (.value (p 0)) pair).bind
      (load? (.bv 32) (.value (p 4)) ·)) ==
    some (.value 2#32)

/-- Block `0`'s 8 bytes as `memcpy dst src len` leaves them, loaded, or `none` for UB. -/
private def memcpyLoad? (src : Pointer) (s : GlobalState) : Option ⟦Ty.bv 64⟧ :=
  match Operation.memcpy (.value (p 0)) (.value src) (.value 8#64) env0 s with
  | .value (_, s') => load? (.bv 64) (.value (p 0)) s'
  | .poison => none

-- `memcpy` copies which bits are defined: from an uninitialized block, poison
#guard memcpyLoad? (a 0) sA == some .poison

-- reading a dead object is UB
#guard memcpyLoad? (a 0) (s0.alloca 8 true) == none

/-! ## Stored pointers -/

/-- Addresses: block `b` at `0x1000 * b`. -/
private instance addrs : Unspecified :=
  ⟨fun b => BitVec.ofNat 64 (0x1000 * b.id), fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- `s0` with block `1`, 16 bytes, fresh from an `alloca`, the blocks at `addrs`. -/
private def sP : GlobalState :=
  let s := s0.alloca 16
  { s with mem := @MemoryState.mk s.mem.mem addrs s.mem.table }

/-- `sP` with `q 3` stored at byte `off` of block `1`. -/
private def withPtr (off : Nat) : Option GlobalState :=
  store? (τ := .ptr) (.value (a off)) (.value (q 3)) sP

/-- `q 3`'s address, as `ptrtoaddr` reads it. -/
private def q3Addr : BitVec 64 :=
  0x2003#64

#guard Operation.ptrtoaddr sP.mem.addr (w := 64) (.value (q 3)) == .value q3Addr

/-- `memcpy dst src len` over `s`, then a load at `at_`; `none` for UB. -/
private def copyLoad? (τ : Ty) (dst src : Pointer) (len : Nat) (at_ : Pointer) (s : GlobalState) :
    Option ⟦τ⟧ :=
  match Operation.memcpy (.value dst) (.value src) (.value (BitVec.ofNat 64 len)) env0 s with
  | .value (_, s') => load? τ (.value at_) s'
  | .poison => none

-- a stored pointer loads back, at any byte offset
#guard ((withPtr 0).bind (load? .ptr (.value (a 0)) ·)) == some (.value (q 3))

#guard ((withPtr 5).bind (load? .ptr (.value (a 5)) ·)) == some (.value (q 3))

-- not from another offset
#guard ((withPtr 0).bind (load? .ptr (.value (a 1)) ·)) == some .poison

-- its bits are its address: an integer load of them is `ptrtoaddr`'s value
#guard ((withPtr 0).bind (load? (.bv 64) (.value (a 0)) ·)) == some (.value q3Addr)

#guard ((withPtr 0).bind (load? (.bv 8) (.value (a 1)) ·)) == some (.value 0x20#8)

#guard ((withPtr 0).bind (load? (.bv 8) (.value (a 7)) ·)) == some (.value 0#8)

-- an integer load past it reads the undefined bits there as poison
#guard ((withPtr 0).bind (load? (.bv 64) (.value (a 4)) ·)) == some .poison

-- a byte stored over it, defined or poison, leaves it poison
#guard
  (((withPtr 0).bind (store? (τ := .bv 8) (.value (a 3)) (.value 1#8) ·)).bind
      (load? .ptr (.value (a 0)) ·)) ==
    some .poison

#guard
  ((((withPtr 0).bind (store? (τ := .bv 8) (.value (a 3)) (.value 1#8) ·)).bind
        (store? (τ := .bv 8) (.value (a 3)) .poison ·)).bind
      (load? .ptr (.value (a 0)) ·)) ==
    some .poison

-- so does its own address stored over it as an integer: the bits, not the pointer
#guard
  (((withPtr 0).bind (store? (τ := .bv 64) (.value (a 0)) (.value q3Addr) ·)).bind
      (fun s => (load? .ptr (.value (a 0)) s).bind fun x =>
        (load? (.bv 64) (.value (a 0)) s).map (x, ·))) ==
    some (.poison, .value q3Addr)

-- a store next to it leaves it
#guard
  (((withPtr 0).bind (store? (τ := .bv 64) (.value (a 8)) (.value 1#64) ·)).bind
      (load? .ptr (.value (a 0)) ·)) ==
    some (.value (q 3))

-- a pointer stored over half of it replaces it
#guard
  (((withPtr 0).bind (store? (τ := .ptr) (.value (a 4)) (.value (p 1)) ·)).bind
      (fun s => (load? .ptr (.value (a 0)) s).bind fun x =>
        (load? .ptr (.value (a 4)) s).map (x, ·))) ==
    some (.poison, .value (p 1))

-- a poison pointer stores nothing, its bits undefined
#guard
  ((store? (τ := .ptr) (.value (a 0)) .poison sP).bind
      (fun s => (load? .ptr (.value (a 0)) s).bind fun x =>
        (load? (.bv 64) (.value (a 0)) s).map (x, ·))) ==
    some (.poison, .poison)

-- a struct's pointer leaf is recorded, its integer leaf stored
#guard
  ((store? (τ := .struct [.ptr, .bv 32]) (.value (a 0)) (.value (q 3), .value 7#32) sP).bind
      (load? (.struct [.ptr, .bv 32]) (.value (a 0)) ·)) ==
    some (.value (q 3), .value 7#32)

-- `memcpy` copies the pointer with its bits: the copy loads back, as a pointer or its address
#guard ((withPtr 0).bind (copyLoad? .ptr (a 8) (a 0) 8 (a 8) ·)) == some (.value (q 3))

#guard ((withPtr 0).bind (copyLoad? (.bv 64) (a 8) (a 0) 8 (a 8) ·)) == some (.value q3Addr)

-- into another block; one reaching past the copied bytes is not carried
#guard ((withPtr 0).bind (copyLoad? .ptr (p 0) (a 0) 8 (p 0) ·)) == some (.value (q 3))

#guard ((withPtr 4).bind (copyLoad? .ptr (p 0) (a 0) 8 (p 0) ·)) == some .poison

-- a copy of part of it carries no pointer, its bits undefined
#guard ((withPtr 0).bind (copyLoad? .ptr (a 8) (a 0) 4 (a 8) ·)) == some .poison

#guard ((withPtr 0).bind (copyLoad? (.bv 32) (a 8) (a 0) 4 (a 8) ·)) == some .poison

-- a copy over it of other bits leaves it poison
#guard
  ((withPtr 8).bind fun s =>
      (store? (τ := .bv 64) (.value (a 0)) (.value 5#64) s).bind
        (copyLoad? .ptr (a 8) (a 0) 8 (a 8) ·)) ==
    some .poison

-- `memmove` reads before it writes: a pointer moved over itself by 4 bytes loads at its new place
#guard
  ((withPtr 0).bind fun s =>
      match Operation.memmove (.value (a 4)) (.value (a 0)) (.value 8#64) env0 s with
      | .value (_, s') =>
        (load? .ptr (.value (a 4)) s').bind fun x => (load? .ptr (.value (a 0)) s').map (x, ·)
      | .poison => none) ==
    some (.value (q 3), .poison)

-- `lifetime.start` drops it
#guard
  ((withPtr 0).bind fun s =>
      match Operation.lifetimeStart (.value (a 0)) env0 s with
      | .value (_, s') => load? .ptr (.value (a 0)) s'
      | .poison => none) ==
    some .poison

/-! ## Lifetimes -/

/-- The state after `lifetime.start` (`start`) or `lifetime.end` of `q`, or `none` for UB. -/
private def lifetime? (start : Bool) (q : ⟦Ty.ptr⟧) (s : GlobalState := s0) : Option GlobalState :=
  match (if start then Operation.lifetimeStart q env0 else Operation.lifetimeEnd q env0) s with
  | .value (_, s') => some s'
  | .poison => none

-- after `lifetime.end`, a load is poison and a store UB
#guard ((lifetime? false (.value (p 0))).bind (load? (.bv 64) (.value (p 0)) ·)) == some .poison

#guard
  ((lifetime? false (.value (p 0))).bind
      (store? (τ := .bv 64) (.value (p 0)) (.value 1#64) ·)).isNone

-- `lifetime.start` makes it live again, its bits undefined
#guard
  (((lifetime? false (.value (p 0))).bind (lifetime? true (.value (p 0)) ·)).bind
      (store? (τ := .bv 64) (.value (p 0)) (.value 1#64) ·)).isSome

#guard ((lifetime? true (.value (p 0))).bind (load? (.bv 64) (.value (p 0)) ·)) == some .poison

-- of a poison pointer: no effect
#guard ((lifetime? false .poison).bind (load? (.bv 64) (.value (p 0)) ·)) == some (.value 0#64)

-- a dead `alloca` (one with lifetime markers): a store is UB until `lifetime.start`
#guard (store? (τ := .bv 64) (.value (a 0)) (.value 1#64) (s0.alloca 8 true)).isNone

#guard
  ((lifetime? true (.value (a 0)) (s0.alloca 8 true)).bind
      (store? (τ := .bv 64) (.value (a 0)) (.value 1#64) ·)).isSome

/-! ## `assume` -/

/-- The state after `assume c`, or `none` for UB. -/
private def assume? (c : ⟦Ty.bv 1⟧) : Option GlobalState :=
  match Operation.assume c env0 s0 with
  | .value (_, s) => some s
  | .poison => none

#guard (assume? (.value 1#1)).isSome

#guard (assume? (.value 0#1)).isNone

#guard (assume? .poison).isNone

end MLIR.Tests
