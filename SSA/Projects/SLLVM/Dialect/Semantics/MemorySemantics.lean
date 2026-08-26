/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import LeanMLIR.Dialects.LLVM.Basic
import SSA.Projects.SLLVM.Dialect.Semantics.HasUB
import SSA.Projects.SLLVM.Dialect.Semantics.EffectM
import SSA.Projects.SLLVM.Dialect.Semantics.ArithSemantics
import SSA.Projects.SLLVM.Tactic.SimpSet

namespace LeanMLIR

/-! ## Instructions -/
namespace SLLVM
open BitVec
open InstCombine (LLVM)

/-- A memorySSA'd state, which tracks:
* the content of memory blocks
* whether UB has occurred (within the def-use chain of the state)
-/
def MemorySSAState := PoisonOr MemoryState

/--
Return the block pointed to by `p`, or throw UB if this block
- doesn't exists (i.e., hasn't been allocated yet), or
- has been freed already
-/
def getLiveBlockOrUB (p : Pointer) : MemorySSAM LiveBlock := do
  let m ← getThe MemoryState
  let some (.live block) := m[p.id]?
    | throwUB
  return block

/-! ### Splicing a value into a block -/

/--
`spliceBits bytes off x` overwrites the range `[off, off + w)` of `bytes` with
`x`, leaving every other bit alone.

This is a *replacement*, not an accumulation: the destination range is masked
out before `x` is placed into it. (An earlier version `|||`-ed `x` into `bytes`
without a mask and shifted it the wrong way, so a store could only ever set
bits, and a store at a non-zero offset was shifted off the bottom of the block
and lost entirely.)
-/
def spliceBits {n w : Nat} (bytes : BitVec n) (off : Nat) (x : BitVec w) : BitVec n :=
  let mask := ((BitVec.allOnes w).setWidth n) <<< off
  (bytes &&& ~~~mask) ||| ((x.setWidth n) <<< off)

@[simp_sllvm]
theorem getLsbD_spliceBits {n w : Nat} (bytes : BitVec n) (off : Nat) (x : BitVec w) (i : Nat) :
    (spliceBits bytes off x).getLsbD i
      = if off ≤ i ∧ i < off + w ∧ i < n then x.getLsbD (i - off) else bytes.getLsbD i := by
  simp only [spliceBits, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  by_cases h3 : i < n
  · by_cases h1 : off ≤ i
    · by_cases h2 : i < off + w
      · rw [if_pos ⟨h1, h2, h3⟩]
        simp [h3, show ¬(i < off) by omega, show i - off < n by omega,
          show i - off < w by omega]
      · -- `i` is past the spliced range, so the mask bit is clear and `x` has no
        -- bit there either: both disjuncts reduce to `bytes.getLsbD i`.
        rw [if_neg (by omega)]
        simp [h3, show ¬(i < off) by omega, BitVec.getLsbD_of_ge x (i - off) (by omega)]
        omega
    · rw [if_neg (by omega)]
      simp [h3, show i < off by omega]
  · rw [if_neg (by omega)]
    simp [h3, BitVec.getLsbD_of_ge bytes i (by omega)]

/-- Two stores at adjacent ranges are one store of the concatenation. `++` puts
its left operand in the high bits, so the *later*, higher store is the left
operand. -/
theorem spliceBits_append {n w w' : Nat} (bytes : BitVec n) (off : Nat)
    (x : BitVec w) (y : BitVec w') :
    spliceBits (spliceBits bytes off x) (off + w) y = spliceBits bytes off (y ++ x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits, BitVec.getLsbD_append]
  by_cases h1 : off ≤ i
  · by_cases h2 : i < off + w
    · -- inside the earlier store: the later one is above `i`
      rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      simp [show i - off < w by omega]
    · by_cases h3 : i < off + w + w'
      · -- inside the later store, which is the concatenation's high half
        rw [if_pos (by omega), if_pos (by omega)]
        simp [show ¬ (i - off < w) by omega, show i - off - w = i - (off + w) by omega]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Any sub-range of the spliced-in range reads back out of the spliced-in
value, at the offset it was placed at. -/
theorem extractLsb'_spliceBits_of_subrange {n w w' : Nat} (bytes : BitVec n) (off off' : Nat)
    (x : BitVec w) (hoff : off ≤ off') (hw : (off' - off) + w' ≤ w) (hn : off + w ≤ n) :
    (spliceBits bytes off x).extractLsb' off' w' = x.extractLsb' (off' - off) w' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi, decide_true, Bool.true_and]
  rw [if_pos (by omega), show off' + i - off = off' - off + i by omega]

/-- The spliced-in value reads back exactly, provided it fits. -/
theorem extractLsb'_spliceBits {n w : Nat} (bytes : BitVec n) (off : Nat) (x : BitVec w)
    (h : off + w ≤ n) :
    (spliceBits bytes off x).extractLsb' off w = x := by
  rw [extractLsb'_spliceBits_of_subrange bytes off off x le_rfl (by omega) h,
    Nat.sub_self, BitVec.extractLsb'_eq_self]

/-- A range disjoint from the spliced-in one is untouched. -/
theorem extractLsb'_spliceBits_of_disjoint {n w w' : Nat} (bytes : BitVec n) (off off' : Nat)
    (x : BitVec w) (h : off' + w' ≤ off ∨ off + w ≤ off') :
    (spliceBits bytes off x).extractLsb' off' w' = bytes.extractLsb' off' w' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi, decide_true, Bool.true_and]
  rw [if_neg (by omega)]

/-! ### load / store -/

/--
`load p t` will load a value of type `t` from the location pointed to by `p`.

Raises UB if:
- `p` is poison
- The block pointed to by `p.id` has not been allocated yet or has been freed already
- The range of bits to be read is out of range of the block pointed to by `p.id`

The bits read are decoded with `LLVM.Ty.unflatten`, so this handles vector types
(`load <8 x i64>`) as well as scalars: a vector is laid out with lane `0` in the
low bits, as LLVM does.

**SIMPLIFICATION**: we don't model alignment constraints at all, and a load
never produces poison from uninitialised memory.
-/
def load (p : SLLVM.Ptr) (t : LLVM.Ty) : MemorySSAM (TyDenote.toType t) := do
  let p ← p.getOrUB
  let block ← getLiveBlockOrUB p
  throwUBIf <| p.offsetInBits + LLVM.Ty.width t > block.lengthInBits
  return LLVM.Ty.unflatten t
    (block.bytes.extractLsb' p.offsetInBits (LLVM.Ty.width t))

/--
A wrapper around `load` which makes the operation pure, operating against the
state in a (memory)SSA variable.
-/
def loadPure (m : MemorySSAState) (p : SLLVM.Ptr) (t : LLVM.Ty) :
    MemorySSAState × TyDenote.toType t :=
  match m with
  | .poison => (.poison, LLVM.Ty.poison t)
  | .value m =>
    match (load p t).run m with
    | .poison => (.poison, LLVM.Ty.poison t)
    | .value ⟨x, m⟩ => ⟨.value m, x⟩

/--
`store p t x` will store the value `x` of type `t` at the location pointed to
by `p`.

Raises UB if:
- `p` is poison
- `x` is poison in any lane (we model stores of fully-defined values only)
- The block pointed to by `p.id` has not been allocated yet or has been freed already
- The range of bits to be written is out of range of the block pointed to by `p.id`

**SIMPLIFICATION**: we don't model alignment constraints at all, and we ignore
alias metadata (`tbaa`) entirely.
-/
def store (p : SLLVM.Ptr) (t : LLVM.Ty) (x : TyDenote.toType t) : MemorySSAM Unit := do
  let p ← p.getOrUB
  let x ← (LLVM.Ty.flatten t x).getOrUB
  let block ← getLiveBlockOrUB p
  throwUBIf <| p.offsetInBits + LLVM.Ty.width t > block.lengthInBits
  modifyThe MemoryState fun m => { m with
    mem := m.mem.insert p.id <| .live
      { block with bytes := spliceBits block.bytes p.offsetInBits x }
  }
  return ()

/--
A wrapper around `store` which makes the operation pure, operating against the
state in a (memory)SSA variable.
-/
def storePure (m : MemorySSAState) (p : SLLVM.Ptr) (t : LLVM.Ty) (x : TyDenote.toType t) :
    MemorySSAState := do
  let m ← m
  Prod.snd <$> (store p t x).run m

/--
Allocate the next available block of `w` bits on the stack.

A block lives until the call that allocated it returns: the denotation of
`llvm.call` snapshots `nextFreeBlock` and marks the blocks allocated past it
dead again on return (`MemoryState.killFrom`), as a real execution
deallocates the callee's frame at its `llvm.return`. Within a single region
nothing is freed -- the lifetime intrinsics denote to nothing, since with a
monotonic block counter there is no slot reuse for them to advise on.
-/
def alloca (w : Nat) : EffectM SLLVM.Ptr := do
  let blockId : BlockId ← modifyGetThe AllocState fun s =>
    (⟨s.nextFreeBlock⟩, { s with nextFreeBlock := s.nextFreeBlock + 1})
  let ptr := .value { id := blockId, offset := 0 }
  modifyThe MemoryState fun s => { s with
      mem := s.mem.insert blockId <| .live {
        length := (w + 7) / 8
        bytes := 0#_
      }
    }
  return ptr

/-- Mark dead every block with id at least `n₀`: the *frame* of a call that
was entered at `nextFreeBlock = n₀`. Ids come from that monotonic counter and
`alloca` is the only allocator, so `n₀ ≤ id` says exactly "allocated during
the call" -- no per-block provenance is needed until a second allocator (a
heap `alloc`) exists. Dead, not removed: a pointer that escaped the callee
takes the freed-already UB path on use -- until the caller's next `alloca`
reuses the id, at which point it aliases the new block, as a dangling stack
pointer does. -/
def _root_.LeanMLIR.MemoryState.killFrom (n₀ : Nat) (s : MemoryState) :
    MemoryState :=
  { mem := s.mem.map fun id b => if n₀ ≤ id.id then .dead else b }

/-- Run `body` as a function: snapshot the counter, run, kill the frame --
every block allocated since the snapshot -- and restore the counter. After it
the stack is as it was on entry up to the blocks the body wrote through its
arguments, which is what `GlobalState.Equiv` captures. -/
def runFunction {α : Type} (body : EffectM α) : EffectM α := do
  let alloc ← getThe AllocState
  let r ← body
  modifyThe MemoryState (MemoryState.killFrom alloc.nextFreeBlock)
  modifyThe AllocState fun _ => alloc
  return r
