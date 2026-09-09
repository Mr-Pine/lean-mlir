/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_pow22523_2
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Fold
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_repsqr_mul2

/-!
# `fd_r43x6_pow22523_2` conforms to its spec

The statement, the `runFunction` peel, and the prologue: the thirteen
constants and the twenty `alloca`s, both put back under the names
`fd_r43x6.c` gives them. What is left is the two inlined `fd_r43x6_sqr_fast`
folds, the eleven `fd_r43x6_repsqr_mul2` calls -- each to be peeled against
`fd_r43x6_repsqr_mul2_conforms` -- and the exponent bookkeeping that adds
their `2^n` up to `2^252 - 3`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/- Scaffolding for the `fd_r43x6_pow22523_2` derivation. Only
`fd_r43x6_pow22523_2_conforms`, below, escapes. -/
namespace Pow22523_2

/-! ### The constants

`%0 = 1` is only the `alloca` element count and `%3` is the poison second
operand of the fold's shuffle; neither is worth a name. `%5 … %12` are the
`n` of the ladder -- 2, 0, 1, 5, 10, 20, 50 and 100 -- and read better as the
literals they are.

What is left is `fd_r43x6_fold_unsigned` (`fd_r43x6.h`), the tail of every
`fd_r43x6_sqr`/`fd_r43x6_mul`:

    wwl_madd52lo( wwl_and( _x, wwl( _m43,…,_m43,_m40, 0,0 ) ),
                  wwl( 19,1,1,1,1,1, 0,0 ),
                  wwl_permute( wwl( 5,0,1,2,3,4, 6,7 ),
                               wwl_shru_vector( _x, wwl( 43,…,43,40, 0,0 ) ) ) )

Its three vectors are `%1`, `%4` and `%2`, hoisted to the top of the region
and shared by both inlined squarings. -/

/-- `%1`: the fold's low-limb mask, `wwl( _m43,_m43,_m43,_m43,_m43,_m40, 0,0 )`
for `_m43 = 2^43 - 1`, `_m40 = 2^40 - 1`. -/
def foldMask : Vector (PoisonOr (BitVec 64)) 8 :=
  toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
    8796093022207, 1099511627775, 0, 0]

/-- `%2`: the fold's limb widths, `wwl( 43,43,43,43,43,40, 0,0 )` -- the
`wwl_shru_vector` that lifts each limb's carry out. -/
def foldShift : Vector (PoisonOr (BitVec 64)) 8 :=
  toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0]

/-- `%4`: the fold's multipliers, `wwl( 19,1,1,1,1,1, 0,0 )`. Every carry
moves up one limb; the one off the top comes back at the bottom scaled by
`19`, since `2^255 = 19` in `GF(p)`. -/
def foldMul : Vector (PoisonOr (BitVec 64)) 8 :=
  toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0]

/-! ### The locals

`%13 … %32` are ten pairs of `fd_r43x6_t`, one pair per `fd_r43x6_repsqr_mul2`
of the ladder but the last, which writes through the region's own
out-parameters. `z2a`/`z2b` have no slot either: the `FD_R43X6_SQR2_INL` that
opens the function is inlined, so they stay in registers. -/

/-- Every local is one `fd_r43x6_t`: `vector<8xi64>`, 512 bits. Indexed by
`Nat`, not `Fin`, because `GlobalState.allocaChain` is. -/
def cw (_ : Nat) : Nat := 512

/-- The twenty locals as pointers: consecutive blocks from the entry counter. -/
def slotPtr (s : GlobalState) (k : Nat) : Pointer := s.chainPtr cw k

/-! Allocation order, under `fd_r43x6.c`'s names. Each slot is named for the
local it holds, and paired with the `fd_r43x6_repsqr_mul2` call that fills
it. -/
namespace Slot

/-- `%13` -- `repsqr_mul2( &z9a, z2a, za, 2 )`. -/
def z9a : Nat := 0
/-- `%14` -- `repsqr_mul2( &z9b, z2b, zb, 2 )`. -/
def z9b : Nat := 1
/-- `%15` -- `repsqr_mul2( &z11a, z9a, z2a, 0 )`. -/
def z11a : Nat := 2
/-- `%16` -- `repsqr_mul2( &z11b, z9b, z2b, 0 )`. -/
def z11b : Nat := 3
/-- `%17` -- `repsqr_mul2( &z2e5m1a, z11a, z9a, 1 )`. -/
def z2e5m1a : Nat := 4
/-- `%18` -- `repsqr_mul2( &z2e5m1b, z11b, z9b, 1 )`. -/
def z2e5m1b : Nat := 5
/-- `%19` -- `repsqr_mul2( &z2e10m1a, z2e5m1a, z2e5m1a, 5 )`. -/
def z2e10m1a : Nat := 6
/-- `%20` -- `repsqr_mul2( &z2e10m1b, z2e5m1b, z2e5m1b, 5 )`. -/
def z2e10m1b : Nat := 7
/-- `%21` -- `repsqr_mul2( &z2e20m1a, z2e10m1a, z2e10m1a, 10 )`. -/
def z2e20m1a : Nat := 8
/-- `%22` -- `repsqr_mul2( &z2e20m1b, z2e10m1b, z2e10m1b, 10 )`. -/
def z2e20m1b : Nat := 9
/-- `%23` -- `repsqr_mul2( &z2e40m1a, z2e20m1a, z2e20m1a, 20 )`. -/
def z2e40m1a : Nat := 10
/-- `%24` -- `repsqr_mul2( &z2e40m1b, z2e20m1b, z2e20m1b, 20 )`. -/
def z2e40m1b : Nat := 11
/-- `%25` -- `repsqr_mul2( &z2e50m1a, z2e40m1a, z2e10m1a, 10 )`. -/
def z2e50m1a : Nat := 12
/-- `%26` -- `repsqr_mul2( &z2e50m1b, z2e40m1b, z2e10m1b, 10 )`. -/
def z2e50m1b : Nat := 13
/-- `%27` -- `repsqr_mul2( &z2e100m1a, z2e50m1a, z2e50m1a, 50 )`. -/
def z2e100m1a : Nat := 14
/-- `%28` -- `repsqr_mul2( &z2e100m1b, z2e50m1b, z2e50m1b, 50 )`. -/
def z2e100m1b : Nat := 15
/-- `%29` -- `repsqr_mul2( &z2e200m1a, z2e100m1a, z2e100m1a, 100 )`. -/
def z2e200m1a : Nat := 16
/-- `%30` -- `repsqr_mul2( &z2e200m1b, z2e100m1b, z2e100m1b, 100 )`. -/
def z2e200m1b : Nat := 17
/-- `%31` -- `repsqr_mul2( &z2e250m1a, z2e200m1a, z2e50m1a, 50 )`. -/
def z2e250m1a : Nat := 18
/-- `%32` -- `repsqr_mul2( &z2e250m1b, z2e200m1b, z2e50m1b, 50 )`. -/
def z2e250m1b : Nat := 19

end Slot

/-! ### Folding the prologue

`peel_alloca_chain` leaves each fresh pointer expanded as
`⟨⟨(s.allocaChain cw k).alloc.nextFreeBlock⟩, 0⟩`. One `rfl` a slot puts it
back as `slotPtr s Slot.<name>`, which is the form the facts above are stated
over -- and the form that shows the C's name rather than an index in every
goal the ladder leaves. -/

@[simp] theorem slotPtr_z9a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 0).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z9a := rfl

@[simp] theorem slotPtr_z9b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 1).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z9b := rfl

@[simp] theorem slotPtr_z11a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 2).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z11a := rfl

@[simp] theorem slotPtr_z11b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 3).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z11b := rfl

@[simp] theorem slotPtr_z2e5m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 4).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e5m1a := rfl

@[simp] theorem slotPtr_z2e5m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 5).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e5m1b := rfl

@[simp] theorem slotPtr_z2e10m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 6).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e10m1a := rfl

@[simp] theorem slotPtr_z2e10m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 7).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e10m1b := rfl

@[simp] theorem slotPtr_z2e20m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 8).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e20m1a := rfl

@[simp] theorem slotPtr_z2e20m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 9).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e20m1b := rfl

@[simp] theorem slotPtr_z2e40m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 10).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e40m1a := rfl

@[simp] theorem slotPtr_z2e40m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 11).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e40m1b := rfl

@[simp] theorem slotPtr_z2e50m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 12).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e50m1a := rfl

@[simp] theorem slotPtr_z2e50m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 13).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e50m1b := rfl

@[simp] theorem slotPtr_z2e100m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 14).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e100m1a := rfl

@[simp] theorem slotPtr_z2e100m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 15).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e100m1b := rfl

@[simp] theorem slotPtr_z2e200m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 16).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e200m1a := rfl

@[simp] theorem slotPtr_z2e200m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 17).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e200m1b := rfl

@[simp] theorem slotPtr_z2e250m1a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 18).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e250m1a := rfl

@[simp] theorem slotPtr_z2e250m1b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 19).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.z2e250m1b := rfl

/-- The frame `fd_r43x6_pow22523_2` allocates: twenty consecutive blocks from
the entry counter `n₀`, with the caller's out-parameters strictly below it.
That is the whole separation story. -/
structure Slots (t : Nat → Pointer) (za zb : Pointer) (n₀ : Nat) : Prop where
  /-- Slot `k` is block `n₀ + k`. -/
  id : ∀ k, (t k).id.id = n₀ + k
  /-- Every slot addresses its block from the base. -/
  off : ∀ k, (t k).offset = 0
  /-- `%arg0`, the `a` chain's out-parameter, predates the frame. -/
  ida : za.id.id < n₀
  /-- `%arg2`, the `b` chain's out-parameter, predates the frame. -/
  idb : zb.id.id < n₀

namespace Slots

variable {t : Nat → Pointer} {za zb : Pointer} {n₀ : Nat} (hs : Slots t za zb n₀)
include hs

/-- Distinct slots are distinct blocks -- by `omega` on the indices. -/
theorem ne {i j : Nat} (hij : i ≠ j) : (t i).id ≠ (t j).id := fun h => by
  have hi := hs.id i
  have hj := hs.id j
  have h' : (t i).id.id = (t j).id.id := by rw [h]
  omega

/-- A slot is never one of the caller's blocks: it is at or above `n₀`. -/
theorem ne_below {i : Nat} {b : BlockId} (hb : b.id < n₀) : (t i).id ≠ b := fun h => by
  have hi := hs.id i
  have h' : (t i).id.id = b.id := by rw [h]
  omega

theorem ne_za (i : Nat) : (t i).id ≠ za.id := hs.ne_below hs.ida
theorem ne_zb (i : Nat) : (t i).id ≠ zb.id := hs.ne_below hs.idb

end Slots

/-- What holds of a state part-way through the ladder. `Slots` is about the
pointers and is fixed once; this is about the state and is rebuilt at every
call. Slot *values* stay outside it: each is live over a different stretch of
the ladder, so carrying all twenty would be dead weight. -/
structure Frame (t : Nat → Pointer) (n₀ : Nat) (s₀ u : GlobalState) : Prop where
  wf : u.WF
  fits : ∀ k, k < 20 → Fits u.mem (t k) 512
  fb : FrameBelow n₀ s₀ u

/-- The prologue's facts: `Slots` for the pointers, `Frame` for the state the
twenty `alloca`s reach.

That state is handed out *opaquely* -- a local, with `hsAlloc` the only place
`allocaChain` is written. Everything downstream is a call at that state or a
frame pop of it, and every one of those is an `isDefEq` against it; left
transparent each would unfold the twenty-step chain. `hsAlloc` folds the goal
back to the local right after `peel_alloca_chain`, and is not needed again. -/
theorem exists_slots_frame (s : GlobalState) (hs : s.WF) {za zb : Pointer}
    (hza : IsVecPtr s.mem za) (hzb : IsVecPtr s.mem zb) :
    ∃ sAlloc : GlobalState, sAlloc = s.allocaChain cw 20
      ∧ Slots (slotPtr s) za zb s.alloc.nextFreeBlock
      ∧ Frame (slotPtr s) s.alloc.nextFreeBlock s sAlloc :=
  ⟨_, rfl,
   { id := fun k => GlobalState.chainPtr_id k
     off := fun k => GlobalState.chainPtr_offset k
     ida := lt_nextFreeBlock_of_fits hs hza.1
     idb := lt_nextFreeBlock_of_fits hs hzb.1 },
   { wf := GlobalState.WF.allocaChain hs 20
     fits := fun _ hk => GlobalState.fits_chainPtr hk
     fb := FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 20 }⟩

/-! ### The ladder, at the exponent

`fd_r43x6_repsqr_mul2( z, x, y, n )` computes `[x^(2^n)] y`, so on exponents
it is `e ↦ e * 2^n + f`. The eleven calls are that map iterated, and this
section is the C's factorisation of `2^252 - 3` checked in the small: nothing
here mentions the program, the state or even `GF(p)`. -/

/-- One rung: the exponent `[x^(2^n)] y` reaches, from `x`'s and `y`'s. -/
def rung (e n f : ℕ) : ℕ := e * 2 ^ n + f

/-- The identity the whole ladder runs on: squaring `z^(2^a - 1)` `b` times
and multiplying by `z^(2^b - 1)` gives `z^(2^(a+b) - 1)`. Seven of the eleven
rungs are this. -/
theorem rung_ones (a b : ℕ) : rung (2 ^ a - 1) b (2 ^ b - 1) = 2 ^ (a + b) - 1 := by
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hab : 2 ^ b ≤ 2 ^ a * 2 ^ b := Nat.le_mul_of_pos_left _ (by omega)
  have hsub : (2 ^ a - 1) * 2 ^ b = 2 ^ a * 2 ^ b - 2 ^ b := by
    rw [Nat.sub_mul, one_mul]
  rw [rung, hsub, pow_add]
  omega

/-! The rungs, under `fd_r43x6.c`'s names for the locals that hold them. The
first four are `norm_num`; from `z2e5m1` on they are `rung_ones`. -/

/-- `z2 = z^2` -- the inlined `FD_R43X6_SQR2_INL`, not a `repsqr_mul2` call. -/
def eZ2 : ℕ := 2
/-- `z9 = [z2^(2^2)] z` -/
def eZ9 : ℕ := rung eZ2 2 1
/-- `z11 = [z9^(2^0)] z2` -/
def eZ11 : ℕ := rung eZ9 0 eZ2
/-- `z2e5m1 = [z11^(2^1)] z9` -/
def eZ2e5m1 : ℕ := rung eZ11 1 eZ9
/-- `z2e10m1 = [z2e5m1^(2^5)] z2e5m1` -/
def eZ2e10m1 : ℕ := rung eZ2e5m1 5 eZ2e5m1
/-- `z2e20m1 = [z2e10m1^(2^10)] z2e10m1` -/
def eZ2e20m1 : ℕ := rung eZ2e10m1 10 eZ2e10m1
/-- `z2e40m1 = [z2e20m1^(2^20)] z2e20m1` -/
def eZ2e40m1 : ℕ := rung eZ2e20m1 20 eZ2e20m1
/-- `z2e50m1 = [z2e40m1^(2^10)] z2e10m1` -/
def eZ2e50m1 : ℕ := rung eZ2e40m1 10 eZ2e10m1
/-- `z2e100m1 = [z2e50m1^(2^50)] z2e50m1` -/
def eZ2e100m1 : ℕ := rung eZ2e50m1 50 eZ2e50m1
/-- `z2e200m1 = [z2e100m1^(2^100)] z2e100m1` -/
def eZ2e200m1 : ℕ := rung eZ2e100m1 100 eZ2e100m1
/-- `z2e250m1 = [z2e200m1^(2^50)] z2e50m1` -/
def eZ2e250m1 : ℕ := rung eZ2e200m1 50 eZ2e50m1

theorem eZ9_eq : eZ9 = 9 := by norm_num [eZ9, eZ2, rung]
theorem eZ11_eq : eZ11 = 11 := by norm_num [eZ11, eZ9, eZ2, rung]
theorem eZ2e5m1_eq : eZ2e5m1 = 2 ^ 5 - 1 := by
  norm_num [eZ2e5m1, eZ11, eZ9, eZ2, rung]
theorem eZ2e10m1_eq : eZ2e10m1 = 2 ^ 10 - 1 := by
  rw [eZ2e10m1, eZ2e5m1_eq, show (2 ^ 5 - 1 : ℕ) = 2 ^ 5 - 1 from rfl, rung_ones]
theorem eZ2e20m1_eq : eZ2e20m1 = 2 ^ 20 - 1 := by
  rw [eZ2e20m1, eZ2e10m1_eq, rung_ones]
theorem eZ2e40m1_eq : eZ2e40m1 = 2 ^ 40 - 1 := by
  rw [eZ2e40m1, eZ2e20m1_eq, rung_ones]
theorem eZ2e50m1_eq : eZ2e50m1 = 2 ^ 50 - 1 := by
  rw [eZ2e50m1, eZ2e40m1_eq, eZ2e10m1_eq, rung_ones]
theorem eZ2e100m1_eq : eZ2e100m1 = 2 ^ 100 - 1 := by
  rw [eZ2e100m1, eZ2e50m1_eq, rung_ones]
theorem eZ2e200m1_eq : eZ2e200m1 = 2 ^ 200 - 1 := by
  rw [eZ2e200m1, eZ2e100m1_eq, rung_ones]
theorem eZ2e250m1_eq : eZ2e250m1 = 2 ^ 250 - 1 := by
  rw [eZ2e250m1, eZ2e200m1_eq, eZ2e50m1_eq, rung_ones]

/-- **The ladder ends where the spec says.** The twelfth step is the eleventh
call, `[z2e250m1^(2^2)] z`, and it is `z^((p-5)/8)`. -/
theorem rung_final : rung eZ2e250m1 2 1 = 2 ^ 252 - 3 := by
  rw [rung, eZ2e250m1_eq]
  have h : (2 ^ 250 - 1) * 2 ^ 2 = 2 ^ 252 - 2 ^ 2 := by
    rw [Nat.sub_mul, one_mul, ← pow_add]
  have hb : (2 : ℕ) ^ 2 ≤ 2 ^ 252 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [h]
  omega

/-! ### What a slot holds

The ladder reads a rung back out of its slot one or two calls after writing
it, so the walk carries, per live rung, that its slot still holds what was
written. `Held.survive` is what pushes one across a later call: the two
destinations are a different pair of slots, and `Slots.ne` is the whole
argument. -/

/-- **The memory the region leaves.** The eleventh call wrote the caller's own
`za`/`zb`; everything else it touched is the frame, which `popFrame` kills. -/
theorem final_mem {za zb : Pointer} {n₀ : Nat} {s u u' : GlobalState}
    (hs : s.WF) (hn₀ : n₀ = s.alloc.nextFreeBlock)
    (hza : za.id.id < n₀) (hzb : zb.id.id < n₀) (hne : za.id ≠ zb.id)
    (fb : FrameBelow n₀ s u)
    {oa ob : Vector (BitVec 64) 8} (w : Wrote2 za zb oa ob u u') :
    s.popFrame u'.mem ≈
      ({ alloc := s.alloc, mem := (s.mem.splice za (vecBV oa)).splice zb (vecBV ob),
         globals := s.globals } : GlobalState) := by
  subst hn₀
  refine popFrame_equiv_written (fun q => q = za.id ∨ q = zb.id) hs ?_ ?_ ?_ ?_
  · rintro b (rfl | rfl) <;> assumption
  · intro b hb hw
    rw [w.other b (fun h => hw (Or.inl h)) (fun h => hw (Or.inr h))]
    exact fb b hb
  · intro b hw
    rw [live?_splice_ne (fun h => hw (Or.inr h.symm)),
      live?_splice_ne (fun h => hw (Or.inl h.symm))]
  · rintro b (rfl | rfl)
    · rw [w.mem.live za.id, live?_splice_ne (fun h => hne h.symm),
        live?_splice_ne (fun h => hne h.symm)]
      exact live?_splice_congr (fb za.id hza)
    · rw [w.mem.live zb.id]
      exact live?_splice_congr (by
        rw [live?_splice_ne (fun h => hne h), live?_splice_ne (fun h => hne h)]
        exact fb zb.id hzb)

/-- `n₀` bounds every slot from below. -/
theorem Slots.le_id {t : Nat → Pointer} {za zb : Pointer} {n₀ : Nat}
    (hs : Slots t za zb n₀) (k : Nat) : n₀ ≤ (t k).id.id := by
  rw [hs.id]; omega

/-- One rung at the value level: `[x^(2^n)] y` is `z` to the `rung` of the
exponents `x` and `y` hold. Eleven of these composed is the ladder. -/
theorem rung_value {z u v w : ZMod p} {e f m : ℕ} {n : BitVec 64} (hm : n.toNat = m)
    (hu : u = z ^ e) (hv : v = z ^ f) (hw : w = u ^ 2 ^ n.toNat * v) :
    w = z ^ rung e m f := by
  subst hm; subst hu; subst hv; subst hw
  rw [rung, pow_add, ← pow_mul]

/-- **Every slot is still a slot after a call.** The two it wrote come from
`Wrote2`; the rest are untouched, so their blocks read as they did. This is
what carries the frame from one rung to the next. -/
theorem slots_after {t : Nat → Pointer} {za zb : Pointer} {n₀ i j : Nat}
    {va vb : Vector (BitVec 64) 8} {u u' : GlobalState}
    (hs : Slots t za zb n₀) (w : Wrote2 (t i) (t j) va vb u u')
    (h : ∀ k, k < 20 → IsVecPtr u.mem (t k)) :
    ∀ k, k < 20 → IsVecPtr u'.mem (t k) := by
  intro k hk
  by_cases h1 : k = i
  · exact h1 ▸ w.ptrA
  by_cases h2 : k = j
  · exact h2 ▸ w.ptrB
  exact ⟨fits_of_live?_eq (w.other _ (hs.ne h1) (hs.ne h2)) (h k hk).1, (h k hk).2⟩

/-- Slot `k` holds `v`. -/
structure Held (t : Nat → Pointer) (k : Nat) (v : Vector (BitVec 64) 8)
    (u : GlobalState) : Prop where
  ptr : IsVecPtr u.mem (t k)
  val : readVec ptr = v

/-- A rung survives any call that did not write its slot. -/
theorem Held.survive {t : Nat → Pointer} {za zb : Pointer} {n₀ k i j : Nat}
    {v va vb : Vector (BitVec 64) 8} {u u' : GlobalState}
    (hs : Slots t za zb n₀) (h : Held t k v u) (w : Wrote2 (t i) (t j) va vb u u')
    (hki : k ≠ i) (hkj : k ≠ j) : Held t k v u' :=
  let ⟨ptr, hval⟩ := w.survive (hs.ne hki) (hs.ne hkj) h.ptr
  ⟨ptr, hval.trans h.val⟩

/-- The two slots a call *did* write hold what it put there. -/
theorem Held.of_wrote {t : Nat → Pointer} {i j : Nat}
    {va vb : Vector (BitVec 64) 8} {u u' : GlobalState}
    (w : Wrote2 (t i) (t j) va vb u u') : Held t i va u' ∧ Held t j vb u' :=
  ⟨⟨w.ptrA, w.valA⟩, ⟨w.ptrB, w.valB⟩⟩

/-! ### The opening `FD_R43X6_SQR2_INL`

`z2a`/`z2b` are computed inline rather than through `fd_r43x6_repsqr_mul2`, so
the region holds the macro's two halves literally: a `fd_r43x6_sqr_fast` call,
which is `Step/fd_r43x6_sqr_fast.lean`'s `sqr_step`, and then
`fd_r43x6_fold_unsigned`'s four instructions, which are `Fold.lean`'s
`denote_foldVec`. Nothing about either is specific to this region, so neither
is restated here. -/

end Pow22523_2

open Pow22523_2 in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`fd_r43x6_pow22523_2` conforms to its spec.** -/
theorem fd_r43x6_pow22523_2_conforms (za zb : Pointer) (xa xb : Vector (BitVec 64) 8)
    (s : GlobalState) (hs : s.WF) (hza : IsVecPtr s.mem za) (hzb : IsVecPtr s.mem zb)
    (hne : za.id ≠ zb.id)
    (hxa : R43x6.U47 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hxb : R43x6.U47 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0) :
    fd_r43x6_pow22523_2_spec za zb xa xb s hza hzb := by
  -- Facts first, while the goal is still one line: an `obtain` against the
  -- walk's goal reverts it, and that is seconds a layer.
  obtain ⟨sAlloc, hsAlloc, slots, frame⟩ := exists_slots_frame s hs hza hzb
  simp only [fd_r43x6_pow22523_2_spec, Cfg.denote]
  refine Firedancer.run_runFunction' _ ?_
  -- %0-%12: the constants
  denote_step_reduce v 12 [LLVM.const?, LLVM.Ty.poison]
  replace hv1 : v1 = foldMask := by simp only [foldMask]; denote_dense hv1
  replace hv2 : v2 = foldShift := by simp only [foldShift]; denote_dense hv2
  replace hv4 : v4 = foldMul := by simp only [foldMul]; denote_dense hv4
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12
  -- %13-%32: the twenty locals, folded back to `slotPtr s Slot.z9a`, …
  peel_alloca_chain s, cw, 20
  simp only [slotPtr_z9a, slotPtr_z9b, slotPtr_z11a, slotPtr_z11b,
    slotPtr_z2e5m1a, slotPtr_z2e5m1b, slotPtr_z2e10m1a, slotPtr_z2e10m1b,
    slotPtr_z2e20m1a, slotPtr_z2e20m1b, slotPtr_z2e40m1a, slotPtr_z2e40m1b,
    slotPtr_z2e50m1a, slotPtr_z2e50m1b, slotPtr_z2e100m1a, slotPtr_z2e100m1b,
    slotPtr_z2e200m1a, slotPtr_z2e200m1b, slotPtr_z2e250m1a, slotPtr_z2e250m1b]
  rw [← hsAlloc]

  -- The result states, named up front: `peel_call` then puts a local into the
  -- goal rather than a `popFrame` term needing a whole-goal `set`.
  refine name_of (sAlloc.popFrame sAlloc.mem) fun u₁ hu₁def => ?_
  refine name_of (u₁.popFrame u₁.mem) fun u₂ hu₂def => ?_
  peel_call (sqr_step_of_take hxa hxa6 hxa7 sAlloc u₁ hu₁def)
  -- %34-%37: `z2a`
  denote_step_all v 37
  denote_eval v 34 37
  subst hv34 hv35 hv36
  simp only [foldMask, foldShift, foldMul] at hv37
  replace hv37 : v37 = (foldVec (sqrVec xa)).map PoisonOr.value := by
    rw [hv37]; exact denote_foldVec (sqrVec xa) (limbNat_sqr_lt hxa) _
  subst hv37
  -- %38-%42: `z2b`
  peel_call (sqr_step_of_take hxb hxb6 hxb7 u₁ u₂ hu₂def)
  denote_step_all v 42
  denote_eval v 39 42
  subst hv39 hv40 hv41
  simp only [foldMask, foldShift, foldMul] at hv42
  replace hv42 : v42 = (foldVec (sqrVec xb)).map PoisonOr.value := by
    rw [hv42]; exact denote_foldVec (sqrVec xb) (limbNat_sqr_lt hxb) _
  subst hv42
  iterate 2 peel_lifetime
  -- Neither `fd_r43x6_sqr_fast` allocates or writes, so each leaves the state
  -- it ran in up to `≈`; `u₂` is where the ladder starts.
  have hpopEq : ∀ u : GlobalState, u.WF → u.popFrame u.mem ≈ u :=
    fun u hu => FrameBelow.popFrame_equiv hu (FrameBelow.refl _ _)
  have hu₁Eq : u₁ ≈ sAlloc := hu₁def ▸ hpopEq _ frame.wf
  have hu₁wf : u₁.WF := GlobalState.WF.of_equiv frame.wf (GlobalState.Equiv.symm hu₁Eq)
  have hu₂Eq : u₂ ≈ sAlloc := (hu₂def ▸ hpopEq _ hu₁wf).trans hu₁Eq
  have hu₂wf : u₂.WF := GlobalState.WF.of_equiv frame.wf (GlobalState.Equiv.symm hu₂Eq)
  have hslot : ∀ k, k < 20 → IsVecPtr u₂.mem (slotPtr s k) := fun k hk =>
    ⟨fits_of_live?_eq (hu₂Eq.live _) (frame.fits k hk), by simp [slotPtr, GlobalState.chainPtr]⟩
  -- `z2a`/`z2b`, as `FD_R43X6_SQR_INL` leaves them
  have h2a := sqr_inl hxa
  have h2b := sqr_inl hxb
  -- `repsqr_mul2( &z9a, z2a, za,  &z9b, z2b, zb,  2 )`
  refine repsqr_mul2_step' (slotPtr s Slot.z9a) (slotPtr s Slot.z9b)
      (foldVec (sqrVec xa)) xa (foldVec (sqrVec xb)) xb 2#64 hu₂wf
      (hslot _ (by decide)) (hslot _ (by decide)) (slots.ne (by decide)) (by decide)
      h2a.u47 h2a.z6 h2a.z7 hxa hxa6 hxa7
      h2b.u47 h2b.z6 h2b.z7 hxb hxb6 hxb7
    fun u₃ v9a v9b hrun9 hv9a hv9b wrote9 => ?_
  peel_call hrun9
  clear hrun9
  iterate 2 peel_lifetime
  -- %43, %44: the rung just written, read back out of its two slots
  peel_load_vec v9a, (slotPtr s Slot.z9a), wrote9.ptrA, wrote9.valA, u₃
  peel_load_vec v9b, (slotPtr s Slot.z9b), wrote9.ptrB, wrote9.valB, u₃
  -- `repsqr_mul2( &z11a, z9a, z2a,  &z11b, z9b, z2b,  0 )`
  have hslot₃ := slots_after slots wrote9 hslot
  refine repsqr_mul2_step' (slotPtr s Slot.z11a) (slotPtr s Slot.z11b)
      v9a (foldVec (sqrVec xa)) v9b (foldVec (sqrVec xb)) 0#64 wrote9.wf
      (hslot₃ _ (by decide)) (hslot₃ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote9.u44A) wrote9.z6A wrote9.z7A h2a.u47 h2a.z6 h2a.z7
      (u47_of_u44 wrote9.u44B) wrote9.z6B wrote9.z7B h2b.u47 h2b.z6 h2b.z7
    fun u₄ v11a v11b hrun11 hval11a hval11b wrote11 => ?_
  peel_call hrun11
  iterate 2 peel_lifetime
  peel_load_vec v11a, (slotPtr s Slot.z11a), wrote11.ptrA, wrote11.valA, u₄
  peel_load_vec v11b, (slotPtr s Slot.z11b), wrote11.ptrB, wrote11.valB, u₄
  -- `repsqr_mul2( &z2e5m1a, z11a, z9a,  &z2e5m1b, …,  1 )`
  have hslot₄ := slots_after slots wrote11 hslot₃
  refine repsqr_mul2_step' (slotPtr s Slot.z2e5m1a) (slotPtr s Slot.z2e5m1b)
      v11a v9a v11b v9b 1#64 wrote11.wf
      (hslot₄ _ (by decide)) (hslot₄ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote11.u44A) wrote11.z6A wrote11.z7A (u47_of_u44 wrote9.u44A) wrote9.z6A wrote9.z7A
      (u47_of_u44 wrote11.u44B) wrote11.z6B wrote11.z7B (u47_of_u44 wrote9.u44B) wrote9.z6B wrote9.z7B
    fun u₅ v5a v5b hrunv5 hvalv5a hvalv5b wrote5 => ?_
  peel_call hrunv5
  iterate 2 peel_lifetime
  peel_load_vec v5a, (slotPtr s Slot.z2e5m1a), wrote5.ptrA, wrote5.valA, u₅
  peel_load_vec v5b, (slotPtr s Slot.z2e5m1b), wrote5.ptrB, wrote5.valB, u₅
  -- `repsqr_mul2( &z2e10m1a, z5a, z5a,  &z2e10m1b, …,  5 )`
  have hslot₅ := slots_after slots wrote5 hslot₄
  refine repsqr_mul2_step' (slotPtr s Slot.z2e10m1a) (slotPtr s Slot.z2e10m1b)
      v5a v5a v5b v5b 5#64 wrote5.wf
      (hslot₅ _ (by decide)) (hslot₅ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote5.u44A) wrote5.z6A wrote5.z7A (u47_of_u44 wrote5.u44A) wrote5.z6A wrote5.z7A
      (u47_of_u44 wrote5.u44B) wrote5.z6B wrote5.z7B (u47_of_u44 wrote5.u44B) wrote5.z6B wrote5.z7B
    fun u₆ v10a v10b hrunv10 hvalv10a hvalv10b wrote10 => ?_
  peel_call hrunv10
  iterate 2 peel_lifetime
  peel_load_vec v10a, (slotPtr s Slot.z2e10m1a), wrote10.ptrA, wrote10.valA, u₆
  peel_load_vec v10b, (slotPtr s Slot.z2e10m1b), wrote10.ptrB, wrote10.valB, u₆
  -- `repsqr_mul2( &z2e20m1a, z10a, z10a,  &z2e20m1b, …,  10 )`
  have hslot₆ := slots_after slots wrote10 hslot₅
  refine repsqr_mul2_step' (slotPtr s Slot.z2e20m1a) (slotPtr s Slot.z2e20m1b)
      v10a v10a v10b v10b 10#64 wrote10.wf
      (hslot₆ _ (by decide)) (hslot₆ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote10.u44A) wrote10.z6A wrote10.z7A (u47_of_u44 wrote10.u44A) wrote10.z6A wrote10.z7A
      (u47_of_u44 wrote10.u44B) wrote10.z6B wrote10.z7B (u47_of_u44 wrote10.u44B) wrote10.z6B wrote10.z7B
    fun u₇ v20a v20b hrunv20 hvalv20a hvalv20b wrote20 => ?_
  peel_call hrunv20
  iterate 2 peel_lifetime
  peel_load_vec v20a, (slotPtr s Slot.z2e20m1a), wrote20.ptrA, wrote20.valA, u₇
  peel_load_vec v20b, (slotPtr s Slot.z2e20m1b), wrote20.ptrB, wrote20.valB, u₇
  -- `repsqr_mul2( &z2e40m1a, z20a, z20a,  &z2e40m1b, …,  20 )`
  have hslot₇ := slots_after slots wrote20 hslot₆
  refine repsqr_mul2_step' (slotPtr s Slot.z2e40m1a) (slotPtr s Slot.z2e40m1b)
      v20a v20a v20b v20b 20#64 wrote20.wf
      (hslot₇ _ (by decide)) (hslot₇ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote20.u44A) wrote20.z6A wrote20.z7A (u47_of_u44 wrote20.u44A) wrote20.z6A wrote20.z7A
      (u47_of_u44 wrote20.u44B) wrote20.z6B wrote20.z7B (u47_of_u44 wrote20.u44B) wrote20.z6B wrote20.z7B
    fun u₈ v40a v40b hrunv40 hvalv40a hvalv40b wrote40 => ?_
  peel_call hrunv40
  iterate 2 peel_lifetime
  peel_load_vec v40a, (slotPtr s Slot.z2e40m1a), wrote40.ptrA, wrote40.valA, u₈
  peel_load_vec v40b, (slotPtr s Slot.z2e40m1b), wrote40.ptrB, wrote40.valB, u₈
  -- `repsqr_mul2( &z2e50m1a, z40a, z10a,  &z2e50m1b, …,  10 )`
  have hslot₈ := slots_after slots wrote40 hslot₇
  refine repsqr_mul2_step' (slotPtr s Slot.z2e50m1a) (slotPtr s Slot.z2e50m1b)
      v40a v10a v40b v10b 10#64 wrote40.wf
      (hslot₈ _ (by decide)) (hslot₈ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote40.u44A) wrote40.z6A wrote40.z7A (u47_of_u44 wrote10.u44A) wrote10.z6A wrote10.z7A
      (u47_of_u44 wrote40.u44B) wrote40.z6B wrote40.z7B (u47_of_u44 wrote10.u44B) wrote10.z6B wrote10.z7B
    fun u₉ v50a v50b hrunv50 hvalv50a hvalv50b wrote50 => ?_
  peel_call hrunv50
  iterate 2 peel_lifetime
  peel_load_vec v50a, (slotPtr s Slot.z2e50m1a), wrote50.ptrA, wrote50.valA, u₉
  peel_load_vec v50b, (slotPtr s Slot.z2e50m1b), wrote50.ptrB, wrote50.valB, u₉
  -- `repsqr_mul2( &z2e100m1a, z50a, z50a,  &z2e100m1b, …,  50 )`
  have hslot₉ := slots_after slots wrote50 hslot₈
  refine repsqr_mul2_step' (slotPtr s Slot.z2e100m1a) (slotPtr s Slot.z2e100m1b)
      v50a v50a v50b v50b 50#64 wrote50.wf
      (hslot₉ _ (by decide)) (hslot₉ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote50.u44A) wrote50.z6A wrote50.z7A (u47_of_u44 wrote50.u44A) wrote50.z6A wrote50.z7A
      (u47_of_u44 wrote50.u44B) wrote50.z6B wrote50.z7B (u47_of_u44 wrote50.u44B) wrote50.z6B wrote50.z7B
    fun u₁₀ v100a v100b hrunv100 hvalv100a hvalv100b wrote100 => ?_
  peel_call hrunv100
  iterate 2 peel_lifetime
  peel_load_vec v100a, (slotPtr s Slot.z2e100m1a), wrote100.ptrA, wrote100.valA, u₁₀
  peel_load_vec v100b, (slotPtr s Slot.z2e100m1b), wrote100.ptrB, wrote100.valB, u₁₀
  -- `repsqr_mul2( &z2e200m1a, z100a, z100a,  &z2e200m1b, …,  100 )`
  have hslot₁₀ := slots_after slots wrote100 hslot₉
  refine repsqr_mul2_step' (slotPtr s Slot.z2e200m1a) (slotPtr s Slot.z2e200m1b)
      v100a v100a v100b v100b 100#64 wrote100.wf
      (hslot₁₀ _ (by decide)) (hslot₁₀ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote100.u44A) wrote100.z6A wrote100.z7A (u47_of_u44 wrote100.u44A) wrote100.z6A wrote100.z7A
      (u47_of_u44 wrote100.u44B) wrote100.z6B wrote100.z7B (u47_of_u44 wrote100.u44B) wrote100.z6B wrote100.z7B
    fun u₁₁ v200a v200b hrunv200 hvalv200a hvalv200b wrote200 => ?_
  peel_call hrunv200
  iterate 2 peel_lifetime
  peel_load_vec v200a, (slotPtr s Slot.z2e200m1a), wrote200.ptrA, wrote200.valA, u₁₁
  peel_load_vec v200b, (slotPtr s Slot.z2e200m1b), wrote200.ptrB, wrote200.valB, u₁₁
  -- `repsqr_mul2( &z2e250m1a, z200a, z50a,  &z2e250m1b, …,  50 )`
  have hslot₁₁ := slots_after slots wrote200 hslot₁₀
  refine repsqr_mul2_step' (slotPtr s Slot.z2e250m1a) (slotPtr s Slot.z2e250m1b)
      v200a v50a v200b v50b 50#64 wrote200.wf
      (hslot₁₁ _ (by decide)) (hslot₁₁ _ (by decide)) (slots.ne (by decide)) (by decide)
      (u47_of_u44 wrote200.u44A) wrote200.z6A wrote200.z7A (u47_of_u44 wrote50.u44A) wrote50.z6A wrote50.z7A
      (u47_of_u44 wrote200.u44B) wrote200.z6B wrote200.z7B (u47_of_u44 wrote50.u44B) wrote50.z6B wrote50.z7B
    fun u₁₂ v250a v250b hrunv250 hvalv250a hvalv250b wrote250 => ?_
  peel_call hrunv250
  -- no `lifetime.start` here: all twenty slots are already live
  peel_load_vec v250a, (slotPtr s Slot.z2e250m1a), wrote250.ptrA, wrote250.valA, u₁₂
  peel_load_vec v250b, (slotPtr s Slot.z2e250m1b), wrote250.ptrB, wrote250.valB, u₁₂
  -- `repsqr_mul2( _za, z2e250m1a, za,  _zb, z2e250m1b, zb,  2 )`: the eleventh
  -- call writes the region's own out-parameters rather than a slot pair, so
  -- `za`/`zb` have to be carried down here -- which is what the frame is for.
  have fb₂ : FrameBelow s.alloc.nextFreeBlock s u₂ :=
    FrameBelow.of_equiv (GlobalState.Equiv.symm hu₂Eq) frame.fb
  have fb₃ := wrote9.frameBelow (slots.le_id _) (slots.le_id _) fb₂
  have fb₄ := wrote11.frameBelow (slots.le_id _) (slots.le_id _) fb₃
  have fb₅ := wrote5.frameBelow (slots.le_id _) (slots.le_id _) fb₄
  have fb₆ := wrote10.frameBelow (slots.le_id _) (slots.le_id _) fb₅
  have fb₇ := wrote20.frameBelow (slots.le_id _) (slots.le_id _) fb₆
  have fb₈ := wrote40.frameBelow (slots.le_id _) (slots.le_id _) fb₇
  have fb₉ := wrote50.frameBelow (slots.le_id _) (slots.le_id _) fb₈
  have fb₁₀ := wrote100.frameBelow (slots.le_id _) (slots.le_id _) fb₉
  have fb₁₁ := wrote200.frameBelow (slots.le_id _) (slots.le_id _) fb₁₀
  have fb₁₂ := wrote250.frameBelow (slots.le_id _) (slots.le_id _) fb₁₁
  have hzaF : IsVecPtr u₁₂.mem za := ⟨fits_of_live?_eq (fb₁₂ za.id slots.ida) hza.1, hza.2⟩
  have hzbF : IsVecPtr u₁₂.mem zb := ⟨fits_of_live?_eq (fb₁₂ zb.id slots.idb) hzb.1, hzb.2⟩
  refine repsqr_mul2_step' za zb v250a xa v250b xb 2#64 wrote250.wf hzaF hzbF hne (by decide)
      (u47_of_u44 wrote250.u44A) wrote250.z6A wrote250.z7A hxa hxa6 hxa7
      (u47_of_u44 wrote250.u44B) wrote250.z6B wrote250.z7B hxb hxb6 hxb7
    fun u₁₃ oa ob hrunF hvalFa hvalFb wroteF => ?_
  peel_call hrunF
  iterate 20 peel_lifetime
  simp_return
  refine ⟨oa, ob, ?mem, ?va, ?vb, wroteF.u44A, wroteF.u44B,
    wroteF.z6A, wroteF.z7A, wroteF.z6B, wroteF.z7B⟩
  case mem => exact final_mem hs rfl slots.ida slots.idb hne fb₁₂ wroteF
  -- The eleven rungs at the exponent, `rung_value` a step at a time, ending at
  -- the `2^252 - 3` `rung_final` says the C's factorisation reaches.
  case va =>
    have e2a : vecValue (foldVec (sqrVec xa)) = vecValue xa ^ eZ2 := h2a.value
    have e9a : vecValue v9a = vecValue xa ^ eZ9 :=
      rung_value rfl e2a (pow_one _).symm hv9a
    have e11a : vecValue v11a = vecValue xa ^ eZ11 :=
      rung_value rfl e9a e2a hval11a
    have e5a : vecValue v5a = vecValue xa ^ eZ2e5m1 :=
      rung_value rfl e11a e9a hvalv5a
    have e10a : vecValue v10a = vecValue xa ^ eZ2e10m1 :=
      rung_value rfl e5a e5a hvalv10a
    have e20a : vecValue v20a = vecValue xa ^ eZ2e20m1 :=
      rung_value rfl e10a e10a hvalv20a
    have e40a : vecValue v40a = vecValue xa ^ eZ2e40m1 :=
      rung_value rfl e20a e20a hvalv40a
    have e50a : vecValue v50a = vecValue xa ^ eZ2e50m1 :=
      rung_value rfl e40a e10a hvalv50a
    have e100a : vecValue v100a = vecValue xa ^ eZ2e100m1 :=
      rung_value rfl e50a e50a hvalv100a
    have e200a : vecValue v200a = vecValue xa ^ eZ2e200m1 :=
      rung_value rfl e100a e100a hvalv200a
    have e250a : vecValue v250a = vecValue xa ^ eZ2e250m1 :=
      rung_value rfl e200a e50a hvalv250a
    rw [rung_value (m := 2) rfl e250a (pow_one _).symm hvalFa, rung_final]
    norm_num
  case vb =>
    have e2b : vecValue (foldVec (sqrVec xb)) = vecValue xb ^ eZ2 := h2b.value
    have e9b : vecValue v9b = vecValue xb ^ eZ9 :=
      rung_value rfl e2b (pow_one _).symm hv9b
    have e11b : vecValue v11b = vecValue xb ^ eZ11 :=
      rung_value rfl e9b e2b hval11b
    have e5b : vecValue v5b = vecValue xb ^ eZ2e5m1 :=
      rung_value rfl e11b e9b hvalv5b
    have e10b : vecValue v10b = vecValue xb ^ eZ2e10m1 :=
      rung_value rfl e5b e5b hvalv10b
    have e20b : vecValue v20b = vecValue xb ^ eZ2e20m1 :=
      rung_value rfl e10b e10b hvalv20b
    have e40b : vecValue v40b = vecValue xb ^ eZ2e40m1 :=
      rung_value rfl e20b e20b hvalv40b
    have e50b : vecValue v50b = vecValue xb ^ eZ2e50m1 :=
      rung_value rfl e40b e10b hvalv50b
    have e100b : vecValue v100b = vecValue xb ^ eZ2e100m1 :=
      rung_value rfl e50b e50b hvalv100b
    have e200b : vecValue v200b = vecValue xb ^ eZ2e200m1 :=
      rung_value rfl e100b e100b hvalv200b
    have e250b : vecValue v250b = vecValue xb ^ eZ2e250m1 :=
      rung_value rfl e200b e50b hvalv250b
    rw [rung_value (m := 2) rfl e250b (pow_one _).symm hvalFb, rung_final]
    norm_num


end Firedancer.Avx512
