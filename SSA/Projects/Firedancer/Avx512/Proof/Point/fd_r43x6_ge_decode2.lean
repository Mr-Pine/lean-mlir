/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_r43x6_ge_decode2
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

/-!
# `fd_r43x6_ge_decode2` conforms to its spec

Header only: the statement, the return value, and the `runFunction` peel. The
return value has to be supplied before the state (`run_runFunction'` takes the
state last), so it is named first, as the `ref` walks do.

What is left is the region's five blocks: the two `memcpy`s and unpacks, the
shared `u`/`v` chain, `fd_r43x6_pow22523_2`, the two square-root branches, and
the sign fixup through `fd_r43x6_diagnose`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/- Scaffolding for the `fd_r43x6_ge_decode2` derivation. Only
`fd_r43x6_ge_decode2_conforms`, below, escapes. -/
namespace GeDecode2

/-! ### The frame

Four locals, and unlike `fd_r43x6_pow22523_2`'s twenty they are not all one
width: `_sa`/`_sb` are the 32-byte staging buffers `memcpy` fills, `t0a`/`t0b`
the `wwl_t` out-parameters of the inlined `FD_R43X6_POW22523_2_INL`. -/

/-- The four locals' widths, in allocation order. -/
def cw : Nat → Nat
  | 0 => 256
  | 1 => 256
  | _ => 512

/-- The locals as pointers: consecutive blocks from the entry counter. -/
def slotPtr (s : GlobalState) (k : Nat) : Pointer := s.chainPtr cw k

namespace Slot

/-- `%49` -- `ulong _sa[4]`, the buffer `memcpy( _sa, _vsa, 32 )` fills. -/
def sa : Nat := 0
/-- `%50` -- `ulong _sb[4]`. -/
def sb : Nat := 1
/-- `%51` -- `t0a`, the first out-parameter of `FD_R43X6_POW22523_2_INL`. -/
def t0a : Nat := 2
/-- `%52` -- `t0b`. -/
def t0b : Nat := 3

end Slot

/-- Fold a pointer the `alloca` prologue leaves expanded back to `slotPtr s k`. -/
@[simp] theorem slotPtr_sa (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 0).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.sa := rfl
@[simp] theorem slotPtr_sb (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 1).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.sb := rfl
@[simp] theorem slotPtr_t0a (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 2).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.t0a := rfl
@[simp] theorem slotPtr_t0b (s : GlobalState) :
    (⟨⟨(s.allocaChain cw 3).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slotPtr s Slot.t0b := rfl

/-- The frame the four `alloca`s allocate: consecutive blocks from the entry
counter `n₀`, with all eight of the caller's pointers strictly below it. -/
structure Slots (t : Nat → Pointer) (n₀ : Nat) : Prop where
  id : ∀ k, (t k).id.id = n₀ + k
  off : ∀ k, (t k).offset = 0

/-- Distinct locals are distinct blocks. -/
theorem Slots.ne {t : Nat → Pointer} {n₀ i j : Nat} (hs : Slots t n₀) (hij : i ≠ j) :
    (t i).id ≠ (t j).id := fun h => by
  have hi := hs.id i; have hj := hs.id j
  have h' : (t i).id.id = (t j).id.id := by rw [h]
  omega

/-- What holds of a state part-way through the region. -/
structure Frame (t : Nat → Pointer) (n₀ : Nat) (s₀ u : GlobalState) : Prop where
  wf : u.WF
  fits : ∀ k, k < 4 → Fits u.mem (t k) (cw k)
  fb : FrameBelow n₀ s₀ u

/-- The prologue's facts, with the state it reaches handed out opaquely --
`hsAlloc` is the only place `allocaChain` is written, which is what keeps every
later `isDefEq` off the four-step chain. -/
theorem exists_slots_frame (s : GlobalState) (hs : s.WF) :
    ∃ sAlloc : GlobalState, sAlloc = s.allocaChain cw 4
      ∧ Slots (slotPtr s) s.alloc.nextFreeBlock
      ∧ Frame (slotPtr s) s.alloc.nextFreeBlock s sAlloc :=
  ⟨_, rfl,
   { id := fun k => GlobalState.chainPtr_id k
     off := fun k => GlobalState.chainPtr_offset k },
   { wf := GlobalState.WF.allocaChain hs 4
     fits := fun _ hk => GlobalState.fits_chainPtr hk
     fb := FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 4 }⟩

end GeDecode2

open GeDecode2 in
open scoped Classical in
set_option maxHeartbeats 1000000 in
theorem fd_r43x6_ge_decode2_conforms (a03 a14 a25 sa b03 b14 b25 sb : Pointer)
    (s : GlobalState) (hs : s.WF)
    (ha03 : IsVecPtr s.mem a03) (ha14 : IsVecPtr s.mem a14) (ha25 : IsVecPtr s.mem a25)
    (hb03 : IsVecPtr s.mem b03) (hb14 : IsVecPtr s.mem b14) (hb25 : IsVecPtr s.mem b25)
    (hsa : IsWvPtr s.mem sa) (hsb : IsWvPtr s.mem sb) :
    fd_r43x6_ge_decode2_spec a03 a14 a25 sa b03 b14 b25 sb s
      ha03 ha14 ha25 hb03 hb14 hb25 hsa hsb := by
  obtain ⟨sAlloc, hsAlloc, slots, frame⟩ := GeDecode2.exists_slots_frame s hs
  simp only [fd_r43x6_ge_decode2_spec, Cfg.denote]
  apply Firedancer.existsISecond
    (if Decodable (readWv hsa) then
      (if Decodable (readWv hsb) then (.value 0#32 : LLVM.IntW 32) else .value (-2#32))
     else .value (-1#32))
  refine Firedancer.run_runFunction' _ ?_
  -- %0-%48: the constants, and the `undef`/`insertelement` chain that builds
  -- the all-poison vector the shuffles take as their dead operand
  denote_step_reduce v 48 [LLVM.const?, LLVM.Ty.poison]
  -- %49-%52: `_sa`, `_sb`, `t0a`, `t0b`
  peel_alloca_chain s, cw, 4
  simp only [slotPtr_sa, slotPtr_sb, slotPtr_t0a, slotPtr_t0b]
  rw [← hsAlloc]
  sorry

end Firedancer.Avx512
