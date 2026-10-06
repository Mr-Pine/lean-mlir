import SSA.Projects.Agave.Ed25519.Proof.NAF.Memory
import SSA.Projects.Agave.Ed25519.Spec.NAF

/-!
# The NAF loop's byte-store invariant

This file gives the memory transformer for the emitted loop: the even branch
does not store, while a nonzero digit stores one byte and advances by the source
width. It proves the byte reads of that transformer equal `NAF.digits`, deriving
the zero gaps from the initial memset and the strictly increasing cursor.

This is the induction invariant for the imported CFG. It is not a theorem that
`kernel5.call` or `kernel8.call` executes this transformer; that connection must
also account for the actual registers, branch edges and scratch-word loads.
-/
namespace Agave.Ed25519.NAF.Memory

open LeanMLIR.RIR

/-- A byte is stored only on the odd-window path. -/
def emitByte (digits : BitVec 2048) (pos : Nat) (digit : Int) : BitVec 2048 :=
  if digit = 0 then digits else writeSlot digits pos (BitVec.ofInt 8 digit)

def arrayLoop (width : Nat) : Nat → Nat → State → BitVec 2048 → BitVec 2048
  | 0, _, _, digits => digits
  | fuel + 1, pos, state, digits =>
      if pos < 256 then
        let transition := step width state
        arrayLoop width fuel (pos + transition.advance) transition.next
          (emitByte digits pos transition.digit)
      else digits

/-- The real `MemoryState.storeAt` sequence, retaining the rest of memory. -/
def storeLoop (width : Nat) (out : Pointer) : Nat → Nat → State → MemoryState → MemoryState
  | 0, _, _, mem => mem
  | fuel + 1, pos, state, mem =>
      if pos < 256 then
        let transition := step width state
        let mem' := if transition.digit = 0 then mem else
          mem.storeAt (out.add (BitVec.ofNat 64 pos)) (BitVec.ofInt 8 transition.digit)
        storeLoop width out fuel (pos + transition.advance) transition.next mem'
      else mem

/-- No future output position has yet been written. -/
def ZeroFrom (digits : BitVec 2048) (pos : Nat) : Prop :=
  ∀ i : Fin 256, pos ≤ i.val → slot digits i.val = 0

theorem zeroFrom_zero (pos : Nat) : ZeroFrom 0 pos := by
  intro i _
  simp [slot]

theorem emitByte_slot (digits : BitVec 2048) (pos i : Fin 256) (digit : Int)
    (hzero : slot digits pos.val = 0) :
    slot (emitByte digits pos.val digit) i.val =
      if i = pos then BitVec.ofInt 8 digit else slot digits i.val := by
  by_cases hd : digit = 0
  · subst digit
    by_cases hi : i = pos
    · subst i
      simp [emitByte, hzero]
    · simp [emitByte, hi]
  · simpa only [emitByte, if_neg hd] using slot_writeSlot digits pos i (BitVec.ofInt 8 digit)

theorem zeroFrom_emitByte {digits : BitVec 2048} {pos : Nat}
    (hzero : ZeroFrom digits pos) (hp : pos < 256) (digit : Int)
    (advance : Nat) (ha : 1 ≤ advance) :
    ZeroFrom (emitByte digits pos digit) (pos + advance) := by
  intro i hi
  have hne : i ≠ (⟨pos, hp⟩ : Fin 256) := by
    intro he
    have he' := congrArg Fin.val he
    change i.val = pos at he'
    omega
  rw [emitByte_slot digits ⟨pos, hp⟩ i digit (hzero ⟨pos, hp⟩ (Nat.le_refl pos)), if_neg hne]
  exact hzero i (by omega)

/-- Strict progress ensures later iterations cannot overwrite this iteration's
byte. The remaining zero suffix supplies all digits skipped by `advance`. -/
theorem arrayLoop_slot (width : Nat) (hw : Supported width) (fuel pos : Nat)
    (state : State) (digits : BitVec 2048) (hzero : ZeroFrom digits pos) (i : Fin 256) :
    slot (arrayLoop width fuel pos state digits) i.val =
      if i.val < pos then slot digits i.val
      else BitVec.ofInt 8 (NAF.digits width fuel pos state i.val) := by
  induction fuel generalizing pos state digits with
  | zero =>
      by_cases hi : i.val < pos
      · simp [arrayLoop, hi]
      · simpa [arrayLoop, NAF.digits, hi] using hzero i (by omega)
  | succ fuel ih =>
      by_cases hp : pos < 256
      · let t := step width state
        have hadvance : 1 ≤ t.advance := (advance_bounds width hw state).1
        have hzero' := zeroFrom_emitByte hzero hp t.digit t.advance hadvance
        rw [arrayLoop, if_pos hp, ih _ _ _ hzero']
        rw [emitByte_slot digits ⟨pos, hp⟩ i t.digit (hzero ⟨pos, hp⟩ (Nat.le_refl pos))]
        have heq : i = (⟨pos, hp⟩ : Fin 256) ↔ i.val = pos := by
          exact Fin.ext_iff
        simp only [heq]
        by_cases hi : i.val < pos
        · have hinext : i.val < pos + t.advance := by omega
          have hne : i.val ≠ pos := by omega
          simp only [hi, if_true, hinext, hne, if_false]
        · by_cases he : i.val = pos
          · have hinext : i.val < pos + t.advance := by omega
            rw [if_pos hinext]
            simp [he, t, NAF.digits, hp]
          · simp only [hi, if_false, he, NAF.digits, hp, if_true]
            by_cases hinext : i.val < pos + t.advance
            · rw [if_pos hinext]
              have hbefore := digits_before width hw fuel (pos + t.advance) t.next i.val hinext
              rw [hbefore]
              simpa using hzero i (by omega)
            · rw [if_neg hinext]
      · have hi : i.val < pos := by have := i.isLt; omega
        simp [arrayLoop, hp, hi]

/-- Freshly zeroed output is transformed into exactly the source digit array. -/
theorem arrayLoop_sourceDigits (width : Nat) (hw : Supported width) (n : Nat) (i : Fin 256) :
    slot (arrayLoop width 256 0 ⟨n, 0⟩ 0) i.val =
      BitVec.ofInt 8 (sourceDigits width n i) := by
  simpa only [Nat.not_lt_zero, if_false, sourceDigits] using
    arrayLoop_slot width hw 256 0 ⟨n, 0⟩ 0 (zeroFrom_zero 0) i

theorem storeLoop_buffer (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : State) (mem : MemoryState) (h : Buffer mem p bytes) :
    Buffer (storeLoop width out fuel pos state mem) p bytes := by
  induction fuel generalizing pos state mem with
  | zero => exact h
  | succ fuel ih =>
      by_cases hp : pos < 256
      · rw [storeLoop, if_pos hp]
        dsimp only
        by_cases hd : (step width state).digit = 0
        · rw [if_pos hd]
          exact ih _ _ _ h
        · rw [if_neg hd]
          exact ih _ _ _ (h.storeAt _ _)
      · simpa only [storeLoop, if_neg hp] using h

/-- Fresh scratch objects and other caller allocations are not changed by the
output stores. Allocation separation, not a value invariant, proves this. -/
theorem storeLoop_preserves_other_block (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : State) (mem : MemoryState) (q : Pointer) (bits : Nat)
    (hseparate : out.id ≠ q.id) :
    (storeLoop width out fuel pos state mem).readAt q bits = mem.readAt q bits := by
  induction fuel generalizing pos state mem with
  | zero => rfl
  | succ fuel ih =>
      by_cases hp : pos < 256
      · rw [storeLoop, if_pos hp]
        dsimp only
        by_cases hd : (step width state).digit = 0
        · rw [if_pos hd]
          exact ih _ _ _
        · rw [if_neg hd, ih]
          exact MemoryState.readAt_storeAt_disjoint
            (p := out.add (BitVec.ofNat 64 pos)) (q := q)
            (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hseparate))
            (BitVec.ofInt 8 (step width state).digit)
      · simp only [storeLoop, if_neg hp]

/-- Byte splices describe the actual sequence of RIR memory stores. Bounds for
every store come from the output allocation and `pos < 256`. -/
theorem storeLoop_read (width : Nat) (out : Pointer) (fuel pos : Nat)
    (state : State) (mem : MemoryState) (h : Buffer mem out 256) :
    (storeLoop width out fuel pos state mem).readAt out 2048 =
      arrayLoop width fuel pos state (mem.readAt out 2048) := by
  induction fuel generalizing pos state mem with
  | zero => rfl
  | succ fuel ih =>
      by_cases hp : pos < 256
      · rw [storeLoop, if_pos hp, arrayLoop, if_pos hp]
        by_cases hd : (step width state).digit = 0
        · simp only [hd, if_true, emitByte]
          exact ih _ _ _ h
        · simp only [hd, if_false, emitByte]
          rw [ih _ _ _ (h.storeAt _ _)]
          rw [write_slot h _ rfl ⟨pos, hp⟩]
      · simp only [storeLoop, arrayLoop, hp, if_false]

/-- The store invariant has no digit-correctness premise: all bytes come from
the input scalar and the initially zero output established by memset. -/
theorem storeLoop_sourceDigits (width : Nat) (hw : Supported width) (n : Nat)
    (out : Pointer) (mem : MemoryState) (h : Buffer mem out 256)
    (hzero : mem.readAt out 2048 = 0) (i : Fin 256) :
    (storeLoop width out 256 0 ⟨n, 0⟩ mem).readAt
      (out.add (BitVec.ofNat 64 i.val)) 8 = BitVec.ofInt 8 (sourceDigits width n i) := by
  rw [read_slot (storeLoop_buffer width out 256 0 ⟨n, 0⟩ mem h) _ rfl i]
  rw [storeLoop_read width out 256 0 ⟨n, 0⟩ mem h, hzero]
  exact arrayLoop_sourceDigits width hw n i

end Agave.Ed25519.NAF.Memory
