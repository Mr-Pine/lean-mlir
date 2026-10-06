/- Released under Apache 2.0 license as described in the file LICENSE. -/
import Std

namespace AgaveLattice
abbrev Label := Nat × Nat
abbrev Row := Nat → Label
abbrev Matrix := Nat → Row

-- Each label records the original (row, word) of one u32 lane.
-- The unpack instructions operate separately on each 128-bit group (4 u32).
def unpack32 (high : Bool) (a b : Row) : Row := fun i =>
  let j := i / 4 * 4 + i % 4 / 2 + if high then 2 else 0
  if i % 2 = 0 then a j else b j

def unpack64 (high : Bool) (a b : Row) : Row := fun i =>
  let j := i / 4 * 4 + i % 2 + if high then 2 else 0
  if i % 4 < 2 then a j else b j

-- Only immediates 0x20 and 0x31 are used: neither zeroes a half.
def permute2x128 (imm : Nat) (a b : Row) : Row := fun i =>
  let sel := if i < 4 then imm % 4 else imm / 16 % 4
  let j := sel % 2 * 4 + i % 4
  if sel < 2 then a j else b j

-- Destination 128-bit groups 0,1 come from a and groups 2,3 from b.
def shuffle128 (imm : Nat) (a b : Row) : Row := fun i =>
  let group := i / 4
  let sel := imm / (4 ^ group) % 4
  let j := sel * 4 + i % 4
  if group < 2 then a j else b j

def labels : Matrix := fun r c => (r, c)

def transpose8 (io : Matrix) : Matrix :=
  let a := io 0
  let b := io 1
  let c := io 2
  let d := io 3
  let e := io 4
  let f := io 5
  let g := io 6
  let h := io 7
  let t0 := unpack32 false a b
  let t1 := unpack32 true a b
  let t2 := unpack32 false c d
  let t3 := unpack32 true c d
  let t4 := unpack32 false e f
  let t5 := unpack32 true e f
  let t6 := unpack32 false g h
  let t7 := unpack32 true g h
  let u0 := unpack64 false t0 t2
  let u1 := unpack64 true t0 t2
  let u2 := unpack64 false t1 t3
  let u3 := unpack64 true t1 t3
  let u4 := unpack64 false t4 t6
  let u5 := unpack64 true t4 t6
  let u6 := unpack64 false t5 t7
  let u7 := unpack64 true t5 t7
  fun row =>
    if row = 0 then permute2x128 32 u0 u4 else
    if row = 1 then permute2x128 32 u1 u5 else
    if row = 2 then permute2x128 32 u2 u6 else
    if row = 3 then permute2x128 32 u3 u7 else
    if row = 4 then permute2x128 49 u0 u4 else
    if row = 5 then permute2x128 49 u1 u5 else
    if row = 6 then permute2x128 49 u2 u6 else
    permute2x128 49 u3 u7

theorem transpose8_mapping : ∀ r c : Fin 8,
    transpose8 labels r c = (c.val, r.val) := by decide

def transpose16 (io : Matrix) : Matrix :=
  let r := io
  let t0 := shuffle128 136 (r 0) (r 4)
  let t1 := shuffle128 136 (r 1) (r 5)
  let t2 := shuffle128 136 (r 2) (r 6)
  let t3 := shuffle128 136 (r 3) (r 7)
  let t4 := shuffle128 221 (r 0) (r 4)
  let t5 := shuffle128 221 (r 1) (r 5)
  let t6 := shuffle128 221 (r 2) (r 6)
  let t7 := shuffle128 221 (r 3) (r 7)
  let t8 := shuffle128 136 (r 8) (r 12)
  let t9 := shuffle128 136 (r 9) (r 13)
  let ta := shuffle128 136 (r 10) (r 14)
  let tb := shuffle128 136 (r 11) (r 15)
  let tc := shuffle128 221 (r 8) (r 12)
  let td := shuffle128 221 (r 9) (r 13)
  let te := shuffle128 221 (r 10) (r 14)
  let tf := shuffle128 221 (r 11) (r 15)
  let r0 := shuffle128 136 t0 t8
  let r1 := shuffle128 136 t1 t9
  let r2 := shuffle128 136 t2 ta
  let r3 := shuffle128 136 t3 tb
  let r4 := shuffle128 136 t4 tc
  let r5 := shuffle128 136 t5 td
  let r6 := shuffle128 136 t6 te
  let r7 := shuffle128 136 t7 tf
  let r8 := shuffle128 221 t0 t8
  let r9 := shuffle128 221 t1 t9
  let ra := shuffle128 221 t2 ta
  let rb := shuffle128 221 t3 tb
  let rc := shuffle128 221 t4 tc
  let rd := shuffle128 221 t5 td
  let re := shuffle128 221 t6 te
  let rf := shuffle128 221 t7 tf
  let t0 := unpack32 false r0 r2
  let t1 := unpack32 false r1 r3
  let t2 := unpack32 true r0 r2
  let t3 := unpack32 true r1 r3
  let t4 := unpack32 false r4 r6
  let t5 := unpack32 false r5 r7
  let t6 := unpack32 true r4 r6
  let t7 := unpack32 true r5 r7
  let t8 := unpack32 false r8 ra
  let t9 := unpack32 false r9 rb
  let ta := unpack32 true r8 ra
  let tb := unpack32 true r9 rb
  let tc := unpack32 false rc re
  let td := unpack32 false rd rf
  let te := unpack32 true rc re
  let tf := unpack32 true rd rf
  fun row =>
    if row = 0 then unpack32 false t0 t1 else
    if row = 1 then unpack32 true t0 t1 else
    if row = 2 then unpack32 false t2 t3 else
    if row = 3 then unpack32 true t2 t3 else
    if row = 4 then unpack32 false t4 t5 else
    if row = 5 then unpack32 true t4 t5 else
    if row = 6 then unpack32 false t6 t7 else
    if row = 7 then unpack32 true t6 t7 else
    if row = 8 then unpack32 false t8 t9 else
    if row = 9 then unpack32 true t8 t9 else
    if row = 10 then unpack32 false ta tb else
    if row = 11 then unpack32 true ta tb else
    if row = 12 then unpack32 false tc td else
    if row = 13 then unpack32 true tc td else
    if row = 14 then unpack32 false te tf else
    unpack32 true te tf

theorem transpose16_mapping : ∀ r c : Fin 16,
    transpose16 labels r c = (c.val, r.val) := by decide

-- Lift the checked provenance permutation to arbitrary payloads.
def applyPerm {α : Type} (perm : Matrix) (m : Nat → Nat → α) (r c : Nat) : α :=
  let src := perm r c
  m src.1 src.2

theorem transpose8_payload {α : Type} (m : Nat → Nat → α) (r c : Fin 8) :
    applyPerm (transpose8 labels) m r c = m c r := by
  unfold applyPerm
  rw [transpose8_mapping r c]

theorem transpose16_payload {α : Type} (m : Nat → Nat → α) (r c : Fin 16) :
    applyPerm (transpose16 labels) m r c = m c r := by
  unfold applyPerm
  rw [transpose16_mapping r c]

end AgaveLattice
