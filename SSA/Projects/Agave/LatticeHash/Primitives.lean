/- Released under Apache 2.0 license as described in the file LICENSE. -/
import Std
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace AgaveLattice

-- The AVX2 shift/or arms equal the AVX-512 lane rotate semantics.
theorem ror16 (x : BitVec 32) : ((x >>> 16) ||| (x <<< 16)) = x.rotateRight 16 := by rfl
theorem ror12 (x : BitVec 32) : ((x >>> 12) ||| (x <<< 20)) = x.rotateRight 12 := by rfl
theorem ror8 (x : BitVec 32) : ((x >>> 8) ||| (x <<< 24)) = x.rotateRight 8 := by rfl
theorem ror7 (x : BitVec 32) : ((x >>> 7) ||| (x <<< 25)) = x.rotateRight 7 := by rfl

-- VPBLENDVB chooses each byte using the mask byte's most significant bit.
def blendByte (m : BitVec 32) (a b : BitVec 32) (i : Nat) : BitVec 8 :=
  if m.getLsbD (8 * i + 7) then b.extractLsb' (8 * i) 8 else a.extractLsb' (8 * i) 8

def blendWord (m a b : BitVec 32) : BitVec 32 :=
  blendByte m a b 3 ++ blendByte m a b 2 ++ blendByte m a b 1 ++ blendByte m a b 0

theorem avx2_mask_select (active : Bool) (a b : BitVec 32) :
    blendWord (if active then 0xffffffff#32 else 0#32) a b = (if active then b else a) := by
  cases active <;> simp only [blendWord, blendByte] <;> simp
  all_goals
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 24 = 16 + 8 by rfl)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 16 = 8 + 8 by rfl)]
    exact BitVec.extractLsb'_append_extractLsb'


def mask16 (active : BitVec 16) : BitVec 16 :=
  (BitVec.ofBool (active.getLsbD 0)).setWidth 16 |||
  ((BitVec.ofBool (active.getLsbD 1)).setWidth 16 <<< 1) |||
  ((BitVec.ofBool (active.getLsbD 2)).setWidth 16 <<< 2) |||
  ((BitVec.ofBool (active.getLsbD 3)).setWidth 16 <<< 3) |||
  ((BitVec.ofBool (active.getLsbD 4)).setWidth 16 <<< 4) |||
  ((BitVec.ofBool (active.getLsbD 5)).setWidth 16 <<< 5) |||
  ((BitVec.ofBool (active.getLsbD 6)).setWidth 16 <<< 6) |||
  ((BitVec.ofBool (active.getLsbD 7)).setWidth 16 <<< 7) |||
  ((BitVec.ofBool (active.getLsbD 8)).setWidth 16 <<< 8) |||
  ((BitVec.ofBool (active.getLsbD 9)).setWidth 16 <<< 9) |||
  ((BitVec.ofBool (active.getLsbD 10)).setWidth 16 <<< 10) |||
  ((BitVec.ofBool (active.getLsbD 11)).setWidth 16 <<< 11) |||
  ((BitVec.ofBool (active.getLsbD 12)).setWidth 16 <<< 12) |||
  ((BitVec.ofBool (active.getLsbD 13)).setWidth 16 <<< 13) |||
  ((BitVec.ofBool (active.getLsbD 14)).setWidth 16 <<< 14) |||
  ((BitVec.ofBool (active.getLsbD 15)).setWidth 16 <<< 15)

theorem mask16_exact (active : BitVec 16) : mask16 active = active := by
  ext i hi
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [mask16]


theorem avx512_mask_select (active : BitVec 16) (i : Fin 16) (a b : BitVec 32) :
    (if (mask16 active).getLsbD i then b else a) = (if active.getLsbD i then b else a) := by
  rw [mask16_exact]

-- VPADDW semantics on two adjacent little-endian u16 fields in a u32 word.
def add16 (x y : BitVec 32) : BitVec 32 :=
  (x.extractLsb' 16 16 + y.extractLsb' 16 16) ++
  (x.extractLsb' 0 16 + y.extractLsb' 0 16)

theorem add16_lo (x y : BitVec 32) :
    (add16 x y).extractLsb' 0 16 = x.extractLsb' 0 16 + y.extractLsb' 0 16 := by
  unfold add16
  exact BitVec.extractLsb'_append_eq_right

theorem add16_hi (x y : BitVec 32) :
    (add16 x y).extractLsb' 16 16 = x.extractLsb' 16 16 + y.extractLsb' 16 16 := by
  unfold add16
  exact BitVec.extractLsb'_append_eq_left

theorem add16_assoc (x y z : BitVec 32) : add16 (add16 x y) z = add16 x (add16 y z) := by
  simp only [add16, BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
    BitVec.add_assoc]

theorem add16_comm (x y : BitVec 32) : add16 x y = add16 y x := by
  simp only [add16, BitVec.add_comm]

theorem fold16_lo (xs : List (BitVec 32)) (acc : BitVec 32) :
    (xs.foldl add16 acc).extractLsb' 0 16 =
      xs.foldl (fun s x => s + x.extractLsb' 0 16) (acc.extractLsb' 0 16) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, add16_lo]

theorem fold16_hi (xs : List (BitVec 32)) (acc : BitVec 32) :
    (xs.foldl add16 acc).extractLsb' 16 16 =
      xs.foldl (fun s x => s + x.extractLsb' 16 16) (acc.extractLsb' 16 16) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, add16_hi]

-- Match the implementation's schedule: sum the batch first, then add acc.
theorem fold16_reassociate (xs : List (BitVec 32)) (acc first : BitVec 32) :
    add16 acc (xs.foldl add16 first) = xs.foldl add16 (add16 acc first) := by
  induction xs generalizing first with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih, add16_assoc]

theorem reduction_lo (xs : List (BitVec 32)) (acc first : BitVec 32) :
    (add16 acc (xs.foldl add16 first)).extractLsb' 0 16 =
      xs.foldl (fun s x => s + x.extractLsb' 0 16)
        (acc.extractLsb' 0 16 + first.extractLsb' 0 16) := by
  rw [fold16_reassociate, fold16_lo, add16_lo]

theorem reduction_hi (xs : List (BitVec 32)) (acc first : BitVec 32) :
    (add16 acc (xs.foldl add16 first)).extractLsb' 16 16 =
      xs.foldl (fun s x => s + x.extractLsb' 16 16)
        (acc.extractLsb' 16 16 + first.extractLsb' 16 16) := by
  rw [fold16_reassociate, fold16_hi, add16_hi]

-- Number of non-root blocks; Nat subtraction handles the empty message.
def rootBlock (len : Nat) : Nat := (len - 1) / 64

def laneStep (len block : Nat) : Nat := if len > block * 64 + 64 then block + 1 else block

def laneAt (len : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => laneStep len (laneAt len k)

theorem laneStep_min (len k : Nat) :
    laneStep len (min k (rootBlock len)) = min (k + 1) (rootBlock len) := by
  unfold laneStep
  split
  · unfold rootBlock at *
    omega
  · unfold rootBlock at *
    omega

theorem laneAt_exact (len k : Nat) : laneAt len k = min k (rootBlock len) := by
  induction k with
  | zero => simp [laneAt]
  | succ k ih => simpa only [laneAt, ih] using laneStep_min len k

theorem root_bounds (len : Nat) (h : len ≤ 1024) :
    rootBlock len ≤ 15 ∧ rootBlock len * 64 ≤ len ∧ len ≤ rootBlock len * 64 + 64 := by
  unfold rootBlock
  omega

theorem all_lanes_finished_by_15 (len : Nat) (h : len ≤ 1024) :
    laneAt len 15 = rootBlock len := by
  rw [laneAt_exact]
  have := (root_bounds len h).1
  omega

theorem active_iff_not_root (len k : Nat) :
    (len > laneAt len k * 64 + 64) ↔ laneAt len k < rootBlock len := by
  rw [laneAt_exact]
  unfold rootBlock
  omega

theorem lane_read_bounds (len k : Nat) (h : len ≤ 1024) :
    laneAt len k * 64 ≤ len ∧ laneAt len k * 64 + 64 ≤ 1024 := by
  rw [laneAt_exact]
  have := root_bounds len h
  omega

-- The last block has the specified real length, including the empty case.
theorem root_size (len : Nat) (h : len ≤ 1024) :
    min (len - rootBlock len * 64) 64 = len - rootBlock len * 64 := by
  have := root_bounds len h
  omega

-- Abstract compression history: h at every lane equals the sequential CV after
-- exactly the non-root blocks already consumed. This is parametric in the
-- compression function, so it does not claim BLAKE3-round correctness itself.
def prefixCv {α : Type} (compress : Nat → α → α) (initial : α) : Nat → α
  | 0 => initial
  | block + 1 => compress block (prefixCv compress initial block)

def cvAt {α : Type} (len : Nat) (compress : Nat → α → α) (initial : α) : Nat → α
  | 0 => initial
  | k + 1 =>
    if len > laneAt len k * 64 + 64 then
      compress (laneAt len k) (cvAt len compress initial k)
    else cvAt len compress initial k

theorem cvAt_exact {α : Type} (len k : Nat) (compress : Nat → α → α) (initial : α) :
    cvAt len compress initial k = prefixCv compress initial (min k (rootBlock len)) := by
  induction k with
  | zero => simp [cvAt, prefixCv]
  | succ k ih =>
    rw [cvAt, ih, laneAt_exact]
    have hs := laneStep_min len k
    unfold laneStep at hs
    by_cases h : len > min k (rootBlock len) * 64 + 64
    · rw [ite_eq_left h] at hs ⊢
      rw [← hs, prefixCv]
    · rw [ite_eq_right h] at hs ⊢
      rw [← hs]

-- Output slices cover 1024 u16 elements without overlap in either backend.
theorem layout8_range (x b : Nat) (hx : x < 32) (hb : b < 2) :
    32 * x + 16 * b + 16 ≤ 1024 := by omega

theorem layout16_range (x : Nat) (hx : x < 32) :
    32 * x + 32 ≤ 1024 := by omega

theorem layout8_cover (i : Nat) (hi : i < 1024) :
    i = 32 * (i / 32) + 16 * (i % 32 / 16) + i % 16 ∧
    i / 32 < 32 ∧ i % 32 / 16 < 2 ∧ i % 16 < 16 := by omega

theorem layout16_cover (i : Nat) (hi : i < 1024) :
    i = 32 * (i / 32) + i % 32 ∧ i / 32 < 32 ∧ i % 32 < 32 := by omega

theorem layout8_unique (x b j x' b' j' : Nat)
    (hb : b < 2) (hj : j < 16) (hb' : b' < 2) (hj' : j' < 16)
    (he : 32*x + 16*b + j = 32*x' + 16*b' + j') :
    x = x' ∧ b = b' ∧ j = j' := by omega

theorem layout16_unique (x j x' j' : Nat) (hj : j < 32) (hj' : j' < 32)
    (he : 32*x + j = 32*x' + j') : x = x' ∧ j = j' := by omega

theorem input_word_offset (len k : Nat) : laneAt len k * 64 / 4 = laneAt len k * 16 := by omega

theorem input_tile8_range (len k b : Nat) (hlen : len ≤ 1024) (hb : b < 2) :
    laneAt len k * 64 / 4 + b * 8 + 8 ≤ 256 := by
  have := lane_read_bounds len k hlen
  omega

theorem input_tile16_range (len k : Nat) (hlen : len ≤ 1024) :
    laneAt len k * 64 / 4 + 16 ≤ 256 := by
  have := lane_read_bounds len k hlen
  omega





#print axioms ror16
#print axioms ror12
#print axioms ror8
#print axioms ror7
#print axioms avx2_mask_select
#print axioms mask16_exact
#print axioms avx512_mask_select
#print axioms add16_lo
#print axioms add16_hi
#print axioms add16_assoc
#print axioms add16_comm
#print axioms fold16_lo
#print axioms fold16_hi
#print axioms fold16_reassociate
#print axioms reduction_lo
#print axioms reduction_hi
#print axioms laneStep_min
#print axioms laneAt_exact
#print axioms root_bounds
#print axioms all_lanes_finished_by_15
#print axioms active_iff_not_root
#print axioms lane_read_bounds
#print axioms root_size
#print axioms cvAt_exact
#print axioms layout8_range
#print axioms layout16_range
#print axioms layout8_cover
#print axioms layout16_cover
#print axioms layout8_unique
#print axioms layout16_unique
#print axioms input_word_offset
#print axioms input_tile8_range
#print axioms input_tile16_range

end AgaveLattice
