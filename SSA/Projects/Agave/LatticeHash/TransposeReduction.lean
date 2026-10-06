/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Primitives
import SSA.Projects.Agave.LatticeHash.Transpose

namespace AgaveLattice

-- Backend-independent specification of a checked N-by-N transpose.
def IsTranspose (n : Nat) (perm : Matrix) : Prop :=
  ∀ r c : Fin n, perm r c = (c.val, r.val)

theorem avx2_isTranspose : IsTranspose 8 (transpose8 labels) := transpose8_mapping
theorem avx512_isTranspose : IsTranspose 16 (transpose16 labels) := transpose16_mapping

theorem transpose_payload {α : Type} {n : Nat} {perm : Matrix}
    (hp : IsTranspose n perm) (m : Nat → Nat → α) (r c : Fin n) :
    applyPerm perm m r c = m c r := by
  unfold applyPerm
  rw [hp r c]

-- Literal load_m indexing: off[l] is a byte offset, and each load supplies
-- N successive u32 words of one message. Rows initially name messages.
def loadTile {α : Type} (n : Nat) (words : Nat → Nat → α)
    (off : Nat → Nat) (blk : Nat) : Nat → Nat → α :=
  fun lane word => words lane (off lane / 4 + blk * n + word)

theorem load_transpose_per_word {α : Type} {n : Nat} {perm : Matrix}
    (hp : IsTranspose n perm) (words : Nat → Nat → α) (off : Nat → Nat)
    (blk : Nat) (word lane : Fin n) :
    applyPerm perm (loadTile n words off blk) word lane =
      words lane (off lane / 4 + blk * n + word) := by
  exact transpose_payload hp _ word lane

-- The sixteen loaded word vectors, indexed as m[word][lane].
def loadWords {α : Type} (n : Nat) (perm : Matrix) (words : Nat → Nat → α)
    (off : Nat → Nat) (word lane : Nat) : α :=
  applyPerm perm (loadTile n words off (word / n)) (word % n) lane

theorem loadWords_correct {α : Type} {n : Nat} {perm : Matrix}
    (hn : 0 < n) (hp : IsTranspose n perm) (words : Nat → Nat → α)
    (off : Nat → Nat) (word : Fin 16) (lane : Fin n) :
    loadWords n perm words off word lane = words lane (off lane / 4 + word) := by
  unfold loadWords
  rw [load_transpose_per_word hp words off (word.val / n)
    ⟨word.val % n, Nat.mod_lt _ hn⟩ lane]
  simp only
  congr 1
  have h := Nat.div_add_mod' word.val n
  omega

-- xof lane block word is the already-produced BLAKE3 XOF u32 value.
-- This file proves data movement and LtHash addition, parametrically in xof.
abbrev XofWords := Nat → Nat → Nat → BitVec 32
abbrev LtAcc := Nat → BitVec 16

def outputRows (n : Nat) (perm : Matrix) (xof : XofWords)
    (block blk : Nat) (lane word : Fin n) : BitVec 32 :=
  applyPerm perm (fun w l => xof l block (blk * n + w)) lane word

theorem output_transpose_per_message {n : Nat} {perm : Matrix}
    (hp : IsTranspose n perm) (xof : XofWords) (block blk : Nat)
    (lane word : Fin n) :
    outputRows n perm xof block blk lane word = xof lane block (blk * n + word) := by
  exact transpose_payload hp _ lane word

-- Low then high u16 fields are the x86 little-endian accumulator order.
def halfWord (word : BitVec 32) (half : Fin 2) : BitVec 16 :=
  word.extractLsb' (16 * half.val) 16

def packAcc (acc : LtAcc) (base : Nat) : BitVec 32 := acc (base + 1) ++ acc base

theorem halfWord_packAcc (acc : LtAcc) (base : Nat) (half : Fin 2) :
    halfWord (packAcc acc base) half = acc (base + half) := by
  rcases half with ⟨half, hh⟩
  have hc : half = 0 ∨ half = 1 := by omega
  rcases hc with rfl | rfl
  · change (acc (base + 1) ++ acc base).extractLsb' 0 16 = acc base
    exact BitVec.extractLsb'_append_eq_right
  · change (acc (base + 1) ++ acc base).extractLsb' 16 16 = acc (base + 1)
    exact BitVec.extractLsb'_append_eq_left

theorem halfWord_fold (xs : List (BitVec 32)) (acc : BitVec 32) (half : Fin 2) :
    halfWord (xs.foldl add16 acc) half =
      xs.foldl (fun s word => s + halfWord word half) (halfWord acc half) := by
  rcases half with ⟨half, hh⟩
  have hc : half = 0 ∨ half = 1 := by omega
  rcases hc with rfl | rfl
  · exact fold16_lo xs acc
  · exact fold16_hi xs acc

-- Exact Rust schedule: initialize s with tile[0], fold tile[1..n], then
-- add the loaded accumulator. Every addition is wrapping in each u16 field.
def laneSum (n : Nat) (hn : 0 < n) (row : Fin n → BitVec 32) : BitVec 32 :=
  ((List.finRange n).tail.map row).foldl add16 (row ⟨0, hn⟩)

theorem laneSum_update (n : Nat) (hn : 0 < n) (row : Fin n → BitVec 32)
    (acc : BitVec 32) :
    add16 acc (laneSum n hn row) = ((List.finRange n).map row).foldl add16 acc := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [laneSum, List.finRange_succ, List.tail_cons, List.map_cons, List.foldl_cons]
    exact fold16_reassociate _ acc _

def outputIndex (n block blk word half : Nat) : Nat :=
  32 * block + 2 * (blk * n + word) + half

def tileResult (n : Nat) (hn : 0 < n) (perm : Matrix) (xof : XofWords)
    (acc : LtAcc) (block blk : Nat) (word : Fin n) (half : Fin 2) : BitVec 16 :=
  halfWord (add16 (packAcc acc (outputIndex n block blk word 0))
    (laneSum n hn (fun lane => outputRows n perm xof block blk lane word))) half

theorem transpose_reduce_update {n : Nat} {perm : Matrix}
    (hn : 0 < n) (hp : IsTranspose n perm) (xof : XofWords) (acc : LtAcc)
    (block blk : Nat) (word : Fin n) (half : Fin 2) :
    tileResult n hn perm xof acc block blk word half =
      (List.finRange n).foldl
        (fun sum (lane : Fin n) => sum + halfWord (xof lane block (blk * n + word)) half)
        (acc (outputIndex n block blk word half)) := by
  unfold tileResult
  rw [laneSum_update, halfWord_fold, halfWord_packAcc, List.foldl_map]
  simp only [output_transpose_per_message hp, outputIndex, Nat.add_zero]

-- Scalar semantics: decode each message's consecutive little-endian u16
-- output fields, then mix messages into the existing LtHash one by one.
def scalarMessage (xof : XofWords) (lane index : Nat) : BitVec 16 :=
  halfWord (xof lane (index / 32) (index % 32 / 2)) ⟨index % 2, Nat.mod_lt _ (by decide)⟩

def scalarLtHash (n : Nat) (xof : XofWords) (acc : LtAcc) : LtAcc :=
  (List.finRange n).foldl (fun a (lane : Fin n) => fun index => a index + scalarMessage xof lane index) acc

theorem fold_function_apply {α β : Type} (xs : List α) (f : α → Nat → β)
    (op : β → β → β) (acc : Nat → β) (index : Nat) :
    (xs.foldl (fun a x => fun i => op (a i) (f x i)) acc) index =
      xs.foldl (fun a x => op a (f x index)) (acc index) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ih]

theorem scalarLtHash_apply (n : Nat) (xof : XofWords) (acc : LtAcc) (index : Nat) :
    scalarLtHash n xof acc index =
      (List.finRange n).foldl (fun a (lane : Fin n) => a + scalarMessage xof lane index) (acc index) := by
  exact fold_function_apply (List.finRange n)
    (fun (lane : Fin n) i => scalarMessage xof lane i) (· + ·) acc index

-- Pointwise result of all tile stores. Coverage and uniqueness below show
-- that exactly this one tile/word/half writes every accumulator position.
def simdLtHash (n : Nat) (hn : 0 < n) (perm : Matrix) (xof : XofWords)
    (acc : LtAcc) (index : Nat) : BitVec 16 :=
  let word := index % 32 / 2
  tileResult n hn perm xof acc (index / 32) (word / n)
    ⟨word % n, Nat.mod_lt _ hn⟩ ⟨index % 2, Nat.mod_lt _ (by decide)⟩

theorem decoded_word (n index : Nat) :
    (index % 32 / 2 / n) * n + index % 32 / 2 % n = index % 32 / 2 :=
  Nat.div_add_mod' _ _

theorem decoded_index (n index : Nat) :
    outputIndex n (index / 32) (index % 32 / 2 / n) (index % 32 / 2 % n) (index % 2) = index := by
  unfold outputIndex
  rw [decoded_word]
  omega

theorem simdLtHash_eq_scalarLtHash {n : Nat} {perm : Matrix}
    (hn : 0 < n) (hp : IsTranspose n perm) (xof : XofWords) (acc : LtAcc) :
    simdLtHash n hn perm xof acc = scalarLtHash n xof acc := by
  funext index
  unfold simdLtHash
  rw [transpose_reduce_update hn hp, scalarLtHash_apply]
  simp only [decoded_word, decoded_index, scalarMessage]

-- Complete finite coverage of the source's 16-word input block and 1024-u16
-- output. Backend restriction supplies exactly 2 tiles of 8 or 1 tile of 16.
def SupportedLanes (n : Nat) : Prop := n = 8 ∨ n = 16

theorem supported_positive {n : Nat} (hn : SupportedLanes n) : 0 < n := by
  rcases hn with rfl | rfl <;> decide

theorem lane_iteration_coverage (n : Nat) (lane : Fin n) : lane ∈ List.finRange n :=
  List.mem_finRange lane

theorem lane_iteration_no_overlap (n : Nat) : (List.finRange n).Nodup :=
  List.nodup_finRange n

theorem input_tile_coverage {n : Nat} (hn : SupportedLanes n) (word : Fin 16) :
    ∃ blk : Fin (16 / n), ∃ j : Fin n, blk.val * n + j.val = word.val := by
  rcases hn with rfl | rfl
  · exact ⟨⟨word / 8, by omega⟩, ⟨word % 8, by omega⟩, Nat.div_add_mod' word 8⟩
  · exact ⟨⟨word / 16, by omega⟩, ⟨word % 16, by omega⟩, Nat.div_add_mod' word 16⟩

theorem input_tile_no_overlap {n : Nat} (hn : SupportedLanes n)
    (blk blk' : Fin (16 / n)) (word word' : Fin n)
    (he : blk.val * n + word.val = blk'.val * n + word'.val) :
    blk = blk' ∧ word = word' := by
  rcases hn with rfl | rfl
  all_goals constructor <;> apply Fin.ext <;> omega

theorem output_index_in_range {n : Nat} (hn : SupportedLanes n)
    (block : Fin 32) (blk : Fin (16 / n)) (word : Fin n) (half : Fin 2) :
    outputIndex n block blk word half < 1024 := by
  rcases hn with rfl | rfl <;> unfold outputIndex <;> omega

theorem output_index_coverage {n : Nat} (hn : SupportedLanes n) (index : Fin 1024) :
    ∃ block : Fin 32, ∃ blk : Fin (16 / n), ∃ word : Fin n, ∃ half : Fin 2,
      outputIndex n block blk word half = index := by
  rcases hn with rfl | rfl
  · exact ⟨⟨index / 32, by omega⟩, ⟨index % 32 / 2 / 8, by omega⟩,
      ⟨index % 32 / 2 % 8, by omega⟩, ⟨index % 2, by omega⟩, decoded_index 8 index⟩
  · exact ⟨⟨index / 32, by omega⟩, ⟨index % 32 / 2 / 16, by omega⟩,
      ⟨index % 32 / 2 % 16, by omega⟩, ⟨index % 2, by omega⟩, decoded_index 16 index⟩

theorem output_index_no_overlap {n : Nat} (hn : SupportedLanes n)
    (block block' : Fin 32) (blk blk' : Fin (16 / n))
    (word word' : Fin n) (half half' : Fin 2)
    (he : outputIndex n block blk word half = outputIndex n block' blk' word' half') :
    block = block' ∧ blk = blk' ∧ word = word' ∧ half = half' := by
  rcases hn with rfl | rfl
  all_goals
    unfold outputIndex at he
    refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega

theorem avx2_load_correct {α : Type} (words : Nat → Nat → α) (off : Nat → Nat)
    (word : Fin 16) (lane : Fin 8) :
    loadWords 8 (transpose8 labels) words off word lane = words lane (off lane / 4 + word) :=
  loadWords_correct (by decide) avx2_isTranspose words off word lane

theorem avx512_load_correct {α : Type} (words : Nat → Nat → α) (off : Nat → Nat)
    (word : Fin 16) (lane : Fin 16) :
    loadWords 16 (transpose16 labels) words off word lane = words lane (off lane / 4 + word) :=
  loadWords_correct (by decide) avx512_isTranspose words off word lane

theorem avx2_LtHash_update (xof : XofWords) (acc : LtAcc) :
    simdLtHash 8 (by decide) (transpose8 labels) xof acc = scalarLtHash 8 xof acc :=
  simdLtHash_eq_scalarLtHash (by decide) avx2_isTranspose xof acc

theorem avx512_LtHash_update (xof : XofWords) (acc : LtAcc) :
    simdLtHash 16 (by decide) (transpose16 labels) xof acc = scalarLtHash 16 xof acc :=
  simdLtHash_eq_scalarLtHash (by decide) avx512_isTranspose xof acc

end AgaveLattice
