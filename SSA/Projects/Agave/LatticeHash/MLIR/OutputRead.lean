/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionMemory

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression CompressionExit

/-- A disjoint write within the same allocation preserves a byte-backed read. -/
theorem readWord?_splice_disjoint {m : MemoryState} {p q : Pointer}
    {w w' : Nat} (x : BitVec w')
    (h : q.offsetInBits + w' ≤ p.offsetInBits ∨
      p.offsetInBits + w ≤ q.offsetInBits) :
    readWord? p w (m.splice q x) = readWord? p w m := by
  by_cases hid : q.id = p.id
  · cases hb : m.live? q.id with
    | none => simp only [readWord?, ← hid, splicedDead hb, hb]
    | some b =>
      simp only [readWord?, ← hid, splicedLive m q b hb x, hb]
      exact congrArg some (extractLsb'_spliceBits_of_disjoint _ _ _ _ h.symm)
  · exact readWord?_splice_ne hid

/-- A bounded byte offset has the expected bit offset, without modular wrap. -/
theorem offsetInBits_withOffset_nat (p : Pointer) (k : Nat)
    (h : p.offset.toNat + k < 2^64) :
    (p.withOffset (BitVec.ofNat 64 k)).offsetInBits = p.offsetInBits + 8*k := by
  have hk : k < 2^64 := by omega
  simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt h]
  omega

/-- Every output-row pointer lies in the contiguous output region. -/
theorem outputRow_offset {n : Nat} (out : Pointer)
    (hwrap : out.offset.toNat + 64*n ≤ 2^64) (k : Fin 16) :
    (out.withOffset (BitVec.ofNat 64 (4*n*k.val))).offsetInBits =
      out.offsetInBits + 32*n*k.val := by
  have hk := k.isLt
  have hoff := out.offset.isLt
  have hmul : 4*n*k.val < 64*n ∨ n = 0 := by
    by_cases hn : n = 0
    · exact Or.inr hn
    · left
      have hm := Nat.mul_lt_mul_of_pos_left hk (show 0 < 4*n by omega)
      omega
  have hb : out.offset.toNat + 4*n*k.val < 2^64 := by
    rcases hmul with hmul | hn
    · omega
    · subst n; simpa using hoff
  rw [offsetInBits_withOffset_nat out _ hb]
  congr 1
  simp only [← Nat.mul_assoc]

/-- Reading any completed row yields exactly its computed vector. Later
stores cannot overwrite it, including when all rows share one allocation. -/
theorem outputMem_read_row {n : Nat} (out : Pointer) (v : State (Vector Word n))
    (m : MemoryState) (hfit : Fits m out (512*n))
    (hwrap : out.offset.toNat + 64*n ≤ 2^64)
    (count : Nat) (hc : count ≤ 16) (i : Fin 16) (hi : i.val < count) :
    readWord? (out.withOffset (BitVec.ofNat 64 (4*n*i.val))) (32*n)
      (outputMem out v count m) = some (packBits (v i)) := by
  induction count with
  | zero => omega
  | succ k ih =>
    have hk : k < 16 := by omega
    have hko := outputRow_offset out hwrap ⟨k, hk⟩
    change (out.withOffset (BitVec.ofNat 64 (4*n*k))).offsetInBits =
      out.offsetInBits + 32*n*k at hko
    have hio := outputRow_offset out hwrap i
    simp only [outputMem]
    by_cases he : i.val = k
    · have heq : Fin.ofNat 16 k = i := by
        apply Fin.ext
        simp only [Fin.ofNat, Nat.mod_eq_of_lt hk]
        exact he.symm
      rw [heq, ← he]
      apply readWord?_splice_self
      apply fits_outputMem out v i.val
      obtain ⟨b, hb, hlen⟩ := hfit
      refine ⟨b, hb, ?_⟩
      rw [hio]
      have hmul := Nat.mul_le_mul_left (32*n) (show i.val+1 ≤ 16 from i.isLt)
      simp only [Nat.mul_add, Nat.mul_one] at hmul
      omega
    · rw [readWord?_splice_disjoint]
      · exact ih (by omega) (by omega)
      · right
        rw [hko, hio]
        have hmul := Nat.mul_le_mul_left (32*n) (show i.val+1 ≤ k by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hmul
        omega

/-- A smaller read of the same allocated bytes extracts the matching bits. -/
theorem readWord?_extract {m : MemoryState} {p q : Pointer} {w w' k : Nat}
    (x : BitVec w) (hp : Fits m p w) (hr : readWord? p w m = some x)
    (hid : q.id = p.id) (hoff : q.offsetInBits = p.offsetInBits+k)
    (hk : k+w' ≤ w) :
    readWord? q w' m = some (x.extractLsb' k w') := by
  obtain ⟨b, hb, hlen⟩ := hp
  have hlive : m.live? p.id = some b := by simp [MemoryState.live?, hb]
  have hx : b.bytes.extractLsb' p.offsetInBits w = x := by
    simpa [readWord?, hlive] using hr
  simp only [readWord?, hid, hlive, Option.pure_def, hoff]
  apply congrArg some
  rw [← hx]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  simp [show k+j < w by omega, Nat.add_assoc]

/-- Every 32-bit output word can be observed at its actual byte address.
The single no-wrap bound prevents the abstract pointer arithmetic from
wrapping inside an otherwise oversized memory allocation. -/
theorem outputMem_read_lane {n : Nat} (out : Pointer) (v : State (Vector Word n))
    (m : MemoryState) (hfit : Fits m out (512*n))
    (hwrap : out.offset.toNat + 64*n ≤ 2^64) (i : Fin 16) (lane : Fin n) :
    readWord? (out.withOffset (BitVec.ofNat 64 (4*n*i.val+4*lane.val))) 32
      (outputMem out v 16 m) = some ((v i)[lane]) := by
  have hrow := outputRow_offset out hwrap i
  have hmul := Nat.mul_le_mul_left n (show i.val+1 ≤ 16 from i.isLt)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  have hl := lane.isLt
  have hb : out.offset.toNat + (4*n*i.val+4*lane.val) < 2^64 := by
    simp only [Nat.mul_assoc]
    omega
  have hword := offsetInBits_withOffset_nat out _ hb
  have hrowfit : Fits (outputMem out v 16 m)
      (out.withOffset (BitVec.ofNat 64 (4*n*i.val))) (32*n) := by
    apply fits_outputMem out v 16
    obtain ⟨b, hb, hlen⟩ := hfit
    refine ⟨b, hb, ?_⟩
    rw [hrow]
    have hmul := Nat.mul_le_mul_left (32*n) (show i.val+1 ≤ 16 from i.isLt)
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    omega
  have hoff : (out.withOffset (BitVec.ofNat 64 (4*n*i.val+4*lane.val))).offsetInBits =
      (out.withOffset (BitVec.ofNat 64 (4*n*i.val))).offsetInBits + lane.val*32 := by
    rw [hword, hrow]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hr := readWord?_extract (packBits (v i)) hrowfit
    (outputMem_read_row out v m hfit hwrap 16 (by omega) i i.isLt)
    (q := out.withOffset (BitVec.ofNat 64 (4*n*i.val+4*lane.val))) rfl hoff
    (show lane.val*32+32 ≤ 32*n by omega)
  rw [extract_packBits] at hr
  exact hr

end AgaveLatticeHash.MLIR
