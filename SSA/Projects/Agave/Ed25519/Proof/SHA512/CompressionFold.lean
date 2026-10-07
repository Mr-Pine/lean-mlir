import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec

/-! Instantiate the padding interface with the concrete 80-round compression
algorithm. Incomplete suffixes are ignored here; padding supplies whole blocks.
The append law follows from block decomposition, not from an assumed hash law. -/

namespace Agave.Ed25519.SHA512.Spec

open Agave.Ed25519.Bridge.Challenge

def completeBlocks (bytes : Bytes) : List Bytes :=
  (List.range (bytes.length / 128)).map fun i => (bytes.drop (128 * i)).take 128

theorem completeBlocks_append (xs ys : Bytes) (hx : xs.length % 128 = 0) :
    completeBlocks (xs ++ ys) = completeBlocks xs ++ completeBlocks ys := by
  have hlength : xs.length = 128 * (xs.length / 128) := by omega
  have hquot : (xs.length + ys.length) / 128 = xs.length / 128 + ys.length / 128 := by
    omega
  unfold completeBlocks
  rw [List.length_append, hquot, List.range_add, List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi' : i < xs.length / 128 := List.mem_range.mp hi
    rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
  · rw [List.map_map]
    apply List.map_congr_left
    intro i _
    change ((xs ++ ys).drop (128 * (xs.length / 128 + i))).take 128 = _
    have hoff : 128 * (xs.length / 128 + i) = xs.length + 128 * i := by omega
    rw [hoff, List.drop_append]
    simp [List.drop_of_length_le (by omega : xs.length ≤ xs.length + 128 * i)]

def run (state : BitVec 512) (bytes : Bytes) : BitVec 512 :=
  (completeBlocks bytes).foldl compressBlockBytes state

@[simp] theorem run_empty (state : BitVec 512) : run state [] = state := by
  simp [run, completeBlocks]

theorem run_append (state : BitVec 512) (xs ys : Bytes)
    (hx : xs.length % 128 = 0) :
    run state (xs ++ ys) = run (run state xs) ys := by
  simp only [run, completeBlocks_append xs ys hx, List.foldl_append]

theorem run_one_block (state : BitVec 512) (block : Bytes) (h : block.length = 128) :
    run state block = compressBlockBytes state block := by
  simp [run, completeBlocks, h, List.take_of_length_le (by omega : block.length ≤ 128)]

/-- The two-block AVX loop must feed the first result into the second block;
computing their message schedules together does not combine chaining states. -/
theorem run_two_blocks (state : BitVec 512) (first second : Bytes)
    (hfirst : first.length = 128) (hsecond : second.length = 128) :
    run state (first ++ second) =
      compressBlockBytes (compressBlockBytes state first) second := by
  rw [run_append state first second (by simp [hfirst]),
    run_one_block state first hfirst, run_one_block _ second hsecond]

/-- A two-block loop cut point followed by an arbitrary remaining suffix. -/
theorem run_pair_prefix (state : BitVec 512) (first second rest : Bytes)
    (hfirst : first.length = 128) (hsecond : second.length = 128) :
    run state ((first ++ second) ++ rest) =
      run (compressBlockBytes (compressBlockBytes state first) second) rest := by
  rw [run_append state (first ++ second) rest (by simp [hfirst, hsecond]),
    run_two_blocks state first second hfirst hsecond]

/-- Concrete implementation of the interface used by `Padding.digest`.
No SHA result or composition property is supplied as an axiom or premise. -/
def compression : Agave.Ed25519.SHA512.Compression where
  run := run
  empty := run_empty
  append := fun state xs ys hx _ => run_append state xs ys hx

end Agave.Ed25519.SHA512.Spec
