import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.Preparation
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMachine

/-! Physical lane refinement for the doubling preparation shuffles.
`Preparation.prepareOperation_value` handles the exact poison-aware operation
sequence. Here its five packed results are related to X,Y,Z,X+Y in the shared
logical-limb layout consumed by the actual field helpers. -/
namespace Agave.Ed25519.Avx2PointDouble

abbrev Blocks := Avx2FieldMul.Execution.Blocks

def blockCoordinates (a : Blocks) : Coordinates :=
  fun lane limb => (Avx2FieldMul.Execution.unpackBlocks a lane limb).toNat

def prepareBlocks (a : Blocks) : Blocks := fun i => prepareBlock (a i)

/-- Exact wrapping preparation, without an input bound. -/
theorem prepareBlocks_words (a : Blocks) (lane : Fin 4) (limb : Fin 10) :
    Avx2FieldMul.Execution.unpackBlocks (prepareBlocks a) lane limb =
      BitVec.ofNat 32 (prepare (blockCoordinates a) lane limb) := by
  fin_cases lane <;> fin_cases limb <;>
    simp [Avx2FieldMul.Execution.unpackBlocks, prepareBlocks, prepareBlock,
      prepare, blockCoordinates, BitVec.ofNat_add]

/-- Caller-derived bounds make the two preparation sums genuine natural
coefficient sums instead of merely congruent u32 words. -/
theorem prepare_fits_u32 {p : Coordinates} (hp : PointBound p)
    (lane : Fin 4) (limb : Fin 10) : prepare p lane limb < 2 ^ 32 := by
  have h := prepare_bounded hp lane limb
  unfold Avx2SquareNegateD.inputLimit at h
  split_ifs at h <;> norm_num at h ⊢ <;> omega

theorem prepareBlocks_coordinates (a : Blocks) (ha : PointBound (blockCoordinates a)) :
    blockCoordinates (prepareBlocks a) = prepare (blockCoordinates a) := by
  funext lane limb
  change (Avx2FieldMul.Execution.unpackBlocks (prepareBlocks a) lane limb).toNat = _
  rw [prepareBlocks_words, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (prepare_fits_u32 ha lane limb)]

end Agave.Ed25519.Avx2PointDouble
