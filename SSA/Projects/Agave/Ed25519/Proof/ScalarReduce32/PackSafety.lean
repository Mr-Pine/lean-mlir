import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Program
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step
import SSA.Projects.Agave.Ed25519.Proof.Encoding.WordBounds

/-! Bounds and bit-level side conditions for the exact scalar radix-52 packer.
These lemmas retain both shift flags and the disjoint-OR condition. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Encoding.RIR
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem pack_shift_unsigned (x : BitVec 64) (h : x.toNat < 2 ^ 53) :
    (x <<< 4) >>> 4 = x := by
  exact shift_unsigned_safe x 4 (2 ^ 53 - 1) (by omega) (by decide)

theorem pack_shift_signed (x : BitVec 64) (h : x.toNat < 2 ^ 53) :
    (x <<< 4).sshiftRight 4 = x := by
  exact shift_signed_safe x 4 (2 ^ 53 - 1) (by omega) (by decide)

theorem pack_mask_bound (x : BitVec 64) :
    (x &&& 4503599627370495#64).toNat < 2 ^ 53 := by
  have h := and_nat_le_right x 4503599627370495#64
  norm_num at h ⊢
  omega

theorem pack_boundary_disjoint (x y : BitVec 64) :
    (x <<< 4) &&& ((y &&& 4503599627370495#64) >>> 48) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp [BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]

end Agave.Ed25519.ScalarReduce32.Execution
