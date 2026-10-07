import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Control
import SSA.Projects.Agave.Ed25519.Spec.Field
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Step

/-! Exact execution of the final packing/storing block of the imported AVX2
kernel. The flagged shifts and additions are safe for arbitrary u32 lanes;
only the live destination range is needed by this block. -/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR Reduce64.Execution
open Avx2SquareNegateD

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 16000000

attribute [local implicit_reducible] Ty.width
attribute [-mlir_operation] Operation.shl Operation.add

/-- Joining the adjacent radix-26/25 limbs into one ordinary u64 limb. -/
def unpackPair (lo hi : BitVec 32) : BitVec 64 :=
  (hi.setWidth 64 <<< 26) + lo.setWidth 64

theorem unpack_shift_toNat (x : BitVec 32) :
    (x.setWidth 64 <<< 26).toNat = x.toNat * 67108864 := by
  have hx := x.isLt
  simp only [BitVec.toNat_shiftLeft, wide_toNat, Nat.shiftLeft_eq]
  norm_num at hx ⊢
  omega

theorem unpack_shift_value (x : BitVec 32) :
    Operation.shl {nsw := true, nuw := true}
      (.value (x.setWidth 64)) (.value 26#64) =
      .value (x.setWidth 64 <<< 26) := by
  have hx := x.isLt
  have hu : (x.setWidth 64 <<< 26) >>> 26 = x.setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, unpack_shift_toNat, wide_toNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
  have hm : (x.setWidth 64 <<< 26).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, unpack_shift_toNat]
    norm_num at hx ⊢
    omega
  have hs : (x.setWidth 64 <<< 26).sshiftRight 26 = x.setWidth 64 := by
    rw [BitVec.sshiftRight_eq_of_msb_false hm]
    exact hu
  simp [Operation.shl, hu, hs]

theorem unpack_add_value (lo hi : BitVec 32) :
    Operation.add {nsw := true, nuw := true}
      (.value (hi.setWidth 64 <<< 26)) (.value (lo.setWidth 64)) =
      .value (unpackPair lo hi) := by
  have hlo := lo.isLt
  have hhi := hi.isLt
  have hli : (lo.setWidth 64).toInt = (lo.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt, wide_toNat]
    rw [wide_toNat]
    norm_num at hlo ⊢
    omega
  have hhi' : (hi.setWidth 64 <<< 26).toInt = (hi.toNat * 67108864 : Nat) := by
    rw [BitVec.toInt_eq_toNat_of_lt, unpack_shift_toNat]
    rw [unpack_shift_toNat]
    norm_num at hhi ⊢
    omega
  have hu : (hi.setWidth 64 <<< 26).uaddOverflow (lo.setWidth 64) = false := by
    simp only [BitVec.uaddOverflow, unpack_shift_toNat, wide_toNat,
      decide_eq_false_iff_not]
    norm_num at hlo hhi ⊢
    omega
  have hs : (hi.setWidth 64 <<< 26).saddOverflow (lo.setWidth 64) = false := by
    simp only [BitVec.saddOverflow, hli, hhi', Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    norm_num at hlo hhi ⊢
    omega
  simp [Operation.add, hs, hu, unpackPair]

/-- The stored u64 is the exact integer radix combination, without wrapping. -/
theorem unpackPair_toNat (lo hi : BitVec 32) :
    (unpackPair lo hi).toNat = lo.toNat + 2^26 * hi.toNat := by
  have hlo := lo.isLt
  have hhi := hi.isLt
  simp only [unpackPair, BitVec.toNat_add, unpack_shift_toNat, wide_toNat]
  norm_num at hlo hhi ⊢
  omega

abbrev UnpackBlocks := Fin 5 → Vector (BitVec 32) 8

def unpackSerial (v : UnpackBlocks) (coordinate : Fin 4) : Field.Serial :=
  fun limb => unpackPair (v limb)[Field.evenLane coordinate]
    (v limb)[Field.oddLane coordinate]

theorem unpackSerial_eq_split (v : UnpackBlocks) (coordinate : Fin 4) :
    unpackSerial v coordinate = Field.split (fun limb lane => (v limb)[lane]) coordinate := by
  funext limb
  apply BitVec.eq_of_toNat_eq
  simp [unpackSerial, unpackPair_toNat, Field.split_toNat, Field.pair,
    Field.lo, Field.hi, Nat.mul_comm]

/-- The exact word conversion preserves the complete integer field value. -/
theorem unpackSerial_value (v : UnpackBlocks) (coordinate : Fin 4) :
    Field.serialValue (unpackSerial v coordinate) =
      Field.packedValue (fun limb lane => (v limb)[lane]) coordinate := by
  rw [unpackSerial_eq_split]
  exact Field.split_value _ _

def unpackInput (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) (v : UnpackBlocks) :
    ⟪avx2Kernel.Γ⟫ :=
  ({E with args := Function.update E.args 0 (.value r)} : ⟪avx2Kernel.Γ⟫)[%3 := .value 32#64, %5 := .value 6#64,
    %10 := .value 1#64, %13 := .value 5#64, %20 := .value 64#64,
    %26 := Vector.replicate 8 .poison,
    %225 := .value 7#64, %226 := .value 4#64, %227 := .value 3#64,
    %228 := .value 26#64, %229 := Vector.replicate 2 (.value 26#64),
    %230 := .value 16#64, %231 := Vector.replicate 4 (.value 26#64),
    %232 := .value 72#64, %233 := .value 2#64, %234 := .value 104#64,
    %235 := .value 136#64, %236 := .value 152#64,
    %808 := (v 0).map PoisonOr.value, %807 := (v 1).map PoisonOr.value,
    %806 := (v 2).map PoisonOr.value, %805 := (v 3).map PoisonOr.value,
    %809 := (v 4).map PoisonOr.value]

/-- The exact eight stores, in their emitted order. -/
def unpackStore (m : MemoryState) (r : Pointer) (v : UnpackBlocks) : MemoryState :=
  let m := m.storeAt r (BitVec.packLanes #v[unpackPair (v 0)[0] (v 0)[2], unpackPair (v 1)[0] (v 1)[2]])
  let m := m.storeAt (r.add 16) (BitVec.packLanes #v[unpackPair (v 2)[0] (v 2)[2], unpackPair (v 3)[0] (v 3)[2]])
  let m := m.storeAt (r.add 32) (BitVec.packLanes #v[unpackPair (v 4)[0] (v 4)[2], unpackPair (v 0)[1] (v 0)[3], unpackPair (v 1)[1] (v 1)[3], unpackPair (v 2)[1] (v 2)[3]])
  let m := m.storeAt (r.add 64) (unpackPair (v 3)[1] (v 3)[3])
  let m := m.storeAt (r.add 72) (BitVec.packLanes #v[unpackPair (v 4)[1] (v 4)[3], unpackPair (v 0)[4] (v 0)[6], unpackPair (v 1)[4] (v 1)[6], unpackPair (v 2)[4] (v 2)[6]])
  let m := m.storeAt (r.add 104) (BitVec.packLanes #v[unpackPair (v 3)[4] (v 3)[6], unpackPair (v 4)[4] (v 4)[6], unpackPair (v 0)[5] (v 0)[7], unpackPair (v 1)[5] (v 1)[7]])
  let m := m.storeAt (r.add 136) (BitVec.packLanes #v[unpackPair (v 2)[5] (v 2)[7], unpackPair (v 3)[5] (v 3)[7]])
  let m := m.storeAt (r.add 152) (unpackPair (v 4)[5] (v 4)[7])
  m

theorem unpack_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (r : Pointer) (v : UnpackBlocks) (s : GlobalState)
    (hr : SmallRange s.mem r 160) :
    (avx2Kernel p g).runFrom (unpackInput E r v) 34 s =
      .value (.nil, {s with mem := unpackStore s.mem r v}) := by
  have hfit0 := hr.fits_add (k := 0) (count := 16) (by decide)
  have hfit16 := hr.fits_add (k := 16) (count := 16) (by decide)
  have hfit32 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hfit64 := hr.fits_add (k := 64) (count := 8) (by decide)
  have hfit72 := hr.fits_add (k := 72) (count := 32) (by decide)
  have hfit104 := hr.fits_add (k := 104) (count := 32) (by decide)
  have hfit136 := hr.fits_add (k := 136) (count := 16) (by decide)
  have hfit152 := hr.fits_add (k := 152) (count := 8) (by decide)
  simp only [Pointer.add_zero] at hfit0
  extract_state
  generalize hE : unpackInput E r v = E'
  symm at hE
  have hEargs : E'.args = Function.update E.args 0 (.value r) := by rw [hE]; rfl
  unfold unpackInput at hE
  generalize ({E with args := Function.update E.args 0 (.value r)} : ⟪avx2Kernel.Γ⟫) = E₀ at hE
  rw [Func.runFrom_eq,
    show (avx2Kernel p g).blocks 34 = avx2Kernel.bb34 from rfl, BasicBlock.run_eq]
  simp only [EffectM.bind_eq, EffectM.map_eq, bind_assoc, bind_map_left]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_store
  have hgep := hr.gep (k := 16) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_store
  have hgep := hr.gep (k := 32) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_store
  have hgep := hr.gep (k := 64) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_store
  have hgep := hr.gep (k := 72) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_store
  have hgep := hr.gep (k := 104) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_store
  have hgep := hr.gep (k := 136) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_store
  have hgep := hr.gep (k := 152) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  simp only [hS] at hgep
  step_reduce_gep [hgep, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange]
  clear hgep
  step_store
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  step_pure [expandOfFn, avx2_execution_simp, unpack_shift_value, unpack_add_value]
  finish_block
  rw [hS]
  subst_vars
  simp [unpackStore, unpackPair, Pointer.add, expandOfFn, avx2_execution_simp,
    zipWith_eq_ofFn]

end Agave.Ed25519.DoubleBase.ExecutionAvx2
