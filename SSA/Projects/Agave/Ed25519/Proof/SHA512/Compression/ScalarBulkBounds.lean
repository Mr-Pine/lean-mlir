import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkRegisters

/-! Count arithmetic and exact original scalar bb2 entry, including zero. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open ScalarFull

theorem count_shift (count : BitVec 64) (h : 128 * count.toNat < 2 ^ 63) :
    Operation.shl {nsw := true, nuw := true} (.value count) (.value 7#64) =
      .value (BitVec.ofNat 64 (128 * count.toNat)) := by
  have hn : 128 * count.toNat < 2 ^ 64 := by omega
  have hsh : count <<< (7 : Nat) = BitVec.ofNat 64 (128 * count.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  have hr : (BitVec.ofNat 64 (128 * count.toNat)) >>> (7 : Nat) = count := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
    norm_num
  have hm : (BitVec.ofNat 64 (128 * count.toNat)).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    omega
  simp only [Operation.shl, LeanMLIR.RIR.PoisonOr.value_bind]
  norm_num only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ge_iff_le, Bool.true_eq, false_and, ite_false, true_and]
  rw [hsh, hr, BitVec.sshiftRight_eq_of_msb_false hm, hr]
  simp

theorem count_gep (n : Nat) (h : n < 2 ^ 63) :
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 n)) = .value (n : Int) := by
  have hn : n < 2 ^ 64 := by omega
  have hnat : (BitVec.ofNat 64 n).toNat = n := by
    exact Nat.mod_eq_of_lt hn
  have ht : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb, hnat]
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hnat]
    omega
  have hs : Operation.GepSignedRange ((BitVec.ofNat 64 n).toInt) := by
    rw [ht]
    unfold Operation.GepSignedRange
    constructor <;> omega
  have hu : (BitVec.ofInt 64 (BitVec.ofNat 64 n).toInt).toNat * 1 < 2 ^ 64 := by
    rw [BitVec.ofInt_toInt, hnat, Nat.mul_one]
    exact hn
  simpa only [ht, Nat.cast_one, Int.mul_one] using Operation.gepInboundsIndex_eq 1
    (BitVec.ofNat 64 n) hs (by simpa using hs)
    (by rw [hnat]; exact hn) hu

def boundsEnv (E : Env program.Γ) (data : Pointer) (count : BitVec 64) : Env program.Γ :=
  E[%175 := .value (BitVec.ofNat 64 (128 * count.toNat)),
    %176 := .value (data.add (BitVec.ofNat 64 (128 * count.toNat))),
    %177 := .value (BitVec.ofBool (count == 0#64))]

theorem bounds_before (E : Env program.Γ) (data : Pointer) (count : BitVec 64) :
    Before 175 E (boundsEnv E data count) := by
  unfold boundsEnv
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem bounds_step (E : Env program.Γ) (state : GlobalState)
    (data : Pointer) (count : BitVec 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hdata : E.read (%arg1) = .value data)
    (hcount : E.read (%arg2) = .value count)
    (hseven : E.read (%1) = .value 7#64)
    (hzero : E.read (%2) = .value 0#64) :
    program.bb2.run program.blockParams E state =
      .value ((boundsEnv E data count, .inr (if count = 0#64 then 7 else 3)), state) := by
  have hext : 128 * count.toNat < 2 ^ 63 := by have := hd.offset_lt; omega
  have hshift := count_shift count hext
  have hidx := count_gep (128 * count.toNat) hext
  have hg := hd.gep (k := 128 * count.toNat) (by omega)
  change Operation.gepInboundsLive state.mem (.value data) [.value ((128 * count.toNat : Nat) : Int)] =
    .value (data.add (BitVec.ofNat 64 (128 * count.toNat))) at hg
  change E.args 1 = .value data at hdata
  change E.args 2 = .value count at hcount
  have hg' : Operation.gepInboundsLive state.mem (.value data) [.value (128 * (count.toNat : Int))] =
    .value (data.add (BitVec.ofNat 64 (128 * count.toNat))) := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hg
  by_cases hz : count = 0#64
  · subst count
    simp at hg hshift hidx
    simp [BasicBlock.run, program.bb2, List.foldlM_cons, List.foldlM_nil,
      Instr.run, Exit.run, Jump.run, boundsEnv, hdata, hcount, hseven, hzero,
      hshift, Operation.icmp, GepIndex.inboundsOffset, hg, hidx,
      BinOp.compute, mlir_env, Regs.read_nil, Env.writeMany_nil,
      EffectM.bind_eq, EffectM.pure_eq, mlir_effect]
  · have hbeq : (count == 0#64) = false := by exact beq_eq_false_iff_ne.mpr hz

    simp [BasicBlock.run, program.bb2, List.foldlM_cons, List.foldlM_nil,
      Instr.run, Exit.run, Jump.run, boundsEnv, hdata, hcount, hseven, hzero,
      hshift, hz, hbeq, Operation.icmp, GepIndex.inboundsOffset, hg', hidx,
      BinOp.compute, mlir_env, Regs.read_nil, Env.writeMany_nil,
      EffectM.bind_eq, EffectM.pure_eq, mlir_effect]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
