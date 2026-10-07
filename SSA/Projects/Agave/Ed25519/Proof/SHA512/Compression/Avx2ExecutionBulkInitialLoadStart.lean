import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialSetup
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

/-! The exact array-stride address and noalias prefix of bb9. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem bulk_initial_index (n : Nat) (h : 128*n < 2^63) :
    Operation.gepInboundsIndex 128 (.value (BitVec.ofNat 64 n)) =
      .value ((128*n : Nat) : Int) := by
  have hn : n < 2^64 := by omega
  have hnat : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt hn
  have ht : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_msb, hnat]
    rw [BitVec.msb_eq_false_iff_two_mul_lt, hnat]
    omega
  have hs : Operation.GepSignedRange ((BitVec.ofNat 64 n).toInt) := by
    rw [ht]
    unfold Operation.GepSignedRange
    constructor <;> omega
  have hm : Operation.GepSignedRange ((BitVec.ofNat 64 n).toInt * (128 : Nat)) := by
    rw [ht]
    unfold Operation.GepSignedRange
    constructor <;> omega
  have hu : (BitVec.ofInt 64 (BitVec.ofNat 64 n).toInt).toNat * 128 < 2^64 := by
    rw [BitVec.ofInt_toInt, hnat]
    omega
  simpa only [ht, Nat.cast_mul, Nat.cast_ofNat, Int.mul_comm] using
    Operation.gepInboundsIndex_eq 128 (BitVec.ofNat 64 n) hs hm
      (by rw [hnat]; omega) hu

def bulkInitialStartEnv (E : Env program.Γ) (data : Pointer) (n : Nat) : Env program.Γ :=
  E[%360 := .value (data.add (BitVec.ofNat 64 (128*n)))]

theorem bulk_initial_start_body (E : Env program.Γ) (mem : GlobalState)
    (data : Pointer) (n : Nat) (hd : SmallRange mem.mem data (128*n+256))
    (hp : E.read (%arg1) = .value data) (hn : E.read (%358) = .value (BitVec.ofNat 64 n)) :
    List.foldlM Instr.run E (program.bb9.body.take 3) mem =
      .value (bulkInitialStartEnv E data n, mem) := by
  have hb : 128*n < 2^63 := by have := hd.offset_lt; omega
  have hidx := bulk_initial_index n hb
  have hg := hd.gep (k := 128*n) (by omega)
  change Operation.gepInboundsLive mem.mem (.value data) [.value ((128*n : Nat) : Int)] =
    .value (data.add (BitVec.ofNat 64 (128*n))) at hg
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hg
  change E.args 1 = .value data at hp
  simp [program.bb9, bulkInitialStartEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, hp, hn, hidx, hg, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem bulkInitialStartEnv_frame (E : Env program.Γ) (data : Pointer) (n : Nat) :
    RegFrame 360 360 E (bulkInitialStartEnv E data n) := by
  apply RegFrame.write <;> try decide
  exact RegFrame.refl _ _ E

theorem bulk_initial_data_live (mem : MemoryState) (data : Pointer) (n : Nat)
    (hd : SmallRange mem data (128*n+256)) :
    SmallRange mem (data.add (BitVec.ofNat 64 (128*n))) 256 :=
  smallRange_add hd (by omega)

end Agave.Ed25519.SHA512.Execution.Avx2
