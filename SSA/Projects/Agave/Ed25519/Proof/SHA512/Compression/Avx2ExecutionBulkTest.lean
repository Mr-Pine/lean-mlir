import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkZero
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairFrame

/-! The live bulk-loop branch after the optional odd-block prologue. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def bulkTestEnv (E : Env program.Γ) (buffer : Pointer) (pairs : Nat) : Env program.Γ :=
  E[%87 := .value (buffer.add 128#64), %88 := .value (BitVec.ofNat 64 (2*pairs)),
    %89 := .value (BitVec.ofNat 64 pairs), %90 := .value (BitVec.ofNat 64 pairs),
    %91 := .value 0#1]

@[simp] theorem bulk_params8 : program.blockParams 8 = .nil := rfl

theorem bulk_test_pairs (E : Env program.Γ) (mem : GlobalState) (buffer : Pointer)
    (consumed pairs : Nat) (hp : 0 < pairs) (hb : consumed + 2*pairs < 2^56)
    (h : BulkTestReady E buffer (BitVec.ofNat 64 (consumed+2*pairs))
      (BitVec.ofNat 64 consumed)) (hlive : SmallRange mem.mem buffer 640) :
    program.bb1.run program.blockParams E mem =
      .value ((bulkTestEnv E buffer pairs, .inr 8), returnState mem buffer) := by
  have hfit : Fits mem.mem (buffer.add 128#64) 4096 :=
    hlive.fits_add (k := 128) (count := 512) (by decide)
  have hgep := hlive.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  have hu := bulk_usub (consumed+2*pairs) consumed (by omega) (by omega)
  have hdiff : consumed + 2*pairs - consumed = 2*pairs := by omega
  rw [hdiff] at hu
  have hh := bulk_half pairs (by omega)
  have hs := bulk_pair_sub pairs (by omega)
  have hn : BitVec.ofNat 64 pairs ≠ 0#64 := by
    intro heq
    have he := congrArg BitVec.toNat heq
    have hbound : pairs < 2^64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at he
    change pairs = 0 at he
    omega
  have hnBool : (BitVec.ofNat 64 pairs == 0#64) = false := beq_eq_false_iff_ne.mpr hn
  rcases h with ⟨hc, hi, hbuf, ho, hz, hl, h1, h0⟩
  change E.args 2 = .value (BitVec.ofNat 64 (consumed+2*pairs)) at hc
  simp [BasicBlock.run, program.bb1, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.memset, bulkTestEnv, returnState,
    hc, hi, hbuf, hz, hl, h1, h0, hfit, hgep, hu, hh, hs,
    Operation.icmp, hnBool, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem bulkTestEnv_frame (E : Env program.Γ) (buffer : Pointer) (pairs : Nat) :
    RegFrame 87 91 E (bulkTestEnv E buffer pairs) := by
  unfold bulkTestEnv
  repeat' (apply RegFrame.write <;> try decide)
  exact RegFrame.refl _ _ E

end Agave.Ed25519.SHA512.Execution.Avx2
