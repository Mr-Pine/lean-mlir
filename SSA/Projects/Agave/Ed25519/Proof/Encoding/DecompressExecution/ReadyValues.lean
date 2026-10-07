import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Ready
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Constants

/-! Field-word consequences of invocation-local initialized byte reads. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR
open Verifier.Execution.Dalek (ReadBytes)

/-- Exact byte initializers are sufficient even when the constant allocation
also contains unrelated data outside these 40 bytes. -/
private theorem readLimbs_of_bytes (s : GlobalState) (p : Pointer) (bytes : BitVec 320)
    (h : ReadBytes s p 40 bytes) :
    SerialFieldMul.readLimbs s p = fun i => bytes.extractLsb' (64 * i.val) 64 := by
  funext i
  have hi : 8 * i.val < 18446744073709551616 := by omega
  have hr := MemoryState.readAt_add_of_readAt (off := BitVec.ofNat 64 (8 * i.val))
    (w := 64) h.1.fits (h.1.no_wrap (k := 8 * i.val) (by omega))
    (by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]; omega) h.2
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi] at hr
  simpa only [SerialFieldMul.readLimbs,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hr

theorem Ready.curveD_read (h : Ready dg sg s) :
    SerialFieldMul.readLimbs s dg.address0 = curveDLimbs :=
  readLimbs_of_bytes s dg.address0 _root_.Agave.Ed25519.Encoding.Decompress.Execution.curveD.bytes h.curveD

theorem Ready.sqrtM1_read (h : Ready dg sg s) :
    SerialFieldMul.readLimbs s sg.address0 = sqrtM1Limbs :=
  readLimbs_of_bytes s sg.address0 _root_.Agave.Ed25519.Encoding.Decompress.Execution.sqrtM1.bytes h.sqrtM1

end Agave.Ed25519.Encoding.Decompress.Execution
