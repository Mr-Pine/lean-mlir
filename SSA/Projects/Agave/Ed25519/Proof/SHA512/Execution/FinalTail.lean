import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Cutpoints
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Zeroization
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.DigestZeroization

/-! Compose all imported post-reduction stores/fences/lifetime markers. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def clearedScratch (s : GlobalState) (scratch : Fin 64 → Pointer) : GlobalState :=
  {s with mem := zeroBytes s.mem (List.ofFn scratch)}

def clearDigestChunks (s : GlobalState) (dst : Pointer) : Nat → GlobalState
  | 0 => s
  | n + 1 => clearChunkState (clearDigestChunks s dst n) dst (8 * n)

def zeroizedState (s : GlobalState) (digest : Pointer) (scratch : Fin 64 → Pointer) : GlobalState :=
  clearDigestChunks (clearedScratch s scratch) digest 8

def zeroizedEnv (E : Env program.Γ) (digest : Pointer) : Env program.Γ :=
  clearChunkEnv7 (clearChunkEnv6 (clearChunkEnv5 (clearChunkEnv4
    (clearChunkEnv3 (clearChunkEnv2 (clearChunkEnv1 (clearChunkEnv0 E digest) digest)
      digest) digest) digest) digest) digest) digest

theorem clearDigestChunks_live (s : GlobalState) (dst q : Pointer) (n count : Nat)
    (h : SmallRange s.mem q count) : SmallRange (clearDigestChunks s dst n).mem q count := by
  induction n with
  | zero => exact h
  | succ n ih => exact clearBytes_live _ _ _ _ _ _ ih

theorem clearDigestChunks_frame (s : GlobalState) (dst : Pointer) (n mark : Nat)
    (hinternal : mark ≤ dst.id.id) :
    (clearDigestChunks s dst n).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (clearBytes_frame _ _ _ _ _ hinternal).trans ih

theorem zeroizedState_frame (s : GlobalState) (digest : Pointer) (scratch : Fin 64 → Pointer)
    (mark : Nat) (hd : mark ≤ digest.id.id) (hs : ∀ i, mark ≤ (scratch i).id.id) :
    (zeroizedState s digest scratch).mem.eraseFrom mark = s.mem.eraseFrom mark := by
  unfold zeroizedState
  rw [clearDigestChunks_frame _ _ _ _ hd]
  apply zeroBytes_frame
  intro ptr hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact hs i

theorem zeroBytes_wf (s : GlobalState) (targets : List Pointer) (h : s.WF) :
    {s with mem := zeroBytes s.mem targets}.WF := by
  induction targets generalizing s with
  | nil => exact h
  | cons dst rest ih => exact ih _ h.storeAt

theorem clearBytes_wf (s : GlobalState) (dst : Pointer) (start n : Nat) (h : s.WF) :
    {s with mem := clearBytes s.mem dst start n}.WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt

theorem clearDigestChunks_wf (s : GlobalState) (dst : Pointer) (n : Nat) (h : s.WF) :
    (clearDigestChunks s dst n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact clearBytes_wf _ _ _ _ ih

theorem zeroizedState_wf (s : GlobalState) (digest : Pointer) (scratch : Fin 64 → Pointer)
    (h : s.WF) : (zeroizedState s digest scratch).WF :=
  clearDigestChunks_wf _ _ _ (zeroBytes_wf _ _ h)

@[simp] theorem clearDigestChunks_counter (s : GlobalState) (dst : Pointer) (n : Nat) :
    (clearDigestChunks s dst n).alloc = s.alloc := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (clearDigestChunks s dst n).alloc = s.alloc
    exact ih

@[simp] theorem zeroizedState_counter (s : GlobalState) (digest : Pointer)
    (scratch : Fin 64 → Pointer) :
    (zeroizedState s digest scratch).alloc = s.alloc := by
  unfold zeroizedState
  rw [clearDigestChunks_counter]
  rfl

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Actual post-reduction instruction execution, including all 128 byte
stores and all 65 sequential fences. No primitive or arithmetic premise. -/
theorem final_tail (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (digest : Pointer) (scratch : Fin 64 → Pointer)
    (hzero : E.read (%8) = .value 0#8)
    (hdigest : E.read (%85) = .value digest)
    (hptr1 : E.read (%191) = .value (digest.add 8#64))
    (hptr2 : E.read (%192) = .value (digest.add 16#64))
    (hptr3 : E.read (%193) = .value (digest.add 24#64))
    (hptr4 : E.read (%194) = .value (digest.add 32#64))
    (hptr5 : E.read (%195) = .value (digest.add 40#64))
    (hptr6 : E.read (%196) = .value (digest.add 48#64))
    (hptr7 : E.read (%197) = .value (digest.add 56#64))
    (hscratch : ∀ i, E.read (scratchReg i) = .value (scratch i))
    (hd : SmallRange s.mem digest 64) (hs : ∀ i, SmallRange s.mem (scratch i) 1) :
    (program.bb3 p).runBodyFrom E 43 s =
      .value (zeroizedEnv E digest, zeroizedState s digest scratch) := by
  have hsrun := scratch_zeroization p E s scratch hzero hscratch hs
  rw [runBodyFrom_slice (program.bb3 p) E E s (clearedScratch s scratch) 43 64 hsrun]
  have hdlive : SmallRange (clearedScratch s scratch).mem digest 64 := zeroBytes_live _ hd
  let S0 := clearedScratch s scratch
  let E0 := E
  let S1 := clearChunkState S0 digest 0
  let E1 := clearChunkEnv0 E0 digest
  have hd0 : SmallRange S0.mem digest 64 := hdlive
  have hc0 := digest_zero_chunk0 p E0 S0 digest hd0
    (by simpa [E0, mlir_env] using hdigest)
    (by simpa [E0, mlir_env] using hdigest)
    (by simpa [E0, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E0 E1 S0 S1 107 24 hc0]
  let S2 := clearChunkState S1 digest 8
  let E2 := clearChunkEnv1 E1 digest
  have hd1 : SmallRange S1.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd0
  have hc1 := digest_zero_chunk1 p E1 S1 digest hd1
    (by simpa [E0, E1, clearChunkEnv0, mlir_env] using hdigest)
    (by simpa [E0, E1, clearChunkEnv0, mlir_env] using hptr1)
    (by simpa [E0, E1, clearChunkEnv0, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E1 E2 S1 S2 131 23 hc1]
  let S3 := clearChunkState S2 digest 16
  let E3 := clearChunkEnv2 E2 digest
  have hd2 : SmallRange S2.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd1
  have hc2 := digest_zero_chunk2 p E2 S2 digest hd2
    (by simpa [E0, E1, E2, clearChunkEnv0, clearChunkEnv1, mlir_env] using hdigest)
    (by simpa [E0, E1, E2, clearChunkEnv0, clearChunkEnv1, mlir_env] using hptr2)
    (by simpa [E0, E1, E2, clearChunkEnv0, clearChunkEnv1, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E2 E3 S2 S3 154 23 hc2]
  let S4 := clearChunkState S3 digest 24
  let E4 := clearChunkEnv3 E3 digest
  have hd3 : SmallRange S3.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd2
  have hc3 := digest_zero_chunk3 p E3 S3 digest hd3
    (by simpa [E0, E1, E2, E3, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, mlir_env] using hdigest)
    (by simpa [E0, E1, E2, E3, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, mlir_env] using hptr3)
    (by simpa [E0, E1, E2, E3, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E3 E4 S3 S4 177 23 hc3]
  let S5 := clearChunkState S4 digest 32
  let E5 := clearChunkEnv4 E4 digest
  have hd4 : SmallRange S4.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd3
  have hc4 := digest_zero_chunk4 p E4 S4 digest hd4
    (by simpa [E0, E1, E2, E3, E4, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, mlir_env] using hdigest)
    (by simpa [E0, E1, E2, E3, E4, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, mlir_env] using hptr4)
    (by simpa [E0, E1, E2, E3, E4, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E4 E5 S4 S5 200 23 hc4]
  let S6 := clearChunkState S5 digest 40
  let E6 := clearChunkEnv5 E5 digest
  have hd5 : SmallRange S5.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd4
  have hc5 := digest_zero_chunk5 p E5 S5 digest hd5
    (by simpa [E0, E1, E2, E3, E4, E5, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, mlir_env] using hdigest)
    (by simpa [E0, E1, E2, E3, E4, E5, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, mlir_env] using hptr5)
    (by simpa [E0, E1, E2, E3, E4, E5, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E5 E6 S5 S6 223 23 hc5]
  let S7 := clearChunkState S6 digest 48
  let E7 := clearChunkEnv6 E6 digest
  have hd6 : SmallRange S6.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd5
  have hc6 := digest_zero_chunk6 p E6 S6 digest hd6
    (by simpa [E0, E1, E2, E3, E4, E5, E6, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, clearChunkEnv5, mlir_env] using hdigest)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, clearChunkEnv5, mlir_env] using hptr6)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, clearChunkEnv5, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E6 E7 S6 S7 246 23 hc6]
  let S8 := clearChunkState S7 digest 56
  let E8 := clearChunkEnv7 E7 digest
  have hd7 : SmallRange S7.mem digest 64 := clearBytes_live _ _ _ _ _ _ hd6
  have hc7 := digest_zero_chunk7 p E7 S7 digest hd7
    (by simpa [E0, E1, E2, E3, E4, E5, E6, E7, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, clearChunkEnv5, clearChunkEnv6, mlir_env] using hdigest)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, E7, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, clearChunkEnv5, clearChunkEnv6, mlir_env] using hptr7)
    (by simpa [E0, E1, E2, E3, E4, E5, E6, E7, clearChunkEnv0, clearChunkEnv1, clearChunkEnv2, clearChunkEnv3, clearChunkEnv4, clearChunkEnv5, clearChunkEnv6, mlir_env] using hzero)
  rw [runBodyFrom_slice (program.bb3 p) E7 E8 S7 S8 269 23 hc7]
  exact final_lifetimes p E8 S8

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
