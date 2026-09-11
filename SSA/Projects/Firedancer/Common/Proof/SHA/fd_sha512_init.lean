/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_sha512_init
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_sha512_init` conforms

A straight walk: twenty constants, eight gep-and-store pairs, one gep and a
`memset`, the return. `state[0]` is a one-index gep and `state[1..7]` are
`SLLVMOp.gep2`s; both normalise to `sha.withOffset (128 + 8k)` by unfolding
the pointer arithmetic. The states are named as they are produced, so each
store's operands never spell out the ones before it.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Name a subterm without reverting the goal. -/
private theorem name_of {α : Sort u} (a : α) {P : Prop} (k : ∀ x, x = a → P) : P := k a rfl

/-- A store at an offset into `p`'s block misses every other block. -/
private theorem live?_splice_withOffset_ne {m : MemoryState} {p : Pointer} {k : BitVec 64}
    {w : Nat} {x : BitVec w} {b : BlockId} (h : p.id ≠ b) :
    (m.splice (p.withOffset k) x).live? b = m.live? b :=
  live?_splice_ne h

set_option maxHeartbeats 1000000 in
theorem fd_sha512_init_conforms (sha : Pointer) (s : GlobalState) (hs : s.WF)
    (hsha : IsSha512Ptr s.mem sha) : fd_sha512_init_spec sha s := by
  simp only [fd_sha512_init_spec, Cfg.denote]
  refine run_runFunction' _ ?_
  denote_step_reduce v 19 [LLVM.const?] fold
  subst hv0 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv18 hv19
  -- `%20`: `sha->state[0]`
  denote_step_all v 20
  denote_eval v 20 20
  have e20 : v20 = .value (sha.withOffset 128) := by
    simp [hv20, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, simp_sllvm]
  subst e20; clear hv20
  have hf0 : Fits s.mem (sha.withOffset 128) 64 :=
    Fits.mono (remainingFits s.mem sha hsha 128 (by decide)) (by decide)
  refine name_of ({ s with mem := s.mem.splice (sha.withOffset 128) (7640891576956012808#64) } :
    GlobalState) fun u0 hu0 => ?_
  peel_store 7640891576956012808#64, sha.withOffset 128, hf0, s as u0 := hu0
  have hsha0 : Fits u0.mem sha (256 * 8) := by rw [hu0]; exact fits_splice hsha
  -- `%21`: `sha->state[1]`
  denote_step_all v 21
  denote_eval v 21 21
  have e21 : v21 = .value (sha.withOffset 136) := by
    simp [hv21, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e21; clear hv21
  have hf1 : Fits u0.mem (sha.withOffset 136) 64 :=
    Fits.mono (remainingFits u0.mem sha hsha0 136 (by decide)) (by decide)
  refine name_of ({ u0 with mem := u0.mem.splice (sha.withOffset 136) (13503953896175478587#64) } :
    GlobalState) fun u1 hu1 => ?_
  peel_store 13503953896175478587#64, sha.withOffset 136, hf1, u0 as u1 := hu1
  have hsha1 : Fits u1.mem sha (256 * 8) := by rw [hu1]; exact fits_splice hsha0
  -- `%22`: `sha->state[2]`
  denote_step_all v 22
  denote_eval v 22 22
  have e22 : v22 = .value (sha.withOffset 144) := by
    simp [hv22, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e22; clear hv22
  have hf2 : Fits u1.mem (sha.withOffset 144) 64 :=
    Fits.mono (remainingFits u1.mem sha hsha1 144 (by decide)) (by decide)
  refine name_of ({ u1 with mem := u1.mem.splice (sha.withOffset 144) (4354685564936845355#64) } :
    GlobalState) fun u2 hu2 => ?_
  peel_store 4354685564936845355#64, sha.withOffset 144, hf2, u1 as u2 := hu2
  have hsha2 : Fits u2.mem sha (256 * 8) := by rw [hu2]; exact fits_splice hsha1
  -- `%23`: `sha->state[3]`
  denote_step_all v 23
  denote_eval v 23 23
  have e23 : v23 = .value (sha.withOffset 152) := by
    simp [hv23, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e23; clear hv23
  have hf3 : Fits u2.mem (sha.withOffset 152) 64 :=
    Fits.mono (remainingFits u2.mem sha hsha2 152 (by decide)) (by decide)
  refine name_of ({ u2 with mem := u2.mem.splice (sha.withOffset 152) (11912009170470909681#64) } :
    GlobalState) fun u3 hu3 => ?_
  peel_store 11912009170470909681#64, sha.withOffset 152, hf3, u2 as u3 := hu3
  have hsha3 : Fits u3.mem sha (256 * 8) := by rw [hu3]; exact fits_splice hsha2
  -- `%24`: `sha->state[4]`
  denote_step_all v 24
  denote_eval v 24 24
  have e24 : v24 = .value (sha.withOffset 160) := by
    simp [hv24, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e24; clear hv24
  have hf4 : Fits u3.mem (sha.withOffset 160) 64 :=
    Fits.mono (remainingFits u3.mem sha hsha3 160 (by decide)) (by decide)
  refine name_of ({ u3 with mem := u3.mem.splice (sha.withOffset 160) (5840696475078001361#64) } :
    GlobalState) fun u4 hu4 => ?_
  peel_store 5840696475078001361#64, sha.withOffset 160, hf4, u3 as u4 := hu4
  have hsha4 : Fits u4.mem sha (256 * 8) := by rw [hu4]; exact fits_splice hsha3
  -- `%25`: `sha->state[5]`
  denote_step_all v 25
  denote_eval v 25 25
  have e25 : v25 = .value (sha.withOffset 168) := by
    simp [hv25, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e25; clear hv25
  have hf5 : Fits u4.mem (sha.withOffset 168) 64 :=
    Fits.mono (remainingFits u4.mem sha hsha4 168 (by decide)) (by decide)
  refine name_of ({ u4 with mem := u4.mem.splice (sha.withOffset 168) (11170449401992604703#64) } :
    GlobalState) fun u5 hu5 => ?_
  peel_store 11170449401992604703#64, sha.withOffset 168, hf5, u4 as u5 := hu5
  have hsha5 : Fits u5.mem sha (256 * 8) := by rw [hu5]; exact fits_splice hsha4
  -- `%26`: `sha->state[6]`
  denote_step_all v 26
  denote_eval v 26 26
  have e26 : v26 = .value (sha.withOffset 176) := by
    simp [hv26, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e26; clear hv26
  have hf6 : Fits u5.mem (sha.withOffset 176) 64 :=
    Fits.mono (remainingFits u5.mem sha hsha5 176 (by decide)) (by decide)
  refine name_of ({ u5 with mem := u5.mem.splice (sha.withOffset 176) (2270897969802886507#64) } :
    GlobalState) fun u6 hu6 => ?_
  peel_store 2270897969802886507#64, sha.withOffset 176, hf6, u5 as u6 := hu6
  have hsha6 : Fits u6.mem sha (256 * 8) := by rw [hu6]; exact fits_splice hsha5
  -- `%27`: `sha->state[7]`
  denote_step_all v 27
  denote_eval v 27 27
  have e27 : v27 = .value (sha.withOffset 184) := by
    simp [hv27, gep2, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add,
      LLVM.mul, LLVM.const?, LLVM.add?, LLVM.mul?, BitVec.add_assoc, simp_sllvm]
  subst e27; clear hv27
  have hf7 : Fits u6.mem (sha.withOffset 184) 64 :=
    Fits.mono (remainingFits u6.mem sha hsha6 184 (by decide)) (by decide)
  refine name_of ({ u6 with mem := u6.mem.splice (sha.withOffset 184) (6620516959819538809#64) } :
    GlobalState) fun u7 hu7 => ?_
  peel_store 6620516959819538809#64, sha.withOffset 184, hf7, u6 as u7 := hu7
  have hsha7 : Fits u7.mem sha (256 * 8) := by rw [hu7]; exact fits_splice hsha6
  -- `%28`: `&sha->buf_used`, then zero the three counters
  denote_step_all v 28
  denote_eval v 28 28
  have e28 : v28 = .value (sha.withOffset 200) := by
    simp [hv28, gep, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?, simp_sllvm]
  subst e28; clear hv28
  have hf8 : Fits u7.mem (sha.withOffset 200) (8 * 24) :=
    Fits.mono (remainingFits u7.mem sha hsha7 200 (by decide)) (by decide)
  peel_memset 0#8, 24, sha.withOffset 200, hf8, u7
  -- the return, and the frame: `sha`'s block is the only one written
  refine ⟨{ u7 with mem := u7.mem.splice (sha.withOffset 200) (BitVec.replicate 24 (0#8)) },
    ?_, ?_⟩
  · simp_return
  · have hmem : (u7.mem.splice (sha.withOffset 200) (BitVec.replicate 24 (0#8)))
        = sha512InitMem s.mem sha := by
      simp only [hu7, hu6, hu5, hu4, hu3, hu2, hu1, hu0, sha512InitMem]
      rfl
    have hshaN : sha.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hsha
    have hn : ∀ b : BlockId, b ≠ sha.id → (sha512InitMem s.mem sha).live? b = s.mem.live? b := by
      intro b hb
      have hb' : sha.id ≠ b := fun e => hb e.symm
      simp only [sha512InitMem, live?_splice_withOffset_ne hb']
    show s.popFrame (u7.mem.splice (sha.withOffset 200) (BitVec.replicate 24 (0#8))) ≈ _
    rw [hmem]
    exact popFrame_equiv_block hs hshaN (fun b _ hb => hn b hb) hn rfl

end Firedancer.Common
