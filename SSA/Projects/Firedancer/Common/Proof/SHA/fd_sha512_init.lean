/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_sha512_init
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_sha512_init` conforms

A straight walk: ten constants, eight `gepConst`-and-store pairs, a `gepConst` and a
`memset`, the return, with `state[k]` at `sha.withOffset (128 + 8k)`. States are named
as produced, so no store spells out the ones before it.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Name a subterm without reverting the goal. -/
private theorem name_of {α : Sort u} (a : α) {P : Prop} (k : ∀ x, x = a → P) : P :=
  k a rfl

/-- A store at an offset into `p`'s block misses every other block. -/
private theorem live?_splice_withOffset_ne {m : MemoryState} {p : Pointer} {k : BitVec 64} {w : Nat}
    {x : BitVec w} {b : BlockId} (h : p.id ≠ b) :
    (m.splice (p.withOffset k) x).live? b = m.live? b :=
  live?_splice_ne h

set_option maxHeartbeats 1000000 in
theorem fd_sha512_init_conforms (sha : Pointer) (s : GlobalState) (hs : s.WF)
    (hsha : IsSha512Ptr s.mem sha) : fd_sha512_init_spec sha s := by
  simp only [fd_sha512_init_spec, Cfg.denote]
  refine run_runFunction' _ ?_
  denote_step_reduce v 9 [LLVM.const?] fold
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9
  -- `%10`: `sha->state[0]`
  denote_step_all v 10
  denote_eval v 10 10
  have e10 : v10 = .value (sha.withOffset 128) := by
    simp [hv10, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e10; clear hv10
  have hf0 : Fits s.mem (sha.withOffset 128) 64 :=
    Fits.mono (remainingFits s.mem sha hsha 128 (by decide)) (by decide)
  refine
    name_of
      ({ s with mem := s.mem.splice (sha.withOffset 128) (7640891576956012808#64) } : GlobalState)
      fun u0 hu0 => ?_
  peel_store 7640891576956012808#64, sha.withOffset 128, hf0, s as u0 := hu0
  have hsha0 : Fits u0.mem sha (256 * 8) := by
    rw [hu0]; exact fits_splice hsha
  -- `%11`: `sha->state[1]`
  denote_step_all v 11
  denote_eval v 11 11
  have e11 : v11 = .value (sha.withOffset 136) := by
    simp [hv11, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e11; clear hv11
  have hf1 : Fits u0.mem (sha.withOffset 136) 64 :=
    Fits.mono (remainingFits u0.mem sha hsha0 136 (by decide)) (by decide)
  refine
    name_of
      ({ u0 with mem := u0.mem.splice (sha.withOffset 136) (13503953896175478587#64) } :
        GlobalState)
      fun u1 hu1 => ?_
  peel_store 13503953896175478587#64, sha.withOffset 136, hf1, u0 as u1 := hu1
  have hsha1 : Fits u1.mem sha (256 * 8) := by
    rw [hu1]; exact fits_splice hsha0
  -- `%12`: `sha->state[2]`
  denote_step_all v 12
  denote_eval v 12 12
  have e12 : v12 = .value (sha.withOffset 144) := by
    simp [hv12, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e12; clear hv12
  have hf2 : Fits u1.mem (sha.withOffset 144) 64 :=
    Fits.mono (remainingFits u1.mem sha hsha1 144 (by decide)) (by decide)
  refine
    name_of
      ({ u1 with mem := u1.mem.splice (sha.withOffset 144) (4354685564936845355#64) } : GlobalState)
      fun u2 hu2 => ?_
  peel_store 4354685564936845355#64, sha.withOffset 144, hf2, u1 as u2 := hu2
  have hsha2 : Fits u2.mem sha (256 * 8) := by
    rw [hu2]; exact fits_splice hsha1
  -- `%13`: `sha->state[3]`
  denote_step_all v 13
  denote_eval v 13 13
  have e13 : v13 = .value (sha.withOffset 152) := by
    simp [hv13, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e13; clear hv13
  have hf3 : Fits u2.mem (sha.withOffset 152) 64 :=
    Fits.mono (remainingFits u2.mem sha hsha2 152 (by decide)) (by decide)
  refine
    name_of
      ({ u2 with mem := u2.mem.splice (sha.withOffset 152) (11912009170470909681#64) } :
        GlobalState)
      fun u3 hu3 => ?_
  peel_store 11912009170470909681#64, sha.withOffset 152, hf3, u2 as u3 := hu3
  have hsha3 : Fits u3.mem sha (256 * 8) := by
    rw [hu3]; exact fits_splice hsha2
  -- `%14`: `sha->state[4]`
  denote_step_all v 14
  denote_eval v 14 14
  have e14 : v14 = .value (sha.withOffset 160) := by
    simp [hv14, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e14; clear hv14
  have hf4 : Fits u3.mem (sha.withOffset 160) 64 :=
    Fits.mono (remainingFits u3.mem sha hsha3 160 (by decide)) (by decide)
  refine
    name_of
      ({ u3 with mem := u3.mem.splice (sha.withOffset 160) (5840696475078001361#64) } : GlobalState)
      fun u4 hu4 => ?_
  peel_store 5840696475078001361#64, sha.withOffset 160, hf4, u3 as u4 := hu4
  have hsha4 : Fits u4.mem sha (256 * 8) := by
    rw [hu4]; exact fits_splice hsha3
  -- `%15`: `sha->state[5]`
  denote_step_all v 15
  denote_eval v 15 15
  have e15 : v15 = .value (sha.withOffset 168) := by
    simp [hv15, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e15; clear hv15
  have hf5 : Fits u4.mem (sha.withOffset 168) 64 :=
    Fits.mono (remainingFits u4.mem sha hsha4 168 (by decide)) (by decide)
  refine
    name_of
      ({ u4 with mem := u4.mem.splice (sha.withOffset 168) (11170449401992604703#64) } :
        GlobalState)
      fun u5 hu5 => ?_
  peel_store 11170449401992604703#64, sha.withOffset 168, hf5, u4 as u5 := hu5
  have hsha5 : Fits u5.mem sha (256 * 8) := by
    rw [hu5]; exact fits_splice hsha4
  -- `%16`: `sha->state[6]`
  denote_step_all v 16
  denote_eval v 16 16
  have e16 : v16 = .value (sha.withOffset 176) := by
    simp [hv16, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e16; clear hv16
  have hf6 : Fits u5.mem (sha.withOffset 176) 64 :=
    Fits.mono (remainingFits u5.mem sha hsha5 176 (by decide)) (by decide)
  refine
    name_of
      ({ u5 with mem := u5.mem.splice (sha.withOffset 176) (2270897969802886507#64) } : GlobalState)
      fun u6 hu6 => ?_
  peel_store 2270897969802886507#64, sha.withOffset 176, hf6, u5 as u6 := hu6
  have hsha6 : Fits u6.mem sha (256 * 8) := by
    rw [hu6]; exact fits_splice hsha5
  -- `%17`: `sha->state[7]`
  denote_step_all v 17
  denote_eval v 17 17
  have e17 : v17 = .value (sha.withOffset 184) := by
    simp [hv17, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e17; clear hv17
  have hf7 : Fits u6.mem (sha.withOffset 184) 64 :=
    Fits.mono (remainingFits u6.mem sha hsha6 184 (by decide)) (by decide)
  refine
    name_of
      ({ u6 with mem := u6.mem.splice (sha.withOffset 184) (6620516959819538809#64) } : GlobalState)
      fun u7 hu7 => ?_
  peel_store 6620516959819538809#64, sha.withOffset 184, hf7, u6 as u7 := hu7
  have hsha7 : Fits u7.mem sha (256 * 8) := by
    rw [hu7]; exact fits_splice hsha6
  -- `%18`: `&sha->buf_used`, then zero the three counters
  denote_step_all v 18
  denote_eval v 18 18
  have e18 : v18 = .value (sha.withOffset 200) := by
    simp [hv18, gepConst, ptradd, Pointer.withOffset, Ctxt.Valuation.singleton, LLVM.const?,
      simp_sllvm]
  subst e18; clear hv18
  have hf8 : Fits u7.mem (sha.withOffset 200) (8 * 24) :=
    Fits.mono (remainingFits u7.mem sha hsha7 200 (by decide)) (by decide)
  peel_memset 0#8, 24, sha.withOffset 200, hf8, u7
  -- the return, and the frame: `sha`'s block is the only one written
  refine ⟨{ u7 with mem := u7.mem.splice (sha.withOffset 200) (BitVec.replicate 24 (0#8)) }, ?_, ?_⟩
  · simp_return
  · have hmem :
      (u7.mem.splice (sha.withOffset 200) (BitVec.replicate 24 (0#8))) =
        sha512InitMem s.mem sha := by
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
