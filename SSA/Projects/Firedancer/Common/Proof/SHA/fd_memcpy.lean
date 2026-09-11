/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_memcpy
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_memcpy` and `fd_memset` conform

One intrinsic each. `peel_memcpy` and `peel_memset` assume a *literal* length,
so these go through `run_memcpy`/`run_memset` directly: the length is the
region's own operand.

`hsrc` cannot be destructed, since the specification mentions `readWord hsrc`;
the source block is reached through `choose` instead, exactly as `peel_memcpy`
does, and `hbytes` is the bridge from that block's bytes to the `readWord` the
statement is phrased with.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A region that writes one caller block and allocates nothing leaves the entry
state with a single splice. -/
private theorem popFrame_splice_self {s : GlobalState} {o : Pointer} {w : Nat} {x : BitVec w}
    (hs : s.WF) (ho : o.id.id < s.alloc.nextFreeBlock) :
    s.popFrame (s.mem.splice o x) ≈ ({ s with mem := s.mem.splice o x } : GlobalState) :=
  (popFrame_equiv_splice hs ho (fun _ _ hb => live?_splice_ne (fun e => hb e.symm)) rfl).symm

set_option maxRecDepth 10000 in
theorem fd_memcpy_conforms (d src : Pointer) (sz : BitVec 64) (s : GlobalState) (hs : s.WF)
    (hsrc : Fits s.mem src (8 * sz.toNat)) (hdst : Fits s.mem d (8 * sz.toNat)) :
    fd_memcpy_spec d src sz s hsrc := by
  simp only [fd_memcpy_spec, Cfg.denote]
  -- the source block, without destructing `hsrc` -- the statement mentions it
  obtain ⟨sblk, hsblk, hslen⟩ :
      ∃ blk, s.mem[src.id]? = some (.live blk)
        ∧ src.offsetInBits + 8 * sz.toNat ≤ blk.lengthInBits := id hsrc
  have hbytes : readWord hsrc = sblk.bytes.extractLsb' src.offsetInBits (8 * sz.toNat) := by
    simp only [readWord, readWord?, MemoryState.live?, hsblk, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def, Option.get_some]
  have hdlt : d.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hdst
  rw [hbytes]
  obtain ⟨bytes, hbv⟩ : ∃ w : BitVec (8 * sz.toNat),
      w = sblk.bytes.extractLsb' src.offsetInBits (8 * sz.toNat) := ⟨_, rfl⟩
  rw [← hbv]
  refine run_runFunction' _ ?_
  refine ⟨{ s with mem := s.mem.splice d bytes }, ?_, popFrame_splice_self hs hdlt⟩
  dsimp only [fd_memcpy]
  rw [BlockCom.run_bind_denote_var_of_nil
    (s' := { s with mem := s.mem.splice d bytes })
    (by simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        rw [run_liftM (run_memcpy hsblk hslen hdst), hbv]
        rfl)]
  simp_return

theorem fd_memset_conforms (d : Pointer) (sz : BitVec 64) (s : GlobalState) (hs : s.WF)
    (hdst : Fits s.mem d (8 * sz.toNat)) :
    fd_memset_spec d sz s := by
  simp only [fd_memset_spec, Cfg.denote]
  have hdlt : d.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hdst
  refine run_runFunction' _ ?_
  refine ⟨{ s with mem := s.mem.splice d (BitVec.replicate sz.toNat (0#8)) }, ?_,
    popFrame_splice_self hs hdlt⟩
  denote_step_all v 0
  denote_eval v 0 0
  simp only [LLVM.const?] at hv0
  subst hv0
  rw [BlockCom.run_bind_denote_var_of_nil
    (s' := { s with mem := s.mem.splice d (BitVec.replicate sz.toNat (0#8)) })
    (by simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        rw [run_liftM (run_memset hdst)]
        rfl)]
  simp_return

end Firedancer.Common
