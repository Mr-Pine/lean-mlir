/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts.Entry

/-!
# `fd_ed25519_point_add_with_opts` conforms (AVX-512)

`b_is_precomputed = 1`. `^bb0` (`entry_run`) branches to `^bb1` (`bb1_run`), which
computes `FD_R43X6_GE_ADD_TABLE_ALT` up to the last product; `^bb3` (`bb3_run`) folds
it and stores into `r`. The arithmetic is `PointAdd.geAddTable`
(`fd_ed25519_point_add_with_opts/Model.lean`).
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

open PointAdd Ge in
theorem fd_ed25519_point_add_with_opts_conforms (r a b : Pointer) (bPre : BitVec 32)
    (s : GlobalState) (hs : s.WF) (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a)
    (hb : IsQuadPtr s.mem b) :
    fd_ed25519_point_add_with_opts_spec r a b bPre s hr ha hb := by
  simp only [fd_ed25519_point_add_with_opts_spec]
  intro hpre ha03 ha14 ha25 hb03 hb14 hb25
  subst hpre
  refine run_runFunction' _ ?_
  have hua : QuadU44 (readQuad ha) := ⟨ha03, ha14, ha25⟩
  have hub : QuadU44 (readQuad hb) := ⟨hb03, hb14, hb25⟩
  refine entry_run r a b s hs fun W u env hF hrun => ?_
  rw [show (1 : BitVec 32) = 1#32 from rfl, hrun]
  refine bb1_run env ha hb hua hub (lt_nextFreeBlock_of_fits hs ha.1)
    (lt_nextFreeBlock_of_fits hs hb.1) hF fun u1 hrun1 hF1 => ?_
  rw [hrun1]
  have hrlt := lt_nextFreeBlock_of_fits hs hr.1
  refine bb3_run env (quadMulResult (egegQuad (addR (readQuad ha) (readQuad hb)))
    (fhfhQuad (addR (readQuad ha) (readQuad hb)))) hF1 hr hrlt fun u2 hrun2 hF2 => ?_
  have hu := u44_geAddTable hua hub
  exact ⟨u2, hrun2, geAddTable (readQuad ha) (readQuad hb),
    popFrame_equiv hs hrlt hF2 (fun _ hne => live?_writeQuad_ne (Ne.symm hne)) rfl,
    toPoint_geAddTable hua hub, hu.1, hu.2.1, hu.2.2⟩

end Firedancer.Avx512
