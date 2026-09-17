/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_point_set
public import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_set
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_set
public import SSA.Projects.Firedancer.Conformance.Proof.fd_ed25519_point_frombytes_2x

/-!
# `fd_ed25519_point_set`: ref ≡ avx512

Each side copies its input: the ref output reads back as `a`'s point, the
avx512 output as `a'`'s QUAD (`readQuad_writeQuad`), and the hypothesis links
the two inputs.
-/

@[expose] public section

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_point_set : fd_ed25519_point_set_equivalent := by
  unfold fd_ed25519_point_set_equivalent
  intro s r a hs hr ha hne refResult

  obtain ⟨oX, oY, oZ, oT, ⟨sRef, hrefRun, hrefEq⟩, -, -, -, -, hpt⟩ :=
    Ref.fd_ed25519_point_set_conforms r a s hs hne hr ha

  intro s' r' a' hs' hr' ha' hne' avxResult

  obtain ⟨sAvx, havxRun, havxEq⟩ :=
    Avx512.fd_ed25519_point_set_conforms r' a' s' hs' hne' hr' ha'

  intro hlink

  refine ⟨(_, sRef), (_, sAvx), hrefRun, havxRun, oX, oY, oZ, oT, Avx512.readQuad ha',
    GlobalState.Equiv.symm hrefEq, GlobalState.Equiv.symm havxEq,
    Ref.isPointPtr_splice (Ref.isPointPtr_splice
      (Ref.isPointPtr_splice (Ref.isPointPtr_splice hr))),
    Avx512.isQuadPtr_writeQuad hr' _, rfl, rfl, ?_, hpt⟩
  rw [hpt, hlink, Avx512.readQuad_writeQuad hr']

end Firedancer
