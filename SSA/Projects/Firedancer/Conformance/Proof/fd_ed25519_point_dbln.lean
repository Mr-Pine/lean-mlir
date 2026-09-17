/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_point_dbln
public import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_dbln
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln
public import SSA.Projects.Firedancer.Conformance.Proof.fd_ed25519_point_frombytes_2x

/-!
# `fd_ed25519_point_dbln`: ref ≡ avx512

Each side's conformance gives `dbln n` of its own input; `Point.dbln_congr`
equates the two, since the inputs agree on `X`, `Y`, `Z`.
-/

@[expose] public section

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The composition, over the two backend theorems as hypotheses. -/
private theorem of_conforms
    (hRef : ∀ (r a : Pointer) (n : BitVec 32) (s : GlobalState)
      (_ : s.WF) (hr : Ref.IsPointPtr s.mem r) (ha : Ref.IsPointPtr s.mem a)
      (_ : Ref.BiasBounds (Ref.isCoordPtr ha 0)) (_ : Ref.LimbBounds (Ref.isCoordPtr ha 1))
      (_ : Ref.LimbBounds.Loose (Ref.isCoordPtr ha 3))
      (_ : n.toInt < 256), Ref.fd_ed25519_point_dbln_spec r a n s hr ha)
    (hAvx : ∀ (r a : Pointer) (n : BitVec 32) (s : GlobalState)
      (_ : s.WF) (hr : Avx512.IsQuadPtr s.mem r) (ha : Avx512.IsQuadPtr s.mem a)
      (_ : R43x6.U44 (Avx512.readQuad ha).v03 ∧ R43x6.U44 (Avx512.readQuad ha).v14
        ∧ R43x6.U44 (Avx512.readQuad ha).v25)
      (_ : n.toInt < 256), Avx512.fd_ed25519_point_dbln_spec r a n s hr ha) :
    fd_ed25519_point_dbln_equivalent := by
  intro s r a n hs hr ha haX haY haZ hn refResult s' r' a' hs' hr' ha' hu' avxResult P P'
    hX hY hZ
  obtain ⟨oX, oY, oZ, oT, ⟨sRef, hrefRun, hrefEq⟩, hvRef, -⟩ :=
    hRef r a n s hs hr ha
      (Ref.biasBounds_congr (Ref.coordPtr_zero a).symm
        (Ref.biasBounds_of_readLimb? (Ref.coordPtr_zero a ▸ Ref.isCoordPtr ha 0) haX))
      (Ref.limbBounds_of_readLimb? _ haY) (Ref.limbBounds_of_readLimb? _ haZ) hn
  obtain ⟨q, ⟨sAvx, havxRun, havxEq⟩, hvAvx, -⟩ := hAvx r' a' n s' hs' hr' ha' hu' hn
  have hrOut' : Avx512.IsQuadPtr (s'.mem.writeQuad r' q) r' := Avx512.isQuadPtr_writeQuad hr' q
  refine ⟨(_, sRef), (_, sAvx), hrefRun, havxRun, oX, oY, oZ, oT, q,
    GlobalState.Equiv.symm hrefEq, GlobalState.Equiv.symm havxEq, _, hrOut',
    rfl, rfl, ?_, hvRef⟩
  rw [hvRef, Avx512.readQuad_writeQuad hr' hrOut', hvAvx]
  exact Point.dbln_congr n hX hY hZ

theorem fd_ed25519_point_dbln : fd_ed25519_point_dbln_equivalent :=
  of_conforms Ref.fd_ed25519_point_dbln_conforms Avx512.fd_ed25519_point_dbln_conforms

end Firedancer
