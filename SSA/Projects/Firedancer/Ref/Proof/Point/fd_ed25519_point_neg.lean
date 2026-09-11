/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point

import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_neg
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# `fd_ed25519_point_neg` conformance

Four calls in the order `X, Y, Z, T` (byte offsets `0, 40, 120, 80`): `neg`,
`set`, `set`, `neg`. The destinations share `r`'s block at disjoint ranges, as
in `fd_ed25519_point_from`; the sources share `a`'s, which no store reaches.

`run_runFunction'` comes first and each callee is run where the walk reaches
it; the outputs and their properties are supplied once the region has returned.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

set_option maxHeartbeats 1600000 in
theorem fd_ed25519_point_neg_conforms (r a : Pointer) (s : GlobalState)
    (hs : s.WF) (hne : r.id ≠ a.id)
    (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) :
    fd_ed25519_point_neg_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_neg_spec, Cfg.denote]
  intro hbX hbT
  refine run_runFunction' _ ?_

  -- a gep by a field offset stays in the same block
  have hne' : ∀ o o' : BitVec 64, (r.withOffset o).id ≠ (a.withOffset o').id := fun _ _ => hne

  denote_expose

  -- `%0`: X ≔ -a->X, in `s`
  have hd0 : IsFieldElemPtr s.mem r := by
    simpa [Pointer.withOffset] using isCoordPtr hr 0
  have hc0 : IsFieldElemPtr s.mem a := by
    simpa [Pointer.withOffset] using isCoordPtr ha 0
  obtain ⟨oX, hvalX, hbndX, u₁, hrun₁, heq₁⟩ :=
    fd_f25519_neg_conforms r a s hs hd0 hc0 hbX
  peel_call hrun₁
  have hu₁WF : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁

  -- `%1 … %3`: Y ≔ a->Y, in `u₁`
  denote_step_reduce v 2 [gepConst, ptradd, LLVM.const?]
  have v1Value : v1 = .value (r.withOffset 40) := by
    simp [hv1, Pointer.withOffset, simp_sllvm]
  have v2Value : v2 = .value (a.withOffset 40) := by
    simp [hv2, Pointer.withOffset, simp_sllvm]
  subst v1Value v2Value
  clear hv1 hv2
  have hd1 : IsFieldElemPtr s.mem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hr 1
  have hc1 : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have hd1u : IsFieldElemPtr u₁.mem (r.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hd1.1), hd1.2⟩
  have hc1u : IsFieldElemPtr u₁.mem (a.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hc1.1), hc1.2⟩
  obtain ⟨oY, ⟨u₂, hrun₂, heq₂⟩, hcopy₂⟩ :=
    fd_f25519_set_conforms (r.withOffset 40) (a.withOffset 40) u₁ hu₁WF (hne' _ _) hd1u hc1u
  peel_call hrun₂
  have hu₂WF : u₂.WF := GlobalState.WF.of_equiv hu₁WF.splice heq₂

  -- `%4 … %6`: Z ≔ a->Z, in `u₂`
  denote_step_reduce v 5 [gepConst, ptradd, LLVM.const?]
  have v4Value : v4 = .value (r.withOffset 120) := by
    simp [hv4, Pointer.withOffset, simp_sllvm]
  have v5Value : v5 = .value (a.withOffset 120) := by
    simp [hv5, Pointer.withOffset, simp_sllvm]
  subst v4Value v5Value
  clear hv4 hv5
  have hd3 : IsFieldElemPtr s.mem (r.withOffset 120) := coordPtr_three r ▸ isCoordPtr hr 3
  have hc3 : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  have hd3u : IsFieldElemPtr u₂.mem (r.withOffset 120) :=
    ⟨fits_equiv heq₂ (by simpa using fits_splice (fits_equiv heq₁
      (by simpa using fits_splice hd3.1))), hd3.2⟩
  have hc3u : IsFieldElemPtr u₂.mem (a.withOffset 120) :=
    ⟨fits_equiv heq₂ (by simpa using fits_splice (fits_equiv heq₁
      (by simpa using fits_splice hc3.1))), hc3.2⟩
  obtain ⟨oZ, ⟨u₃, hrun₃, heq₃⟩, hcopy₃⟩ :=
    fd_f25519_set_conforms (r.withOffset 120) (a.withOffset 120) u₂ hu₂WF (hne' _ _) hd3u hc3u
  peel_call hrun₃
  have hu₃WF : u₃.WF := GlobalState.WF.of_equiv hu₂WF.splice heq₃

  -- `%7 … %9`: T ≔ -a->T, in `u₃`
  denote_step_reduce v 8 [gepConst, ptradd, LLVM.const?]
  have v7Value : v7 = .value (r.withOffset 80) := by
    simp [hv7, Pointer.withOffset, simp_sllvm]
  have v8Value : v8 = .value (a.withOffset 80) := by
    simp [hv8, Pointer.withOffset, simp_sllvm]
  subst v7Value v8Value
  clear hv7 hv8
  have hd2 : IsFieldElemPtr s.mem (r.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr hr 2
  have hc2 : IsFieldElemPtr s.mem (a.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr ha 2
  have hd2u : IsFieldElemPtr u₃.mem (r.withOffset 80) :=
    ⟨fits_equiv heq₃ (by simpa using fits_splice (fits_equiv heq₂
      (by simpa using fits_splice (fits_equiv heq₁
        (by simpa using fits_splice hd2.1))))), hd2.2⟩
  have hc2u : IsFieldElemPtr u₃.mem (a.withOffset 80) :=
    ⟨fits_equiv heq₃ (by simpa using fits_splice (fits_equiv heq₂
      (by simpa using fits_splice (fits_equiv heq₁
        (by simpa using fits_splice hc2.1))))), hc2.2⟩
  -- `a`'s limbs at `u₃` are its limbs at `s`: three calls wrote only `r`
  have La : ∀ (off : BitVec 64) (i : Fin 5),
      readLimb? (a.withOffset off) i u₃.mem = readLimb? (a.withOffset off) i s.mem := by
    intro off i
    have e3 := readLimb?_of_equiv heq₃ (a.withOffset off) i
    dsimp only at e3
    rw [readLimb?_splice_of_disjoint i (.inl (hne' _ _))] at e3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset off) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i (.inl (hne' _ _))] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset off) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i (.inl (show r.id ≠ (a.withOffset off).id from hne))] at e1
    rw [← e3, ← e2, ← e1]
  have hbTu : BiasBounds hc2u := fun i => by
    rw [readLimb_eq_of_readLimb? (h' := hc2) (La 80 i)]
    exact hbT i
  obtain ⟨oT, hvalT, hbndT, u₄, hrun₄, heq₄⟩ :=
    fd_f25519_neg_conforms (r.withOffset 80) (a.withOffset 80) u₃ hu₃WF hd2u hc2u hbTu
  peel_call hrun₄

  -- `return %arg0`, in `u₄`
  refine ⟨u₄, by simp_return, ?_⟩

  /- The region has returned. What remains is the four stores' readback. -/

  -- coordinate offsets in bits; `hr.right` rules out wrapping
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := hr.2; simp; omega)

  -- The four coordinates of `r` at the end, at the `readLimb?` level.
  have Lx : ∀ i : Fin 5,
      readLimb? r i ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
        (r.withOffset 120) oZ).splice (r.withOffset 80) oT)
        = readLimb? r i (s.mem.splice r oX) := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h80]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h120]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40]; omega)))]

  have Ly : ∀ i : Fin 5,
      readLimb? (r.withOffset 40) i ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
        (r.withOffset 120) oZ).splice (r.withOffset 80) oT)
        = readLimb? (a.withOffset 40) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40, h80]; omega))),
      readLimb?_splice_of_disjoint i (.inr (.inr (by rw [h40, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice hd1.1) i]
    have h2 := hcopy₂ i
    rw [limbSpliceReadback _ _ _ hd1u.1 i] at h2
    rw [h2, ← readLimb?_of_equiv heq₁ (a.withOffset 40) i]
    exact readLimb?_splice_of_disjoint i (.inl (show r.id ≠ (a.withOffset 40).id from hne))

  have Lz : ∀ i : Fin 5,
      readLimb? (r.withOffset 120) i ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
        (r.withOffset 120) oZ).splice (r.withOffset 80) oT)
        = readLimb? (a.withOffset 120) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inl (by rw [h80, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice (fits_splice hd3.1)) i]
    have h3 := hcopy₃ i
    rw [limbSpliceReadback _ _ _ hd3u.1 i] at h3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 120) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i (.inl (hne' _ _))] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 120) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i
      (.inl (show r.id ≠ (a.withOffset 120).id from hne))] at e1
    rw [h3, ← e2, ← e1]

  have Lt : ∀ i : Fin 5,
      readLimb? (r.withOffset 80) i ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
        (r.withOffset 120) oZ).splice (r.withOffset 80) oT)
        = readLimb? (r.withOffset 80) i (u₃.mem.splice (r.withOffset 80) oT) := by
    intro i
    rw [limbSpliceReadback _ _ _ (fits_splice (fits_splice (fits_splice hd2.1))) i,
      limbSpliceReadback _ _ _ hd2u.1 i]

  refine ⟨oX, oY, oZ, oT, ?equiv, ?point, fun i => ?bx, fun i => ?bt,
    fun i => readLimb_eq_of_readLimb? (Ly i),
    fun i => readLimb_eq_of_readLimb? (Lz i)⟩

  case equiv =>
    have c₂ :=
      GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 40) (x := oY) heq₁) heq₂
    have c₃ :=
      GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 120) (x := oZ) c₂) heq₃
    have hchain :=
      GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 80) (x := oT) c₃) heq₄
    have hu₄WF : u₄.WF := GlobalState.WF.of_equiv hu₃WF.splice heq₄
    have halloc : u₄.alloc = s.alloc :=
      (heq₁.1.trans (heq₂.1.trans (heq₃.1.trans heq₄.1))).symm
    have hglobals : s.globals = u₄.globals :=
      heq₁.globals.trans (heq₂.globals.trans (heq₃.globals.trans heq₄.globals))
    have hpop : (s.popFrame u₄.mem : GlobalState) ≈ u₄ :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none (fun b hb => hu₄WF b (by rw [halloc]; omega)))
        ⟨halloc.symm, hglobals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans hchain (GlobalState.Equiv.symm hpop)

  case bx =>
    rw [readLimb_eq_of_readLimb? (h' := isFieldElemPtr_splice hd0) (Lx i)]
    exact hbndX i
  case bt =>
    rw [readLimb_eq_of_readLimb? (h' := isFieldElemPtr_splice hd2u) (Lt i)]
    exact hbndT i

  case point =>
    have hP : readPoint ha =
        ⟨readFieldElem hc0, readFieldElem hc1, readFieldElem hc3, readFieldElem hc2⟩ :=
      readPoint_eq_of ha rfl rfl rfl rfl
    rw [hP]
    refine readPoint_eq_of _
      (h0 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hd0))))
      (h1 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hd1))))
      (h2 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hd2))))
      (h3 := isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice
        (isFieldElemPtr_splice hd3))))
      ?_ ?_ ?_ ?_
    · rw [readFieldElem_eq_of_readLimb (h' := isFieldElemPtr_splice hd0)
        (fun i => readLimb_eq_of_readLimb? (Lx i)), hvalX]
    · exact readFieldElem_eq_of_readLimb (h' := hc1) (fun i => readLimb_eq_of_readLimb? (Ly i))
    · rw [readFieldElem_eq_of_readLimb (h' := isFieldElemPtr_splice hd2u)
        (fun i => readLimb_eq_of_readLimb? (Lt i)), hvalT,
        readFieldElem_eq_of_readLimb (h' := hc2) (fun i => readLimb_eq_of_readLimb? (La 80 i))]
    · exact readFieldElem_eq_of_readLimb (h' := hc3) (fun i => readLimb_eq_of_readLimb? (Lz i))

end Firedancer.Ref
