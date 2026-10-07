/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_set
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
public import SSA.Projects.Firedancer.Ref.Proof.Point
public import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# `fd_ed25519_point_set` conformance

Four `fd_f25519_set` calls, `X, Y, Z, T` at byte offsets `0, 40, 120, 80`.
Destinations share `r`'s block, so a later splice misses an earlier copy by
offset (as in `point_from`); sources lie in `a`'s block, which no splice
touches (as in `point_to`).
-/

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

theorem fd_ed25519_point_set_conforms (r a : Pointer) (s : GlobalState) (hs : s.WF)
    (hne : r.id ≠ a.id) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) :
    fd_ed25519_point_set_spec r a s hne hr ha := by
  simp only [fd_ed25519_point_set_spec, Cfg.denote]
  -- the coordinate pointers of both points, as field elements in `s`
  have hr0 : IsFieldElemPtr s.mem r := by simpa [Pointer.withOffset] using isCoordPtr hr 0
  have hr1 : IsFieldElemPtr s.mem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hr 1
  have hr2 : IsFieldElemPtr s.mem (r.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr hr 2
  have hr3 : IsFieldElemPtr s.mem (r.withOffset 120) := coordPtr_three r ▸ isCoordPtr hr 3
  have ha0 : IsFieldElemPtr s.mem a := by simpa [Pointer.withOffset] using isCoordPtr ha 0
  have ha1 : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have ha2 : IsFieldElemPtr s.mem (a.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr ha 2
  have ha3 : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  -- call 1: X, in `s`
  obtain ⟨oX, ⟨u₁, hrun₁, heq₁⟩, hcopy₁⟩ := fd_f25519_set_conforms r a s hs hne hr0 ha0
  have hu₁WF : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁
  -- call 2: Y, in `u₁`
  have hr1u : IsFieldElemPtr u₁.mem (r.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hr1.1), hr1.2⟩
  have ha1u : IsFieldElemPtr u₁.mem (a.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice ha1.1), ha1.2⟩
  obtain ⟨oY, ⟨u₂, hrun₂, heq₂⟩, hcopy₂⟩ :=
    fd_f25519_set_conforms (r.withOffset 40) (a.withOffset 40) u₁ hu₁WF hne hr1u ha1u
  have hu₂WF : u₂.WF := GlobalState.WF.of_equiv hu₁WF.splice heq₂
  -- call 3: Z, in `u₂`
  have hr3u : IsFieldElemPtr u₂.mem (r.withOffset 120) :=
    ⟨fits_equiv heq₂
        (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice hr3.1))),
      hr3.2⟩
  have ha3u : IsFieldElemPtr u₂.mem (a.withOffset 120) :=
    ⟨fits_equiv heq₂
        (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice ha3.1))),
      ha3.2⟩
  obtain ⟨oZ, ⟨u₃, hrun₃, heq₃⟩, hcopy₃⟩ :=
    fd_f25519_set_conforms (r.withOffset 120) (a.withOffset 120) u₂ hu₂WF hne hr3u ha3u
  have hu₃WF : u₃.WF := GlobalState.WF.of_equiv hu₂WF.splice heq₃
  -- call 4: T, in `u₃`
  have hr2u : IsFieldElemPtr u₃.mem (r.withOffset 80) :=
    ⟨fits_equiv heq₃
        (by
          simpa using
            fits_splice
              (fits_equiv heq₂
                (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice hr2.1))))),
      hr2.2⟩
  have ha2u : IsFieldElemPtr u₃.mem (a.withOffset 80) :=
    ⟨fits_equiv heq₃
        (by
          simpa using
            fits_splice
              (fits_equiv heq₂
                (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice ha2.1))))),
      ha2.2⟩
  obtain ⟨oT, ⟨u₄, hrun₄, heq₄⟩, hcopy₄⟩ :=
    fd_f25519_set_conforms (r.withOffset 80) (a.withOffset 80) u₃ hu₃WF hne hr2u ha2u
  have hu₄WF : u₄.WF := GlobalState.WF.of_equiv hu₃WF.splice heq₄
  refine ⟨oX, oY, oZ, oT, ?_⟩
  -- coordinate offsets in bits; `hr.right` rules out wrapping
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using
      withOffset_offsetInBits (off := 40)
        (by
          have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using
      withOffset_offsetInBits (off := 80)
        (by
          have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using
      withOffset_offsetInBits (off := 120)
        (by
          have := hr.2; simp; omega)
  -- the limb copies, at the `readLimb?` level
  have Lx :
    ∀ i : Fin 5,
      readLimb? r i
          ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
            (r.withOffset 80) oT) =
        readLimb? a i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i
        (.inr
          (.inr
            (by
              rw [h80]; omega))),
      readLimb?_splice_of_disjoint i
        (.inr
          (.inr
            (by
              rw [h120]; omega))),
      readLimb?_splice_of_disjoint i
        (.inr
          (.inr
            (by
              rw [h40]; omega)))]
    exact hcopy₁ i
  have Ly :
    ∀ i : Fin 5,
      readLimb? (r.withOffset 40) i
          ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
            (r.withOffset 80) oT) =
        readLimb? (a.withOffset 40) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i
        (.inr
          (.inr
            (by
              rw [h40, h80]; omega))),
      readLimb?_splice_of_disjoint i
        (.inr
          (.inr
            (by
              rw [h40, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice hr1.1) i]
    have h2 := hcopy₂ i
    rw [limbSpliceReadback _ _ _ hr1u.1 i] at h2
    rw [h2, ← readLimb?_of_equiv heq₁ (a.withOffset 40) i]
    exact readLimb?_splice_of_disjoint i (.inl hne)
  have Lz :
    ∀ i : Fin 5,
      readLimb? (r.withOffset 120) i
          ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
            (r.withOffset 80) oT) =
        readLimb? (a.withOffset 120) i s.mem := by
    intro i
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i
        (.inr
          (.inl
            (by
              rw [h80, h120]; omega))),
      limbSpliceReadback _ _ _ (fits_splice (fits_splice hr3.1)) i]
    have h3 := hcopy₃ i
    rw [limbSpliceReadback _ _ _ hr3u.1 i] at h3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 120) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint (q := r.withOffset 40) (p := a.withOffset 120) i
        (.inl hne)] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 120) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint (q := r) (p := a.withOffset 120) i (.inl hne)] at e1
    rw [h3, ← e2, ← e1]
  have Lt :
    ∀ i : Fin 5,
      readLimb? (r.withOffset 80) i
          ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
            (r.withOffset 80) oT) =
        readLimb? (a.withOffset 80) i s.mem := by
    intro i
    rw [limbSpliceReadback _ _ _ (fits_splice (fits_splice (fits_splice hr2.1))) i]
    have h4 := hcopy₄ i
    rw [limbSpliceReadback _ _ _ hr2u.1 i] at h4
    have e3 := readLimb?_of_equiv heq₃ (a.withOffset 80) i
    dsimp only at e3
    rw [readLimb?_splice_of_disjoint (q := r.withOffset 120) (p := a.withOffset 80) i
        (.inl hne)] at e3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 80) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint (q := r.withOffset 40) (p := a.withOffset 80) i
        (.inl hne)] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 80) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint (q := r) (p := a.withOffset 80) i (.inl hne)] at e1
    rw [h4, ← e3, ← e2, ← e1]
  refine ⟨⟨s.popFrame u₄.mem, run_runFunction (s' := u₄) ?run, ?equiv⟩, Lx, Ly, Lt, Lz, ?pt⟩
  case
    pt =>
    have o0 :
      IsFieldElemPtr
        ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
          (r.withOffset 80) oT)
        r :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr0)))
    have o1 :
      IsFieldElemPtr
        ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
          (r.withOffset 80) oT)
        (r.withOffset 40) :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr1)))
    have o2 :
      IsFieldElemPtr
        ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
          (r.withOffset 80) oT)
        (r.withOffset 80) :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr2)))
    have o3 :
      IsFieldElemPtr
        ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
          (r.withOffset 80) oT)
        (r.withOffset 120) :=
      isFieldElemPtr_splice
        (isFieldElemPtr_splice (isFieldElemPtr_splice (isFieldElemPtr_splice hr3)))
    exact
      (readPoint_eq_of _
          (readFieldElem_eq_of_readLimb (h := o0) (h' := ha0) (readLimb_eq_of_readLimb? <| Lx ·))
          (readFieldElem_eq_of_readLimb (h := o1) (h' := ha1) (readLimb_eq_of_readLimb? <| Ly ·))
          (readFieldElem_eq_of_readLimb (h := o2) (h' := ha2) (readLimb_eq_of_readLimb? <| Lt ·))
          (readFieldElem_eq_of_readLimb (h := o3) (h' := ha3)
            (readLimb_eq_of_readLimb? <| Lz ·))) |>.trans
        (readPoint_eq_of ha rfl rfl rfl rfl).symm
  case
    equiv =>
    have c₂ := GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 40) (x := oY) heq₁) heq₂
    have c₃ := GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 120) (x := oZ) c₂) heq₃
    have hchain := GlobalState.Equiv.trans (splice_equiv (p := r.withOffset 80) (x := oT) c₃) heq₄
    have halloc : u₄.alloc = s.alloc := (heq₁.1.trans (heq₂.1.trans (heq₃.1.trans heq₄.1))).symm
    have hglobals : s.globals = u₄.globals :=
      heq₁.globals.trans (heq₂.globals.trans (heq₃.globals.trans heq₄.globals))
    have hpop : (s.popFrame u₄.mem : GlobalState) ≈ u₄ :=
      GlobalState.Equiv.trans
        (killFrom_equiv_of_none
          (fun b hb =>
            hu₄WF b
              (by
                rw [halloc]; omega)))
        ⟨halloc.symm, hglobals, fun _ => rfl⟩
    exact GlobalState.Equiv.trans hchain (GlobalState.Equiv.symm hpop)
  case run =>
    denote_expose
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value r) (s' := u₁) ?_).trans ?_
    · exact hrun₁
    denote_step_all v 2
    denote_eval v 1 2
    simp [gepConst, ptradd, LLVM.const?] at hv1 hv2
    have v1Value : v1 = .value (r.withOffset 40) := by simp [hv1, Pointer.withOffset, simp_sllvm]
    have v2Value : v2 = .value (a.withOffset 40) := by simp [hv2, Pointer.withOffset, simp_sllvm]
    subst v1Value v2Value
    clear hv1 hv2
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r.withOffset 40)) (s' := u₂)
            ?_).trans
        ?_
    · exact hrun₂
    denote_step_all v 5
    denote_eval v 4 5
    simp [gepConst, ptradd, LLVM.const?] at hv4 hv5
    have v4Value : v4 = .value (r.withOffset 120) := by simp [hv4, Pointer.withOffset, simp_sllvm]
    have v5Value : v5 = .value (a.withOffset 120) := by simp [hv5, Pointer.withOffset, simp_sllvm]
    subst v4Value v5Value
    clear hv4 hv5
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r.withOffset 120)) (s' := u₃)
            ?_).trans
        ?_
    · exact hrun₃
    denote_step_all v 8
    denote_eval v 7 8
    simp [gepConst, ptradd, LLVM.const?] at hv7 hv8
    have v7Value : v7 = .value (r.withOffset 80) := by simp [hv7, Pointer.withOffset, simp_sllvm]
    have v8Value : v8 = .value (a.withOffset 80) := by simp [hv8, Pointer.withOffset, simp_sllvm]
    subst v7Value v8Value
    clear hv7 hv8
    refine
      (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value (r.withOffset 80)) (s' := u₄)
            ?_).trans
        ?_
    · exact hrun₄
    simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm] <;> rfl

end Firedancer.Ref
