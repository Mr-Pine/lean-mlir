/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point

import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# `fd_ed25519_point_to` conformance

The mirror of `fd_ed25519_point_from`: four `fd_f25519_set` calls in the order
`x, y, z, t`, reading `a`'s coordinates at byte offsets `0, 40, 120, 80`.

Transporting is easier here than in `point_from`. There the four destinations
shared `r`'s block and the disjointness was arithmetic on offsets; here they
are four *different* blocks, pairwise apart by `hNodup` and apart from `a`, so
every splice a later call makes is `.inl`-disjoint from what an earlier one
wrote and from the source still to be read.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The four coordinates of a point, as reads at the pointers the region geps.
`readPoint_eq_of` with every value taken to be the read itself. -/
private theorem readPoint_of_coords {m : MemoryState} {a : Pointer} (ha : IsPointPtr m a)
    (h0 : IsFieldElemPtr m a) (h1 : IsFieldElemPtr m (a.withOffset 40))
    (h2 : IsFieldElemPtr m (a.withOffset 80)) (h3 : IsFieldElemPtr m (a.withOffset 120)) :
    readPoint ha =
      { X := readFieldElem h0, Y := readFieldElem h1, Z := readFieldElem h3,
        T := readFieldElem h2 } :=
  readPoint_eq_of ha rfl rfl rfl rfl

set_option maxHeartbeats 1600000 in
theorem fd_ed25519_point_to_conforms (x y z t a : Pointer) (s : GlobalState) (hs : s.WF)
    (hNodup : ([x, y, z, t, a].map Pointer.id).Nodup) (ha : IsPointPtr s.mem a)
    (hx : IsFieldElemPtr s.mem x) (hy : IsFieldElemPtr s.mem y) (hz : IsFieldElemPtr s.mem z)
    (ht : IsFieldElemPtr s.mem t) : fd_ed25519_point_to_spec x y z t a s hNodup ha hx hy hz ht := by
  simp only [fd_ed25519_point_to_spec, Cfg.denote]
  -- the ten pairwise block inequalities `hNodup` packages
  have hnd := hNodup
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.mem_singleton, or_false, not_or, List.nodup_nil, and_true] at hnd
  have hxy : x.id ≠ y.id := by tauto
  have hxz : x.id ≠ z.id := by tauto
  have hxt : x.id ≠ t.id := by tauto
  have hxa : x.id ≠ a.id := by tauto
  have hyz : y.id ≠ z.id := by tauto
  have hyt : y.id ≠ t.id := by tauto
  have hya : y.id ≠ a.id := by tauto
  have hzt : z.id ≠ t.id := by tauto
  have hza : z.id ≠ a.id := by tauto
  have hta : t.id ≠ a.id := by tauto
  -- the four coordinate pointers, as field elements in `s`
  have hc0 : IsFieldElemPtr s.mem a := by simpa [Pointer.withOffset] using isCoordPtr ha 0
  have hc1 : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have hc2 : IsFieldElemPtr s.mem (a.withOffset 80) := by
    simpa [Pointer.withOffset] using isCoordPtr ha 2
  have hc3 : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  -- call 1: x ≔ a->X, in `s`
  obtain ⟨oX, ⟨u₁, hrun₁, heq₁⟩, hcopy₁⟩ := fd_f25519_set_conforms x a s hs hxa hx hc0
  have hu₁WF : u₁.WF := GlobalState.WF.of_equiv hs.splice heq₁
  -- call 2: y ≔ a->Y, in `u₁`
  have hyu : IsFieldElemPtr u₁.mem y := ⟨fits_equiv heq₁ (by simpa using fits_splice hy.1), hy.2⟩
  have hc1u : IsFieldElemPtr u₁.mem (a.withOffset 40) :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice hc1.1), hc1.2⟩
  obtain ⟨oY, ⟨u₂, hrun₂, heq₂⟩, hcopy₂⟩ :=
    fd_f25519_set_conforms y (a.withOffset 40) u₁ hu₁WF hya hyu hc1u
  have hu₂WF : u₂.WF := GlobalState.WF.of_equiv hu₁WF.splice heq₂
  -- call 3: z ≔ a->Z, in `u₂`
  have hzu : IsFieldElemPtr u₂.mem z :=
    ⟨fits_equiv heq₂
        (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice hz.1))),
      hz.2⟩
  have hc3u : IsFieldElemPtr u₂.mem (a.withOffset 120) :=
    ⟨fits_equiv heq₂
        (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice hc3.1))),
      hc3.2⟩
  obtain ⟨oZ, ⟨u₃, hrun₃, heq₃⟩, hcopy₃⟩ :=
    fd_f25519_set_conforms z (a.withOffset 120) u₂ hu₂WF hza hzu hc3u
  have hu₃WF : u₃.WF := GlobalState.WF.of_equiv hu₂WF.splice heq₃
  -- call 4: t ≔ a->T, in `u₃`
  have htu : IsFieldElemPtr u₃.mem t :=
    ⟨fits_equiv heq₃
        (by
          simpa using
            fits_splice
              (fits_equiv heq₂
                (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice ht.1))))),
      ht.2⟩
  have hc2u : IsFieldElemPtr u₃.mem (a.withOffset 80) :=
    ⟨fits_equiv heq₃
        (by
          simpa using
            fits_splice
              (fits_equiv heq₂
                (by simpa using fits_splice (fits_equiv heq₁ (by simpa using fits_splice hc2.1))))),
      hc2.2⟩
  obtain ⟨oT, ⟨u₄, hrun₄, heq₄⟩, hcopy₄⟩ :=
    fd_f25519_set_conforms t (a.withOffset 80) u₃ hu₃WF hta htu hc2u
  have hu₄WF : u₄.WF := GlobalState.WF.of_equiv hu₃WF.splice heq₄
  refine ⟨oX, oY, oZ, oT, ?_⟩
  -- a gep by a field offset stays in the same block
  have ida : ∀ off : BitVec 64, (a.withOffset off).id = a.id := fun _ => rfl
  -- The limb copies, at the `readLimb?` level: no proof arguments, so the same
  -- fact serves both the limb conjuncts and the value ones.
  have Lx :
    ∀ i : Fin 5,
      readLimb? x i ((((s.mem.splice x oX).splice y oY).splice z oZ).splice t oT) =
        readLimb? a i s.mem := by
    intro i
    rw [readLimb?_splice_of_disjoint i (.inl (Ne.symm hxt)),
      readLimb?_splice_of_disjoint i (.inl (Ne.symm hxz)),
      readLimb?_splice_of_disjoint i (.inl (Ne.symm hxy))]
    exact hcopy₁ i
  have Ly :
    ∀ i : Fin 5,
      readLimb? y i ((((s.mem.splice x oX).splice y oY).splice z oZ).splice t oT) =
        readLimb? (a.withOffset 40) i s.mem := by
    intro i
    rw [readLimb?_splice_of_disjoint i (.inl (Ne.symm hyt)),
      readLimb?_splice_of_disjoint i (.inl (Ne.symm hyz)),
      limbSpliceReadback _ _ _ (fits_splice hy.1) i]
    have h2 := hcopy₂ i
    rw [limbSpliceReadback _ _ _ hyu.1 i] at h2
    rw [h2, ← readLimb?_of_equiv heq₁ (a.withOffset 40) i]
    exact
      readLimb?_splice_of_disjoint i
        (.inl
          (by
            rw [ida]; exact hxa))
  have Lz :
    ∀ i : Fin 5,
      readLimb? z i ((((s.mem.splice x oX).splice y oY).splice z oZ).splice t oT) =
        readLimb? (a.withOffset 120) i s.mem := by
    intro i
    rw [readLimb?_splice_of_disjoint i (.inl (Ne.symm hzt)),
      limbSpliceReadback _ _ _ (fits_splice (fits_splice hz.1)) i]
    have h3 := hcopy₃ i
    rw [limbSpliceReadback _ _ _ hzu.1 i] at h3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 120) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i
        (.inl
          (by
            rw [ida]; exact hya))] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 120) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i
        (.inl
          (by
            rw [ida]; exact hxa))] at e1
    rw [h3, ← e2, ← e1]
  have Lt :
    ∀ i : Fin 5,
      readLimb? t i ((((s.mem.splice x oX).splice y oY).splice z oZ).splice t oT) =
        readLimb? (a.withOffset 80) i s.mem := by
    intro i
    rw [limbSpliceReadback _ _ _ (fits_splice (fits_splice (fits_splice ht.1))) i]
    have h4 := hcopy₄ i
    rw [limbSpliceReadback _ _ _ htu.1 i] at h4
    have e3 := readLimb?_of_equiv heq₃ (a.withOffset 80) i
    dsimp only at e3
    rw [readLimb?_splice_of_disjoint i
        (.inl
          (by
            rw [ida]; exact hza))] at e3
    have e2 := readLimb?_of_equiv heq₂ (a.withOffset 80) i
    dsimp only at e2
    rw [readLimb?_splice_of_disjoint i
        (.inl
          (by
            rw [ida]; exact hya))] at e2
    have e1 := readLimb?_of_equiv heq₁ (a.withOffset 80) i
    dsimp only at e1
    rw [readLimb?_splice_of_disjoint i
        (.inl
          (by
            rw [ida]; exact hxa))] at e1
    rw [h4, ← e3, ← e2, ← e1]
  refine
    ⟨⟨s.popFrame u₄.mem, run_runFunction (s' := u₄) ?run, ?equiv⟩, fun i =>
      readLimb_eq_of_readLimb? (Lx i), fun i => readLimb_eq_of_readLimb? (Ly i), fun i =>
      readLimb_eq_of_readLimb? (Lz i), fun i => readLimb_eq_of_readLimb? (Lt i), ?vx, ?vy, ?vz, ?vt⟩
  case vx =>
    rw [readFieldElem_eq_of_readLimb (h' := hc0) (fun i => readLimb_eq_of_readLimb? (Lx i)),
      readPoint_of_coords ha hc0 hc1 hc2 hc3]
  case vy =>
    rw [readFieldElem_eq_of_readLimb (h' := hc1) (fun i => readLimb_eq_of_readLimb? (Ly i)),
      readPoint_of_coords ha hc0 hc1 hc2 hc3]
  case vz =>
    rw [readFieldElem_eq_of_readLimb (h' := hc3) (fun i => readLimb_eq_of_readLimb? (Lz i)),
      readPoint_of_coords ha hc0 hc1 hc2 hc3]
  case vt =>
    rw [readFieldElem_eq_of_readLimb (h' := hc2) (fun i => readLimb_eq_of_readLimb? (Lt i)),
      readPoint_of_coords ha hc0 hc1 hc2 hc3]
  case equiv =>
    have c₂ := GlobalState.Equiv.trans (splice_equiv (p := y) (x := oY) heq₁) heq₂
    have c₃ := GlobalState.Equiv.trans (splice_equiv (p := z) (x := oZ) c₂) heq₃
    have hchain := GlobalState.Equiv.trans (splice_equiv (p := t) (x := oT) c₃) heq₄
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
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value x) (s' := u₁) ?_).trans ?_
    · exact hrun₁
    denote_step_all v 1
    denote_eval v 1 1
    simp [gepConst, ptradd, LLVM.const?] at hv1
    have v1Value : v1 = .value (a.withOffset 40) := by simp [hv1, Pointer.withOffset, simp_sllvm]
    subst v1Value
    clear hv1
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value y) (s' := u₂) ?_).trans ?_
    · exact hrun₂
    denote_step_all v 3
    denote_eval v 3 3
    simp [gepConst, ptradd, LLVM.const?] at hv3
    have v3Value : v3 = .value (a.withOffset 120) := by simp [hv3, Pointer.withOffset, simp_sllvm]
    subst v3Value
    clear hv3
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value z) (s' := u₃) ?_).trans ?_
    · exact hrun₃
    denote_step_all v 5
    denote_eval v 5 5
    simp [gepConst, ptradd, LLVM.const?] at hv5
    have v5Value : v5 = .value (a.withOffset 80) := by simp [hv5, Pointer.withOffset, simp_sllvm]
    subst v5Value
    clear hv5
    refine (BlockCom.run_bind_denote_call_of_value (x := PoisonOr.value t) (s' := u₄) ?_).trans ?_
    · exact hrun₄
    simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm] <;> rfl

end Firedancer.Ref
