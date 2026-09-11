/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Conformance.Rel
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.WriteChain
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_eq
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_f25519_is_zero
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_f25519_eq

/-!
# `fd_ed25519_affine_is_small_order`: ref ≡ avx512, in lockstep

The two regions are the same source with the field representation swapped, and
this proof walks them together: one goal holds both runs, each side is stepped
under `focus_left`/`focus_right` where a step is side-specific, and the two
walks meet at the end on the equality of the two input points.

It is built the way the two per-backend proofs
(`Ref/Proof/Point/…`, `Avx512/Proof/Point/…`) are built, and for the same
reasons:

* the callees are `local irreducible`, so no stepper defeq ever opens one --
  that, not the call site, is what sends `peel_call` to the heartbeat limit;
* `run_runFunction'` comes first and each callee's state is obtained where the
  walk reaches it;
* memory facts cross a callee through `live?_of_equiv_mem` (stated over
  `{ s with mem := m }`), `wf_splice4` and `frameBelow_splice4`, never through a
  projection walked across four splices.

What the lockstep buys over composing the two per-backend theorems: the
statement needs neither `Z = 1` nor the curve equation. The shared result is
fixed up front as the disjunction the three `or`s literally build, on the ref
point; each side's walk reaches that shape on its own point, and `hpoint`
closes. No `lowOrder`, no `isSmallOrderTest_iff_mem`.
-/

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

-- the callees are reached only through their conformance theorems
attribute [local irreducible]
  Ref.fd_ed25519_point_to Ref.fd_f25519_is_zero Ref.fd_f25519_eq
  Avx512.fd_ed25519_point_to Avx512.fd_f25519_is_zero Avx512.fd_f25519_eq

set_option maxHeartbeats 400000 in
set_option maxRecDepth 40000 in
theorem fd_ed25519_affine_is_small_order : fd_ed25519_affine_is_small_order_equivalent := by
  unfold fd_ed25519_affine_is_small_order_equivalent
  intro s a hrefwf ha haLimbs refResult
    s' a' g0' g1' hs' ha' hg0' hg1' hgp0 hgp1 hgv0 hgv1 hgr0 hgr1 hXr hYr avxResult hpoint

  -- ── ref: entry state, four locals, frames ────────────────────────────────
  have hs : s.WF := hrefwf.wf
  obtain ⟨g0, hgy0, -⟩ := hrefwf.gy0
  obtain ⟨g1, hgy1, -⟩ := hrefwf.gy1

  obtain ⟨xr, r1, hxrdef, hr1def, hr1, hxrfits, hxrid, hxroff, hctr1, -⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  obtain ⟨yr, r2, hyrdef, hr2def, hr2, hyrfits, hyrid, hyroff, hctr2, -⟩ :=
    GlobalState.exists_afterAlloca_facts r1 hr1 (5 * 64)
  obtain ⟨zr, r3, hzrdef, hr3def, hr3, hzrfits, hzrid, hzroff, hctr3, -⟩ :=
    GlobalState.exists_afterAlloca_facts r2 hr2 (5 * 64)
  obtain ⟨tr, r4, htrdef, hr4def, hr4, htrfits, htrid, htroff, hctr4, -⟩ :=
    GlobalState.exists_afterAlloca_facts r3 hr3 (5 * 64)

  have hxrge : s.alloc.nextFreeBlock ≤ xr.id.id := by omega
  have hyrge : s.alloc.nextFreeBlock ≤ yr.id.id := by omega
  have hzrge : s.alloc.nextFreeBlock ≤ zr.id.id := by omega
  have htrge : s.alloc.nextFreeBlock ≤ tr.id.id := by omega
  have hxrlt1 : xr.id.id < r1.alloc.nextFreeBlock := by omega
  have hyrlt2 : yr.id.id < r2.alloc.nextFreeBlock := by omega
  have hzrlt3 : zr.id.id < r3.alloc.nextFreeBlock := by omega

  have fbR1 : FrameBelow s.alloc.nextFreeBlock s r1 :=
    hr1def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have fbR2 : FrameBelow s.alloc.nextFreeBlock s r2 :=
    hr2def ▸ FrameBelow.afterAlloca (by omega) fbR1
  have fbR3 : FrameBelow s.alloc.nextFreeBlock s r3 :=
    hr3def ▸ FrameBelow.afterAlloca (by omega) fbR2
  have fbR4 : FrameBelow s.alloc.nextFreeBlock s r4 :=
    hr4def ▸ FrameBelow.afterAlloca (by omega) fbR3
  have fbr1 : FrameBelow r1.alloc.nextFreeBlock r1 r4 := by
    have h2 : FrameBelow r1.alloc.nextFreeBlock r1 r2 :=
      hr2def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h3 : FrameBelow r1.alloc.nextFreeBlock r1 r3 :=
      hr3def ▸ FrameBelow.afterAlloca (by omega) h2
    exact hr4def ▸ FrameBelow.afterAlloca (by omega) h3
  have fbr2 : FrameBelow r2.alloc.nextFreeBlock r2 r4 := by
    have h3 : FrameBelow r2.alloc.nextFreeBlock r2 r3 :=
      hr3def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    exact hr4def ▸ FrameBelow.afterAlloca (by omega) h3
  have fbr3 : FrameBelow r3.alloc.nextFreeBlock r3 r4 :=
    hr4def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)

  have hxr4 : Ref.IsFieldElemPtr r4.mem xr :=
    ⟨fits_of_live?_eq (fbr1 xr.id hxrlt1) hxrfits, by rw [hxroff]; simp⟩
  have hyr4 : Ref.IsFieldElemPtr r4.mem yr :=
    ⟨fits_of_live?_eq (fbr2 yr.id hyrlt2) hyrfits, by rw [hyroff]; simp⟩
  have hzr4 : Ref.IsFieldElemPtr r4.mem zr :=
    ⟨fits_of_live?_eq (fbr3 zr.id hzrlt3) hzrfits, by rw [hzroff]; simp⟩
  have htr4 : Ref.IsFieldElemPtr r4.mem tr := ⟨htrfits, by rw [htroff]; simp⟩

  have hold : ∀ r : Pointer, Ref.IsFieldElemPtr s.mem r → r.id.id < s.alloc.nextFreeBlock :=
    fun r hr => lt_nextFreeBlock_of_fits hs hr.left
  have halt : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.left
  have ha4 : Ref.IsPointPtr r4.mem a := Ref.isPointPtr_of_live?_eq (fbR4 a.id halt) ha
  have hNodupR : ([xr, yr, zr, tr, a].map Pointer.id).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    and_intros <;>
      first
        | exact fun h => absurd (congrArg BlockId.id h) (by omega)
        | exact id
  have hreadPt : Ref.readPoint ha4 = Ref.readPoint ha :=
    Ref.readPoint_of_live?_eq (fbR4 a.id halt) ha ha4
  have haLimbs4 : Ref.AllLimbBounds ha4 := by
    intro i
    show Ref.LimbBounds (Ref.isCoordPtr ha4 i)
    refine Ref.limbBounds_of_readLimb? _ (fun k l hl => ?_)
    rw [Ref.readLimb?_of_live?_eq (p := a.withOffset (i * (5 * 8))) (fbR4 a.id halt) k] at hl
    exact Ref.limbBounds_readLimb? (Ref.isCoordPtr ha i) (Ref.coordLimbBounds ha haLimbs i) k l hl

  -- ── avx512: entry state, four locals, frames ─────────────────────────────
  obtain ⟨xa, w1, hxadef, hw1def, hw1, hxafits, hxaid, hxaoff, hctw1, -⟩ :=
    GlobalState.exists_afterAlloca_facts s' hs' (8 * 64)
  obtain ⟨ya, w2, hyadef, hw2def, hw2, hyafits, hyaid, hyaoff, hctw2, -⟩ :=
    GlobalState.exists_afterAlloca_facts w1 hw1 (8 * 64)
  obtain ⟨za, w3, hzadef, hw3def, hw3, hzafits, hzaid, hzaoff, hctw3, -⟩ :=
    GlobalState.exists_afterAlloca_facts w2 hw2 (8 * 64)
  obtain ⟨ta, w4, htadef, hw4def, hw4, htafits, htaid, htaoff, hctw4, -⟩ :=
    GlobalState.exists_afterAlloca_facts w3 hw3 (8 * 64)

  have hxage : s'.alloc.nextFreeBlock ≤ xa.id.id := by omega
  have hyage : s'.alloc.nextFreeBlock ≤ ya.id.id := by omega
  have hzage : s'.alloc.nextFreeBlock ≤ za.id.id := by omega
  have htage : s'.alloc.nextFreeBlock ≤ ta.id.id := by omega
  have hxalt1 : xa.id.id < w1.alloc.nextFreeBlock := by omega
  have hyalt2 : ya.id.id < w2.alloc.nextFreeBlock := by omega
  have hzalt3 : za.id.id < w3.alloc.nextFreeBlock := by omega

  have fbA1 : FrameBelow s'.alloc.nextFreeBlock s' w1 :=
    hw1def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have fbA2 : FrameBelow s'.alloc.nextFreeBlock s' w2 :=
    hw2def ▸ FrameBelow.afterAlloca (by omega) fbA1
  have fbA3 : FrameBelow s'.alloc.nextFreeBlock s' w3 :=
    hw3def ▸ FrameBelow.afterAlloca (by omega) fbA2
  have fbA4 : FrameBelow s'.alloc.nextFreeBlock s' w4 :=
    hw4def ▸ FrameBelow.afterAlloca (by omega) fbA3
  have fbw1 : FrameBelow w1.alloc.nextFreeBlock w1 w4 := by
    have h2 : FrameBelow w1.alloc.nextFreeBlock w1 w2 :=
      hw2def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    have h3 : FrameBelow w1.alloc.nextFreeBlock w1 w3 :=
      hw3def ▸ FrameBelow.afterAlloca (by omega) h2
    exact hw4def ▸ FrameBelow.afterAlloca (by omega) h3
  have fbw2 : FrameBelow w2.alloc.nextFreeBlock w2 w4 := by
    have h3 : FrameBelow w2.alloc.nextFreeBlock w2 w3 :=
      hw3def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
    exact hw4def ▸ FrameBelow.afterAlloca (by omega) h3
  have fbw3 : FrameBelow w3.alloc.nextFreeBlock w3 w4 :=
    hw4def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)

  have hxa4 : Avx512.IsVecPtr w4.mem xa :=
    ⟨fits_of_live?_eq (fbw1 xa.id hxalt1) hxafits, by rw [hxaoff]; simp⟩
  have hya4 : Avx512.IsVecPtr w4.mem ya :=
    ⟨fits_of_live?_eq (fbw2 ya.id hyalt2) hyafits, by rw [hyaoff]; simp⟩
  have hza4 : Avx512.IsVecPtr w4.mem za :=
    ⟨fits_of_live?_eq (fbw3 za.id hzalt3) hzafits, by rw [hzaoff]; simp⟩
  have hta4 : Avx512.IsVecPtr w4.mem ta := ⟨htafits, by rw [htaoff]; simp⟩

  have hg0lt : g0'.id.id < s'.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs' hg0'.1
  have hg1lt : g1'.id.id < s'.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs' hg1'.1
  have halt' : a'.id.id < s'.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs' ha'.1
  have ha4' : Avx512.IsQuadPtr w4.mem a' := ⟨fits_of_live?_eq (fbA4 a'.id halt') ha'.1, ha'.2⟩
  have hq4 : Avx512.readQuad ha4' = Avx512.readQuad ha' :=
    Avx512.readQuad_of_live?_eq (fbA4 a'.id halt') ha' ha4'
  have hNodupA : ([xa, ya, za, ta].map Pointer.id).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    and_intros <;>
      first
        | exact fun h => absurd (congrArg BlockId.id h) (by omega)
        | exact id
  have hredX4 : R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X) := by
    rw [hq4]; exact hXr
  have hredY4 : R43x6.Reduced (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y) := by
    rw [hq4]; exact hYr

  -- ── the shared result, and the two `runFunction`s stripped ───────────────
  -- The region's own disjunction, in the association its three `or`s build,
  -- on the ref point. The ref walk reaches it directly; the AVX-512 walk
  -- reaches the same shape on its point, and `hpoint` identifies the two.
  suffices h : ∃ r : BitVec 32,
      (∃ sOut, StateT.run (runFunction (Ref.fd_ed25519_affine_is_small_order.denote
          (Ctxt.Valuation.singleton (.value a)))) s
        = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut) ∧ s ≈ sOut)
      ∧ (∃ sOut', StateT.run (runFunction (Avx512.fd_ed25519_affine_is_small_order.denote
          (Ctxt.Valuation.singleton (.value a')))) s'
        = .value ([(PoisonOr.value r : LLVM.IntW 32)]ₕ, sOut') ∧ s' ≈ sOut') by
    obtain ⟨r, ⟨sOut, hr, he⟩, ⟨sOut', hr', he'⟩⟩ := h
    exact ⟨r, sOut, sOut', hr, hr', he, he'⟩
  refine ⟨if (((Ref.readPoint ha).Y = 0 ∨ (Ref.readPoint ha).X = 0)
      ∨ (Ref.readPoint ha).Y = order8_y0) ∨ (Ref.readPoint ha).Y = order8_y1
    then 1#32 else 0#32, ?_⟩
  refine And.imp_left (run_runFunction' (s ≈ ·)) ?_
  refine And.imp_right (run_runFunction' (s' ≈ ·)) ?_
  simp only [Ref.fd_ed25519_affine_is_small_order, Avx512.fd_ed25519_affine_is_small_order,
    Cfg.denote]

  -- ── `%0`–`%16` and the lifetimes, both sides ─────────────────────────────
  focus_left
    denote_step_all v 5
    denote_eval v 0 0
    simp only [LLVM.const?] at hv0
    subst hv0
    peel_addressof hgy0.addr
    denote_step_all v 11
    peel_addressof hgy1.addr
    peel_alloca from s as r1 with hr1def
    peel_alloca from r1 as r2 with hr2def
    peel_alloca from r2 as r3 with hr3def
    peel_alloca from r3 as r4 with hr4def
    rw [← hxrdef, ← hyrdef, ← hzrdef, ← htrdef]
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
  focus_right
    denote_step_all u 5
    denote_eval u 0 0
    simp only [LLVM.const?] at hu0
    subst hu0
    peel_addressof hgp0
    denote_step_all u 11
    peel_addressof hgp1
    peel_alloca from s' as w1 with hw1def
    peel_alloca from w1 as w2 with hw2def
    peel_alloca from w2 as w3 with hw3def
    peel_alloca from w3 as w4 with hw4def
    rw [← hxadef, ← hyadef, ← hzadef, ← htadef]
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime

  -- ── `fd_ed25519_point_to( x, y, z, t, a )` ───────────────────────────────
  obtain ⟨oX, oY, oZ, oT, ⟨ptR, hptR, hptR_eq⟩, hlimbX, hlimbY, -, -, hvalX, hvalY, -, -⟩ :=
    Ref.fd_ed25519_point_to_conforms xr yr zr tr a r4 hr4 hNodupR ha4 hxr4 hyr4 hzr4 htr4
  obtain ⟨⟨ptA, hptA, hptA_eq⟩, hrX, hrY, -, -, hvX, hvY, -, -⟩ :=
    Avx512.fd_ed25519_point_to_conforms xa ya za ta a' w4 hw4 hNodupA ha4' hxa4 hya4 hza4 hta4
  focus_left
    peel_call hptR
  focus_right
    peel_call hptA

  -- ref: the copy's witnesses, transported to the state it left
  have hoXmR : Ref.IsFieldElemPtr
      ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) xr :=
    Ref.isFieldElemPtr_splice (p := tr) (x := oT) (Ref.isFieldElemPtr_splice (p := zr) (x := oZ)
      (Ref.isFieldElemPtr_splice (p := yr) (x := oY)
        (Ref.isFieldElemPtr_splice (p := xr) (x := oX) hxr4)))
  have hoYmR : Ref.IsFieldElemPtr
      ((((r4.mem.splice xr oX).splice yr oY).splice zr oZ).splice tr oT) yr :=
    Ref.isFieldElemPtr_splice (p := tr) (x := oT) (Ref.isFieldElemPtr_splice (p := zr) (x := oZ)
      (Ref.isFieldElemPtr_splice (p := yr) (x := oY)
        (Ref.isFieldElemPtr_splice (p := xr) (x := oX) hyr4)))
  have haXm : Ref.IsFieldElemPtr r4.mem a := Ref.coordPtr_zero a ▸ Ref.isCoordPtr ha4 0
  have haYm : Ref.IsFieldElemPtr r4.mem (a.withOffset 40) :=
    Ref.coordPtr_one a ▸ Ref.isCoordPtr ha4 1
  have hXlimb : ∀ i, Ref.readLimb i hoXmR = Ref.readLimb i haXm := hlimbX
  have hYlimb : ∀ i, Ref.readLimb i hoYmR = Ref.readLimb i haYm := hlimbY
  have hXvalOut : Ref.readFieldElem hoXmR = (Ref.readPoint ha4).X := hvalX
  have hYvalOut : Ref.readFieldElem hoYmR = (Ref.readPoint ha4).Y := hvalY
  have haXbnd : Ref.LimbBounds haXm :=
    Ref.limbBounds_congr (Ref.coordPtr_zero a) (Ref.coordLimbBounds ha4 haLimbs4 0)
  have haYbnd : Ref.LimbBounds haYm :=
    Ref.limbBounds_congr (Ref.coordPtr_one a) (Ref.coordLimbBounds ha4 haLimbs4 1)
  have hptWFR : ptR.WF := (wf_splice4 hr4).of_equiv hptR_eq
  have hxPtR : Ref.IsFieldElemPtr ptR.mem xr :=
    Ref.isFieldElemPtr_of_live?_eq (Ref.live?_of_equiv_mem hptR_eq.symm xr.id) hoXmR
  have hyPtR : Ref.IsFieldElemPtr ptR.mem yr :=
    Ref.isFieldElemPtr_of_live?_eq (Ref.live?_of_equiv_mem hptR_eq.symm yr.id) hoYmR
  have hxPtBndR : Ref.LimbBounds hxPtR := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hoXmR)
        (Ref.readLimb?_of_live?_eq (Ref.live?_of_equiv_mem hptR_eq.symm xr.id) i),
      hXlimb i]
    exact haXbnd i
  have hyPtBndR : Ref.LimbBounds hyPtR := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hoYmR)
        (Ref.readLimb?_of_live?_eq (Ref.live?_of_equiv_mem hptR_eq.symm yr.id) i),
      hYlimb i]
    exact haYbnd i
  have hxPtValR : Ref.readFieldElem? xr ptR.mem = some (Ref.readPoint ha).X :=
    (Ref.readFieldElem?_of_live?_eq (Ref.live?_of_equiv_mem hptR_eq.symm xr.id)).trans
      ((Option.some_get (Ref.readFieldElem?_isSome hoXmR)).symm.trans
        (congrArg some (hXvalOut.trans (congrArg Point.X hreadPt))))
  have hyPtValR : Ref.readFieldElem? yr ptR.mem = some (Ref.readPoint ha).Y :=
    (Ref.readFieldElem?_of_live?_eq (Ref.live?_of_equiv_mem hptR_eq.symm yr.id)).trans
      ((Option.some_get (Ref.readFieldElem?_isSome hoYmR)).symm.trans
        (congrArg some (hYvalOut.trans (congrArg Point.Y hreadPt))))
  have fbPtR : FrameBelow s.alloc.nextFreeBlock s ptR :=
    FrameBelow.of_equiv hptR_eq (frameBelow_splice4 fbR4 hxrge hyrge hzrge htrge)

  -- avx512: the same, over `vector<8xi64>` slots
  have hoXmA := Avx512.isVecPtr_splice (q := ta)
    (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))
    (Avx512.isVecPtr_splice (q := za)
      (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))
      (Avx512.isVecPtr_splice (q := ya)
        (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))
        (Avx512.isVecPtr_splice (q := xa)
          (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X)) hxa4)))
  have hoYmA := Avx512.isVecPtr_splice (q := ta)
    (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.T))
    (Avx512.isVecPtr_splice (q := za)
      (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Z))
      (Avx512.isVecPtr_splice (q := ya)
        (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y))
        (Avx512.isVecPtr_splice (q := xa)
          (x := Avx512.vecBV (Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X)) hya4)))
  have hptWFA : ptA.WF := (wf_splice4 hw4).of_equiv hptA_eq
  have fbPtA : FrameBelow s'.alloc.nextFreeBlock s' ptA :=
    FrameBelow.of_equiv hptA_eq (frameBelow_splice4 fbA4 hxage hyage hzage htage)
  have hxLive := live?_of_equiv_mem' hptA_eq.symm xa.id
  have hyLive := live?_of_equiv_mem' hptA_eq.symm ya.id
  have hxPtA : Avx512.IsVecPtr ptA.mem xa := ⟨fits_of_live?_eq hxLive hoXmA.1, hoXmA.2⟩
  have hyPtA : Avx512.IsVecPtr ptA.mem ya := ⟨fits_of_live?_eq hyLive hoYmA.1, hoYmA.2⟩
  have hxPtRead0 : Avx512.readVec hxPtA = Avx512.readVec hoXmA := by
    simp only [Avx512.readVec, Avx512.readVec?_of_live?_eq hxLive]
  have hyPtRead0 : Avx512.readVec hyPtA = Avx512.readVec hoYmA := by
    simp only [Avx512.readVec, Avx512.readVec?_of_live?_eq hyLive]
  have hxPtRead : Avx512.readVec hxPtA = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.X :=
    hxPtRead0.trans hrX
  have hyPtRead : Avx512.readVec hyPtA = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y :=
    hyPtRead0.trans hrY
  have hxPtValA : Avx512.vecValue (Avx512.readVec hxPtA) = (Avx512.readQuad ha').toPoint.X :=
    ((congrArg Avx512.vecValue hxPtRead0).trans hvX).trans (congrArg (fun w => w.toPoint.X) hq4)
  have hyPtValA : Avx512.vecValue (Avx512.readVec hyPtA) = (Avx512.readQuad ha').toPoint.Y :=
    ((congrArg Avx512.vecValue hyPtRead0).trans hvY).trans (congrArg (fun w => w.toPoint.Y) hq4)

  -- ── `fd_f25519_is_zero( x )` ─────────────────────────────────────────────
  obtain ⟨izXR, hizXR, hizXR_eq⟩ := Ref.fd_f25519_is_zero_conforms xr ptR hptWFR hxPtR hxPtBndR
  obtain ⟨izXA, hizXA, hizXA_eq⟩ :=
    Avx512.fd_f25519_is_zero_conforms xa ptA hptWFA hxPtA
      (by rw [hxPtRead]; exact hredX4.nearlyReduced)
      (by rw [hxPtRead]; rfl) (by rw [hxPtRead]; rfl)
  focus_left
    peel_call hizXR
  focus_right
    peel_call hizXA

  have hizXWFR : izXR.WF := hptWFR.of_equiv hizXR_eq
  have fbIzXR : FrameBelow s.alloc.nextFreeBlock s izXR := FrameBelow.of_equiv hizXR_eq fbPtR
  have hyIzXR : Ref.IsFieldElemPtr izXR.mem yr :=
    Ref.isFieldElemPtr_of_live?_eq (hizXR_eq.live yr.id).symm hyPtR
  have hyIzXBndR : Ref.LimbBounds hyIzXR := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hyPtR)
      (Ref.readLimb?_of_live?_eq (hizXR_eq.live yr.id).symm i)]
    exact hyPtBndR i
  have hyIzXValR : Ref.readFieldElem? yr izXR.mem = some (Ref.readPoint ha).Y :=
    (Ref.readFieldElem?_of_live?_eq (hizXR_eq.live yr.id).symm).trans hyPtValR

  have hizXWFA : izXA.WF := hptWFA.of_equiv hizXA_eq
  have fbIzXA : FrameBelow s'.alloc.nextFreeBlock s' izXA := FrameBelow.of_equiv hizXA_eq fbPtA
  have hyIzXA : Avx512.IsVecPtr izXA.mem ya := Avx512.isVecPtr_of_equiv hizXA_eq hyPtA
  have hyIzXRead : Avx512.readVec hyIzXA = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y :=
    (Avx512.readVec_of_equiv hizXA_eq hyPtA).trans hyPtRead
  have hyIzXValA : Avx512.vecValue (Avx512.readVec hyIzXA) = (Avx512.readQuad ha').toPoint.Y :=
    (congrArg Avx512.vecValue (Avx512.readVec_of_equiv hizXA_eq hyPtA)).trans hyPtValA

  -- ── `fd_f25519_is_zero( y )` ─────────────────────────────────────────────
  obtain ⟨izYR, hizYR, hizYR_eq⟩ :=
    Ref.fd_f25519_is_zero_conforms yr izXR hizXWFR hyIzXR hyIzXBndR
  obtain ⟨izYA, hizYA, hizYA_eq⟩ :=
    Avx512.fd_f25519_is_zero_conforms ya izXA hizXWFA hyIzXA
      (by rw [hyIzXRead]; exact hredY4.nearlyReduced)
      (by rw [hyIzXRead]; rfl) (by rw [hyIzXRead]; rfl)
  focus_left
    peel_call hizYR
  focus_right
    peel_call hizYA

  have hizYWFR : izYR.WF := hizXWFR.of_equiv hizYR_eq
  have fbIzYR : FrameBelow s.alloc.nextFreeBlock s izYR := FrameBelow.of_equiv hizYR_eq fbIzXR
  have hyIzYR : Ref.IsFieldElemPtr izYR.mem yr :=
    Ref.isFieldElemPtr_of_live?_eq (hizYR_eq.live yr.id).symm hyIzXR
  have hyIzYBndR : Ref.LimbBounds hyIzYR := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hyIzXR)
      (Ref.readLimb?_of_live?_eq (hizYR_eq.live yr.id).symm i)]
    exact hyIzXBndR i
  have hyIzYValR : Ref.readFieldElem? yr izYR.mem = some (Ref.readPoint ha).Y :=
    (Ref.readFieldElem?_of_live?_eq (hizYR_eq.live yr.id).symm).trans hyIzXValR
  have hg0IzYR : Ref.IsFieldElemPtr izYR.mem g0 :=
    Ref.isFieldElemPtr_of_live?_eq (fbIzYR g0.id (hold g0 hgy0.ptr)) hgy0.ptr
  have hg0IzYBndR : Ref.LimbBounds hg0IzYR := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hgy0.ptr)
      (Ref.readLimb?_of_live?_eq (fbIzYR g0.id (hold g0 hgy0.ptr)) i)]
    exact hgy0.bnd i
  have hg0IzYValR : Ref.readFieldElem? g0 izYR.mem = some order8_y0 :=
    (Ref.readFieldElem?_of_live?_eq (fbIzYR g0.id (hold g0 hgy0.ptr))).trans
      ((Option.some_get (Ref.readFieldElem?_isSome hgy0.ptr)).symm.trans
        (congrArg some hgy0.value))

  have hizYWFA : izYA.WF := hizXWFA.of_equiv hizYA_eq
  have fbIzYA : FrameBelow s'.alloc.nextFreeBlock s' izYA := FrameBelow.of_equiv hizYA_eq fbIzXA
  have hyIzYA : Avx512.IsVecPtr izYA.mem ya := Avx512.isVecPtr_of_equiv hizYA_eq hyIzXA
  have hyIzYRead : Avx512.readVec hyIzYA = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y :=
    (Avx512.readVec_of_equiv hizYA_eq hyIzXA).trans hyIzXRead
  have hyIzYValA : Avx512.vecValue (Avx512.readVec hyIzYA) = (Avx512.readQuad ha').toPoint.Y :=
    (congrArg Avx512.vecValue (Avx512.readVec_of_equiv hizYA_eq hyIzXA)).trans hyIzXValA
  have hg0IzYA : Avx512.IsVecPtr izYA.mem g0' :=
    ⟨fits_of_live?_eq (fbIzYA g0'.id hg0lt) hg0'.1, hg0'.2⟩
  have hg0IzYRead : Avx512.readVec hg0IzYA = Avx512.readVec hg0' := by
    simp only [Avx512.readVec, Avx512.readVec?_of_live?_eq (fbIzYA g0'.id hg0lt)]

  -- ── `%19 = or %18, %17` ──────────────────────────────────────────────────
  focus_left
    denote_step_all v 19
    denote_eval v 19 19
    simp only [LLVM.or, LLVM.or?] at hv19
    subst hv19
  focus_right
    denote_step_all u 19
    denote_eval u 19 19
    simp only [LLVM.or, LLVM.or?] at hu19
    subst hu19

  -- ── `fd_f25519_eq( y, y0 )` ──────────────────────────────────────────────
  obtain ⟨eq0R, heq0R, heq0R_eq⟩ :=
    Ref.fd_f25519_eq_conforms yr g0 izYR hizYWFR hyIzYR hg0IzYR hyIzYBndR
      (Ref.LimbBounds.bias hg0IzYBndR)
  obtain ⟨eq0A, heq0A, heq0A_eq⟩ :=
    Avx512.fd_f25519_eq_conforms ya g0' izYA hizYWFA hyIzYA hg0IzYA
      (by rw [hyIzYRead]; exact hredY4) (by rw [hg0IzYRead]; exact hgr0)
  focus_left
    peel_call heq0R
  focus_right
    peel_call heq0A

  have heq0WFR : eq0R.WF := hizYWFR.of_equiv heq0R_eq
  have fbEq0R : FrameBelow s.alloc.nextFreeBlock s eq0R := FrameBelow.of_equiv heq0R_eq fbIzYR
  have hyEq0R : Ref.IsFieldElemPtr eq0R.mem yr :=
    Ref.isFieldElemPtr_of_live?_eq (heq0R_eq.live yr.id).symm hyIzYR
  have hyEq0BndR : Ref.LimbBounds hyEq0R := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hyIzYR)
      (Ref.readLimb?_of_live?_eq (heq0R_eq.live yr.id).symm i)]
    exact hyIzYBndR i
  have hyEq0ValR : Ref.readFieldElem? yr eq0R.mem = some (Ref.readPoint ha).Y :=
    (Ref.readFieldElem?_of_live?_eq (heq0R_eq.live yr.id).symm).trans hyIzYValR
  have hg1Eq0R : Ref.IsFieldElemPtr eq0R.mem g1 :=
    Ref.isFieldElemPtr_of_live?_eq (fbEq0R g1.id (hold g1 hgy1.ptr)) hgy1.ptr
  have hg1Eq0BndR : Ref.LimbBounds hg1Eq0R := by
    intro i
    rw [Ref.readLimb_eq_of_readLimb? (h' := hgy1.ptr)
      (Ref.readLimb?_of_live?_eq (fbEq0R g1.id (hold g1 hgy1.ptr)) i)]
    exact hgy1.bnd i
  have hg1Eq0ValR : Ref.readFieldElem? g1 eq0R.mem = some order8_y1 :=
    (Ref.readFieldElem?_of_live?_eq (fbEq0R g1.id (hold g1 hgy1.ptr))).trans
      ((Option.some_get (Ref.readFieldElem?_isSome hgy1.ptr)).symm.trans
        (congrArg some hgy1.value))

  have heq0WFA : eq0A.WF := hizYWFA.of_equiv heq0A_eq
  have fbEq0A : FrameBelow s'.alloc.nextFreeBlock s' eq0A := FrameBelow.of_equiv heq0A_eq fbIzYA
  have hyEq0A : Avx512.IsVecPtr eq0A.mem ya := Avx512.isVecPtr_of_equiv heq0A_eq hyIzYA
  have hyEq0Read : Avx512.readVec hyEq0A = Avx512.widenVec (Avx512.readQuad ha4').PointVecs.Y :=
    (Avx512.readVec_of_equiv heq0A_eq hyIzYA).trans hyIzYRead
  have hyEq0ValA : Avx512.vecValue (Avx512.readVec hyEq0A) = (Avx512.readQuad ha').toPoint.Y :=
    (congrArg Avx512.vecValue (Avx512.readVec_of_equiv heq0A_eq hyIzYA)).trans hyIzYValA
  have hg1Eq0A : Avx512.IsVecPtr eq0A.mem g1' :=
    ⟨fits_of_live?_eq (fbEq0A g1'.id hg1lt) hg1'.1, hg1'.2⟩
  have hg1Eq0Read : Avx512.readVec hg1Eq0A = Avx512.readVec hg1' := by
    simp only [Avx512.readVec, Avx512.readVec?_of_live?_eq (fbEq0A g1'.id hg1lt)]

  -- ── `%21 = or %19, %20` ──────────────────────────────────────────────────
  focus_left
    denote_step_all v 21
    denote_eval v 21 21
    simp only [LLVM.or, LLVM.or?] at hv21
    subst hv21
  focus_right
    denote_step_all u 21
    denote_eval u 21 21
    simp only [LLVM.or, LLVM.or?] at hu21
    subst hu21

  -- ── `fd_f25519_eq( y, y1 )` ──────────────────────────────────────────────
  obtain ⟨eq1R, heq1R, heq1R_eq⟩ :=
    Ref.fd_f25519_eq_conforms yr g1 eq0R heq0WFR hyEq0R hg1Eq0R hyEq0BndR
      (Ref.LimbBounds.bias hg1Eq0BndR)
  obtain ⟨eq1A, heq1A, heq1A_eq⟩ :=
    Avx512.fd_f25519_eq_conforms ya g1' eq0A heq0WFA hyEq0A hg1Eq0A
      (by rw [hyEq0Read]; exact hredY4) (by rw [hg1Eq0Read]; exact hgr1)
  focus_left
    peel_call heq1R
  focus_right
    peel_call heq1A
  have fbEq1R : FrameBelow s.alloc.nextFreeBlock s eq1R := FrameBelow.of_equiv heq1R_eq fbEq0R
  have fbEq1A : FrameBelow s'.alloc.nextFreeBlock s' eq1A := FrameBelow.of_equiv heq1A_eq fbEq0A

  -- ── the two returns ──────────────────────────────────────────────────────
  -- Everything relational is established; the last `or`, the lifetimes and
  -- the return are one plain walk per side, meeting on `hpoint`.
  refine ⟨⟨eq1R, ?_, GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs fbEq1R)⟩,
    ⟨eq1A, ?_, GlobalState.Equiv.symm (FrameBelow.popFrame_equiv hs' fbEq1A)⟩⟩
  · denote_step_all v 23
    denote_eval v 23 23
    simp only [LLVM.or, LLVM.or?] at hv23
    subst hv23
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
    simp_return
    rw [hxPtValR, hyIzXValR, Ref.readFieldElem_eq_of hyIzYValR, Ref.readFieldElem_eq_of hg0IzYValR,
      Ref.readFieldElem_eq_of hyEq0ValR, Ref.readFieldElem_eq_of hg1Eq0ValR]
    simp only [Option.some.injEq, or_ite_or]
  · denote_step_all u 23
    denote_eval u 23 23
    simp only [LLVM.or, LLVM.or?] at hu23
    subst hu23
    peel_lifetime
    peel_lifetime
    peel_lifetime
    peel_lifetime
    simp_return
    rw [hxPtValA, hyIzXValA, hyIzYValA, hyEq0ValA, congrArg Avx512.vecValue hg0IzYRead,
      congrArg Avx512.vecValue hg1Eq0Read, hgv0, hgv1]
    simp only [or_ite_or]
    rw [hpoint]

end Firedancer
