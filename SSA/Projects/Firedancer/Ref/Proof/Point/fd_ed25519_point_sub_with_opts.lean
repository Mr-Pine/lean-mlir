/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_add_with_opts

/-!
# `fd_ed25519_point_sub_with_opts` conformance (ref)

The add walk with `b`'s `X` and `Y` exchanged at `^bb2` and `add_nr`/`sub_nr`
exchanged for `Y` and `Z` at `^bb8`; the step lemmas are add's.
-/

namespace Firedancer.Ref

-- v4.34: the literal blocks a walk enters are indexed by `Γout` unfolded
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] fd_ed25519_point_sub_with_opts
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

attribute [local irreducible] fd_f25519_add fd_f25519_add_nr fd_f25519_sub_nr fd_f25519_mul3
  fd_f25519_mul4 fd_f25519_mul

namespace SubWithOpts
open AddWithOpts

/-! ### `^bb5 … ^bb10` -/

/-- The tail both `b_Z_is_one` paths reach: `^bb5` and `^bb7` fall through to
`^bb8`, which stores `(r6 - r5, r8 + r7, r8 - r7, r6 + r5)` into `r`. -/
theorem tail_run {s w : GlobalState} {r : Pointer} (hs : s.WF) (hr : IsPointPtr s.mem r)
    (hnr : r.id.id < s.alloc.nextFreeBlock)
    (V : fd_ed25519_point_sub_with_opts.Γout.Valuation)
    (hv1 : V (⟨1, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var (SLLVM.Ty.bitvec 1))
      = .value 0#1)
    (hv15 : V (⟨15, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var (SLLVM.Ty.bitvec 32))
      = .value 0#32)
    (hv17 : V (⟨17, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var (SLLVM.Ty.bitvec 32))
      = .value 1#32)
    (hv22 : V (⟨22, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var SLLVM.Ty.ptr) = .value r)
    (hv9 : V (⟨9, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var SLLVM.Ty.ptr)
      = .value (addLocal s 4))
    (hv8 : V (⟨8, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var SLLVM.Ty.ptr)
      = .value (addLocal s 5))
    (hv7 : V (⟨7, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var SLLVM.Ty.ptr)
      = .value (addLocal s 6))
    (hv6 : V (⟨6, by rfl⟩ : fd_ed25519_point_sub_with_opts.Γout.Var SLLVM.Ty.ptr)
      = .value (addLocal s 7))
    (F : Frame s w) {A B C D : ZMod _root_.p}
    (hA : Holds w.mem (addLocal s 4) A 0x8000000000000)
    (hB : Holds w.mem (addLocal s 5) B 0x8000000000000)
    (hC : Holds w.mem (addLocal s 6) C 0x8000000000000)
    (hD : Holds w.mem (addLocal s 7) D 0x8000000000000)
    (Pt : Point) (hPt : Pt = ⟨B - A, D + C, D - C, B + A⟩) :
    ∃ s' : GlobalState,
      StateT.run (fd_ed25519_point_sub_with_opts.blocks.run V ⟨4, by rfl, HVector.nil⟩) w
        = .value ([.value r]ₕ, s')
      ∧ ∃ oX oY oZ oT : BitVec (5 * 64),
        let outMem := (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
          (r.withOffset 120) oZ).splice (r.withOffset 80) oT
        have hpt : IsPointPtr outMem r :=
          isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
        ({ s with mem := outMem } : GlobalState) ≈ s.popFrame s'.mem
        ∧ readPoint hpt = Pt ∧ ∀ i, LimbBounds.Loose (isCoordPtr hpt i) := by
  have hmapnil : ∀ {α : Type} {A B : α → Type} (f : (a : α) → A a → B a),
      HVector.map f (.nil : HVector A []) = .nil := fun _ => rfl
  -- `^bb5`: `b_is_precomputed ≠ 0`, so no `mul` by `k`
  denote_enter_block
  reduce_list_lits
  simp only [BlockCom.denote_term]
  rw [Terminator.denote_condBr_value (b := 0#1) (by exact hv1)]
  simp only [simp_denote, simp_sllvm]
  rw [if_neg (by decide : ¬ ((0#1 : BitVec 1) = 1))]

  -- `^bb7`: `skip_last_mul ≠ 0`
  denote_enter_block
  reduce_list_lits
  denote_number_from 32
  denote_step_reduce v 32 [LLVM.icmp, LLVM.icmp?, LLVM.icmp']
  have e32 : v32 = .value 0#1 := by simp only [hv32, hv17, hv15]; rfl
  simp only [BlockCom.denote_term]
  rw [Terminator.denote_condBr_value (b := 0#1) (by exact e32)]
  simp only [simp_denote, simp_sllvm]
  rw [if_neg (by decide : ¬ ((0#1 : BitVec 1) = 1))]

  -- `^bb8`: `X = r6 - r5`
  denote_enter_block
  reduce_list_lits
  denote_number_from 33
  have hr0 : IsFieldElemPtr w.mem r :=
    isFieldElemPtr_of_live?_eq (F.live r.id hnr) (coordPtr_zero r ▸ isCoordPtr hr 0)
  refine subNr_step F.wf hr0 hB hA
    fun w₁ hrun₁ st₁ HX => ?_
  peel_call hrun₁ with hmapnil, Target.denote, hv22, hv8, hv9
  have hl₁ : ∀ k : Fin 9, w₁.mem.live? (addLocal s k).id = w.mem.live? (addLocal s k).id :=
    fun _ => st₁.live _ (Ne.symm (fieldLocal_ne_below hnr))

  -- `%34`, `%35`: `Y = r8 + r7`
  denote_step_reduce v 34 [gepConst, ptradd, LLVM.const?, hmapnil, Target.denote, hv22]
  have e34 : v34 = .value (r.withOffset 40) := hv34
  subst e34
  clear hv34
  have hr1 : IsFieldElemPtr w₁.mem (r.withOffset 40) :=
    st₁.isFieldElemPtr (isFieldElemPtr_of_live?_eq (F.live r.id hnr) (isCoordPtr hr 1))
  refine addNr_step st₁.wf hr1 (hD.carry (hl₁ 7)) (hC.carry (hl₁ 6))
    fun w₂ hrun₂ st₂ HY => ?_
  peel_call hrun₂ with hmapnil, Target.denote, Ctxt.Valuation.cons_zero, hv7, hv6
  have hl₂ : ∀ k : Fin 9, w₂.mem.live? (addLocal s k).id = w₁.mem.live? (addLocal s k).id :=
    fun _ => st₂.live _ (Ne.symm (fieldLocal_ne_below hnr))

  -- `%36`, `%37`: `Z = r8 - r7`
  denote_step_reduce v 36 [gepConst, ptradd, LLVM.const?, hmapnil, Target.denote, hv22]
  have e36 : v36 = .value (r.withOffset 120) := hv36
  subst e36
  clear hv36
  have hr3 : IsFieldElemPtr w₂.mem (r.withOffset 120) :=
    st₂.isFieldElemPtr (st₁.isFieldElemPtr
      (isFieldElemPtr_of_live?_eq (F.live r.id hnr) (isCoordPtr hr 3)))
  refine subNr_step st₂.wf hr3 ((hD.carry (hl₁ 7)).carry (hl₂ 7))
    ((hC.carry (hl₁ 6)).carry (hl₂ 6)) fun w₃ hrun₃ st₃ HZ => ?_
  peel_call hrun₃ with hmapnil, Target.denote, Ctxt.Valuation.cons_zero, hv7, hv6
  have hl₃ : ∀ k : Fin 9, w₃.mem.live? (addLocal s k).id = w₂.mem.live? (addLocal s k).id :=
    fun _ => st₃.live _ (Ne.symm (fieldLocal_ne_below hnr))

  -- `%38`, `%39`: `T = r6 + r5`
  denote_step_reduce v 38 [gepConst, ptradd, LLVM.const?, hmapnil, Target.denote, hv22]
  have e38 : v38 = .value (r.withOffset 80) := hv38
  subst e38
  clear hv38
  have hr2 : IsFieldElemPtr w₃.mem (r.withOffset 80) :=
    st₃.isFieldElemPtr (st₂.isFieldElemPtr (st₁.isFieldElemPtr
      (isFieldElemPtr_of_live?_eq (F.live r.id hnr) (isCoordPtr hr 2))))
  refine addNr_step st₃.wf hr2 (((hB.carry (hl₁ 5)).carry (hl₂ 5)).carry (hl₃ 5))
      (((hA.carry (hl₁ 4)).carry (hl₂ 4)).carry (hl₃ 4))
    fun w₄ hrun₄ st₄ HT => ?_
  peel_call hrun₄ with hmapnil, Target.denote, Ctxt.Valuation.cons_zero, hv8, hv9

  -- `^bb10`
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
  denote_enter_block
  reduce_list_lits
  iterate 9 peel_lifetime
  simp_return
  simp [hv22]

  /- The region has returned: `r`'s block as the four stores left it. -/
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := hr.2; simp; omega)
  obtain ⟨xX, hxX⟩ := st₁.splice
  obtain ⟨xY, hxY⟩ := st₂.splice
  obtain ⟨xZ, hxZ⟩ := st₃.splice
  obtain ⟨xT, hxT⟩ := st₄.splice
  have k1 : w₁.mem.live? r.id = (s.mem.splice r xX).live? r.id :=
    hxX.trans (live?_splice_congr (p := r) (x := xX) (F.live r.id hnr))
  have k2 : w₂.mem.live? r.id = ((s.mem.splice r xX).splice (r.withOffset 40) xY).live? r.id :=
    hxY.trans (live?_splice_congr (p := r.withOffset 40) (x := xY) k1)
  have k3 : w₃.mem.live? r.id = (((s.mem.splice r xX).splice (r.withOffset 40) xY).splice
      (r.withOffset 120) xZ).live? r.id :=
    hxZ.trans (live?_splice_congr (p := r.withOffset 120) (x := xZ) k2)
  have k4 : w₄.mem.live? r.id = ((((s.mem.splice r xX).splice (r.withOffset 40) xY).splice
      (r.withOffset 120) xZ).splice (r.withOffset 80) xT).live? r.id :=
    hxT.trans (live?_splice_congr (p := r.withOffset 80) (x := xT) k3)
  have hpop := popFrame_equiv_block hs hnr
    (fun b hb hbr =>
      have h : r.id ≠ b := fun h => hbr h.symm
      (st₄.live b h).trans ((st₃.live b h).trans ((st₂.live b h).trans
        ((st₁.live b h).trans (F.live b hb)))))
    (fun b hbr =>
      have h : r.id ≠ b := fun h => hbr h.symm
      (live?_splice_ne (p := r.withOffset 80) h).trans
        ((live?_splice_ne (p := r.withOffset 120) h).trans
          ((live?_splice_ne (p := r.withOffset 40) h).trans (live?_splice_ne (p := r) h))))
    k4
  have OX := (((HX.carry k1.symm).splice (d := r.withOffset 40) (x := xY)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 120) (x := xZ)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 80) (x := xT) (.inr (.inr (by omega)))
  have OY := ((HY.carry k2.symm).splice (d := r.withOffset 120) (x := xZ)
    (.inr (.inr (by omega)))).splice (d := r.withOffset 80) (x := xT) (.inr (.inr (by omega)))
  have OZ := (HZ.carry k3.symm).splice (d := r.withOffset 80) (x := xT) (.inr (.inl (by omega)))
  have OT := HT.carry k4.symm
  refine ⟨xX, xY, xZ, xT, GlobalState.Equiv.symm hpop,
    (readPoint_eq_of _ OX.val OY.val OT.val OZ.val).trans hPt.symm, fun i => ?_⟩
  fin_cases i
  · exact limbBounds_congr' (coordPtr_zero r).symm OX.bnd
  · exact OY.bnd
  · exact OT.bnd
  · exact OZ.bnd

end SubWithOpts

open AddWithOpts in
theorem fd_ed25519_point_sub_with_opts_conforms (r a b : Pointer) (bZ1 bPre skip : BitVec 32)
    (s : GlobalState) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a)
    (hb : IsPointPtr s.mem b) :
    fd_ed25519_point_sub_with_opts_spec r a b bZ1 bPre skip s hr ha hb := by
  simp only [fd_ed25519_point_sub_with_opts_spec, Cfg.denote]
  intro hpre hskip hm haX haY haT haZ hbB
  subst hpre hskip
  have hs := hm.wf
  obtain ⟨pk, hgk, -⟩ := hm.gk
  refine run_runFunction' _ ?_
  denote_step_reduce v 1 [LLVM.const?] fold
  peel_addressof hgk.addr

  have hnr : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.left
  have hna : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.left
  have hnb : b.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hb.left
  have fb : FrameBelow s.alloc.nextFreeBlock s (s.allocaChain fieldW 9) :=
    FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 9
  have hwf : (s.allocaChain fieldW 9).WF := GlobalState.WF.allocaChain hs 9
  have hlf : ∀ k : Fin 9, Fits (s.allocaChain fieldW 9).mem (addLocal s k) 320 :=
    fun k => GlobalState.fits_chainPtr k.isLt
  set sL : GlobalState := s.allocaChain fieldW 9 with hsL
  clear_value sL

  -- `%3 … %11`: `r1 … r8, t`
  peel_alloca_chain s, fieldW, 9
  fold_cells s, fieldW, addLocal, 9
  rw [← hsL]
  iterate 9 peel_lifetime

  -- `%12`: `a->Y`
  denote_step_reduce v 12 [gepConst, ptradd, LLVM.const?]
  have e12 : v12 = .value (a.withOffset 40) := hv12
  subst e12
  clear hv12

  have F₀ : Frame s sL := ⟨hwf, fun k => ⟨hlf k, by simp [addLocal, fieldLocal]⟩, fb⟩
  -- the operands' coordinates, on entry
  have hca : IsFieldElemPtr s.mem a := coordPtr_zero a ▸ isCoordPtr ha 0
  have hPa := readPoint_eq_of ha (h0 := hca) (h1 := isCoordPtr ha 1)
    (h2 := isCoordPtr ha 2) (h3 := isCoordPtr ha 3) rfl rfl rfl rfl
  have hX : Holds s.mem a (readPoint ha).X 0x8000000000000 :=
    ⟨hca, (congrArg Point.X hPa).symm, limbBounds_congr (coordPtr_zero a) haX⟩
  have hY : Holds s.mem (a.withOffset 40) (readPoint ha).Y 0x8000000000000 :=
    ⟨_, (congrArg Point.Y hPa).symm, haY⟩

  -- `%13`: `r1 = a->Y - a->X`
  refine subNr_step F₀.wf (F₀.locals 0) (F₀.caller hY hna) (F₀.caller hX hna)
    fun u₁ hrun₁ st₁ H1 => ?_
  peel_call hrun₁
  have F₁ := F₀.stepLocal st₁

  -- `%14`: `r3 = a->Y + a->X`
  refine addNr_step F₁.wf (F₁.locals 2) (F₁.caller hY hna) (F₁.caller hX hna)
    fun u₂ hrun₂ st₂ H3 => ?_
  peel_call hrun₂
  have F₂ := F₁.stepLocal st₂
  have H1₂ := H1.carry (st₂.live _ (fieldLocal_ne (by decide)))

  -- `%15`, `%16`
  denote_step_reduce v 16 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', gepConst, ptradd, LLVM.const?, hv1]
  have e16 : v16 = .value (b.withOffset 40) := hv16
  subst e16
  clear hv16
  simp only [hv15, BlockCom.denote_term, Terminator.denote_condBr_value, simp_denote, simp_sllvm]
  rw [if_neg (by decide : ¬ ((0#1 : BitVec 1) = 1))]

  -- `^bb2(b->Y, b)`: branch on `b_Z_is_one`
  denote_enter_block
  reduce_list_lits
  denote_number_from 21
  denote_step_reduce v 21 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hv1]
  simp only [BlockCom.denote_term]
  rw [Terminator.denote_condBr_value (by exact hv21)]
  simp only [simp_denote, simp_sllvm]

  -- the remaining coordinates, on entry
  have hT : Holds s.mem (a.withOffset 80) (readPoint ha).T 0x18000000000000 :=
    ⟨_, (congrArg Point.T hPa).symm, haT⟩
  have hZ : Holds s.mem (a.withOffset 120) (readPoint ha).Z 0x8000000000000 :=
    ⟨_, (congrArg Point.Z hPa).symm, haZ⟩
  have hcb : IsFieldElemPtr s.mem b := coordPtr_zero b ▸ isCoordPtr hb 0
  have hPb := readPoint_eq_of hb (h0 := hcb) (h1 := isCoordPtr hb 1)
    (h2 := isCoordPtr hb 2) (h3 := isCoordPtr hb 3) rfl rfl rfl rfl
  have hbX : Holds s.mem b (readPoint hb).X 0x18000000000000 :=
    ⟨hcb, (congrArg Point.X hPb).symm, limbBounds_congr' (coordPtr_zero b) (hbB 0)⟩
  have hbY : Holds s.mem (b.withOffset 40) (readPoint hb).Y 0x18000000000000 :=
    ⟨_, (congrArg Point.Y hPb).symm, hbB 1⟩
  have hbT : Holds s.mem (b.withOffset 80) (readPoint hb).T 0x18000000000000 :=
    ⟨_, (congrArg Point.T hPb).symm, hbB 2⟩
  have hbZ : Holds s.mem (b.withOffset 120) (readPoint hb).Z 0x18000000000000 :=
    ⟨_, (congrArg Point.Z hPb).symm, hbB 3⟩

  by_cases hz : bZ1 = 0
  · -- `^bb4`: `t = 2 a->Z`, then four `mul`s, the last by `b->Z`
    rw [if_pos (by simp [hz] : BitVec.ofBool (bZ1 == 0#32) = 1)]
    denote_enter_block
    reduce_list_lits
    denote_number_from 26
    denote_step_reduce v 26 [gepConst, ptradd, LLVM.const?]
    have e26 : v26 = .value (a.withOffset 120) := hv26
    subst e26
    clear hv26
    refine addNr_step F₂.wf (F₂.locals 8) (F₂.caller hZ hna) (F₂.caller hZ hna)
      fun u₃ hrun₃ st₃ H8 => ?_
    peel_call hrun₃
    have F₃ := F₂.stepLocal st₃

    -- `%28 … %30`, then `mul4( r5, r1, b->Y, r6, r3, b->X, r7, a->T, b->T, r8, t, b->Z )`
    denote_step_reduce v 30 [gepConst, ptradd, LLVM.const?]
    have e28 : v28 = .value (a.withOffset 80) := hv28
    have e29 : v29 = .value (b.withOffset 80) := hv29
    have e30 : v30 = .value (b.withOffset 120) := hv30
    subst e28 e29 e30
    clear hv28 hv29 hv30
    have hsrc : ∀ d ∈ [addLocal s 4, addLocal s 5, addLocal s 6, addLocal s 7],
        ∀ x ∈ [addLocal s 0, b.withOffset 40, addLocal s 2, b, a.withOffset 80, b.withOffset 80,
          addLocal s 8, b.withOffset 120], d.id ≠ x.id := by
      intro d hd x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd hx
      rcases hd with rfl | rfl | rfl | rfl <;>
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact fieldLocal_ne (by decide)
          | exact fieldLocal_ne_below hnb
          | exact fieldLocal_ne_below hna
    refine mul4_step F₃.wf (locals_pairwise s (ks := [4, 5, 6, 7]) (by decide) :
          [addLocal s 4, addLocal s 5, addLocal s 6, addLocal s 7].Pairwise FieldApart) hsrc
        (F₃.locals 4) (F₃.locals 5) (F₃.locals 6) (F₃.locals 7)
        (H1₂.carry (st₃.live _ (fieldLocal_ne (by decide)))) (F₃.caller hbY hnb)
        (H3.carry (st₃.live _ (fieldLocal_ne (by decide)))) (F₃.caller hbX hnb)
        (F₃.caller hT hna) (F₃.caller hbT hnb) H8 (F₃.caller hbZ hnb)
      fun u₄ hrun₄ hwf₄ hptr₄ hlive₄ R5 R6 R7 R8 => ?_
    peel_call hrun₄
    have F₄ : Frame s u₄ := F₃.step hwf₄ hptr₄ fun blk hblk =>
      hlive₄ blk (fieldLocal_ne_below hblk) (fieldLocal_ne_below hblk)
        (fieldLocal_ne_below hblk) (fieldLocal_ne_below hblk)

    -- `br ^bb5`
    simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
    refine SubWithOpts.tail_run hs hr hnr _ rfl (by exact hv1) rfl rfl rfl rfl rfl rfl F₄
      R5 R6 R7 R8 _ ?_
    rw [if_pos hz]
    simp only [Point.addPrecomputedPartial, PrecomputedPoint.ofSlots, PrecomputedPoint.neg]
    congr 1 <;> ring
  · -- `^bb3`: `b->Z` is taken as 1: three `mul`s, and `r8 = 2 a->Z`
    have hz' : (bZ1 == 0#32) = false := by simpa using hz
    rw [hz', if_neg (by decide)]
    denote_enter_block
    reduce_list_lits
    denote_number_from 22
    denote_step_reduce v 23 [gepConst, ptradd, LLVM.const?]
    have e22 : v22 = .value (a.withOffset 80) := hv22
    have e23 : v23 = .value (b.withOffset 80) := hv23
    subst e22 e23
    clear hv22 hv23
    have hsrc : ∀ d ∈ [addLocal s 4, addLocal s 5, addLocal s 6],
        ∀ x ∈ [addLocal s 0, b.withOffset 40, addLocal s 2, b, a.withOffset 80, b.withOffset 80],
          d.id ≠ x.id := by
      intro d hd x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd hx
      rcases hd with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact fieldLocal_ne (by decide)
          | exact fieldLocal_ne_below hnb
          | exact fieldLocal_ne_below hna
    -- `mul3( r5, r1, b->Y, r6, r3, b->X, r7, a->T, b->T )`
    refine mul3_step F₂.wf (locals_pairwise s (ks := [4, 5, 6]) (by decide) :
          [addLocal s 4, addLocal s 5, addLocal s 6].Pairwise FieldApart) hsrc
        (F₂.locals 4) (F₂.locals 5) (F₂.locals 6) H1₂ (F₂.caller hbY hnb) H3
        (F₂.caller hbX hnb) (F₂.caller hT hna) (F₂.caller hbT hnb)
      fun u₃ hrun₃ hwf₃ hptr₃ hlive₃ R5 R6 R7 => ?_
    peel_call hrun₃
    have F₃ : Frame s u₃ := F₂.step hwf₃ hptr₃ fun blk hblk =>
      hlive₃ blk (fieldLocal_ne_below hblk) (fieldLocal_ne_below hblk) (fieldLocal_ne_below hblk)

    -- `%24`, `%25`: `r8 = a->Z + a->Z`
    denote_step_reduce v 24 [gepConst, ptradd, LLVM.const?]
    have e24 : v24 = .value (a.withOffset 120) := hv24
    subst e24
    clear hv24
    refine add_step' F₃.wf (F₃.locals 7) (F₃.caller hZ hna) (F₃.caller hZ hna)
      fun u₄ hrun₄ st₄ R8 => ?_
    peel_call hrun₄
    have F₄ := F₃.stepLocal st₄

    -- `br ^bb5`
    simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
    refine SubWithOpts.tail_run hs hr hnr _ rfl (by exact hv1) rfl rfl rfl rfl rfl rfl F₄
      (R5.carry (st₄.live _ (fieldLocal_ne (by decide))))
      (R6.carry (st₄.live _ (fieldLocal_ne (by decide))))
      (R7.carry (st₄.live _ (fieldLocal_ne (by decide)))) R8 _ ?_
    rw [if_neg hz]
    simp only [Point.addPrecomputedPartial, PrecomputedPoint.ofSlots, PrecomputedPoint.neg]
    congr 1 <;> ring

end Firedancer.Ref
