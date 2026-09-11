/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_wnaf
import SSA.Projects.Firedancer.Common.Proof.Scalar.fd_int_min
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_wnaf` writes nowhere but `slides`

The region loops, and what it computes is irrelevant here, so the proof is an
invariant rather than a walk: `Blocks.run_inv` is partial correctness for a
block walk -- if every block keeps `Reach` and a returning block meets `Done`,
any run that returns ends in `Done`. Poison is never ruled out; a step that
might trap is split on it and the poison side closes vacuously.

`Reach` has one constructor per tail block. Each says the state is the entry
state with some `w : BitVec 4096` spliced at `slides` (`Sw`), and pins only
what the next stores need: the indices the region stores through, as small
naturals, and the sentinel

    slot w 255 = 0 ∨ i = 255

at the outer loop head. That disjunction is the C comment's argument made
checkable: the carry scan in `^bb14`/`^bb18` only continues past a set entry,
and entry 255 is clear whenever `i < 255`, so every index it stores through
stays at most 255.

The scalar's bytes are loaded but never inspected, so a load there is only
"traps, or returns something and leaves the state" (`load_cases_cont`) and no
hypothesis about `n` is needed.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- Partial correctness of a block walk. -/
theorem _root_.LeanMLIR.SLLVM.Blocks.run_inv {Γamb : Ctxt SLLVM.Ty}
    {rets : List SLLVM.Ty} {all : List (List SLLVM.Ty)}
    {bs : Blocks Γamb rets all all} {Vamb : Γamb.Valuation}
    (Inv : SuccArgs all → GlobalState → Prop)
    (Q : HVector toType rets → GlobalState → Prop)
    (hstep : ∀ t s, Inv t s → ∃ res,
      StateT.run ((bs.get t.idx t.hidx).2.denote
          (Ctxt.Valuation.ofHVector t.args.reverse ++ Vamb)) s = res ∧ ∀ p s',
      res = .value (p, s') →
      (∀ rs, p.2 = .inl rs → Q rs s') ∧ (∀ t', p.2 = .inr t' → Inv t' s'))
    {t₀ : SuccArgs all} {s₀ : GlobalState} (h₀ : Inv t₀ s₀) :
    ∀ rs s', StateT.run (bs.run Vamb t₀) s₀ = .value (rs, s') → Q rs s' := by
  intro rs s' h
  rw [Blocks.run_eq_limit] at h
  cases hl : Fuel.limit (fun n => bs.iterate n Vamb t₀ s₀) with
  | none => rw [hl, Fuel.force_none] at h; exact absurd h.symm (PoisonOr.value_ne_poison _)
  | some r =>
    rw [hl, Fuel.force_some] at h
    subst h
    obtain ⟨n, hn⟩ := Fuel.exists_of_limit_eq_some hl
    clear hl
    induction n generalizing t₀ s₀ with
    | zero => rw [Blocks.iterate] at hn; exact absurd hn (by simp)
    | succ n ih =>
      rw [Blocks.iterate] at hn
      cases he : (bs.get t₀.idx t₀.hidx).2.eval n
          (Ctxt.Valuation.ofHVector t₀.args.reverse ++ Vamb) s₀ with
      | none => rw [he] at hn; exact absurd hn (by simp)
      | some r' =>
        rw [he] at hn
        have hd := (bs.get t₀.idx t₀.hidx).2.run_denote
          (Ctxt.Valuation.ofHVector t₀.args.reverse ++ Vamb) s₀
        rw [Fuel.limit_eq_of BlockCom.eval_mono he, Fuel.force_some] at hd
        cases r' with
        | poison => exact absurd (Option.some.inj hn).symm (PoisonOr.value_ne_poison _)
        | value p =>
          rw [Fuel.andThen_value] at hn
          obtain ⟨res, hres, hpost⟩ := hstep t₀ s₀ h₀
          have hpost := hpost p.1 p.2 (hres.symm.trans hd)
          obtain ⟨⟨V', r''⟩, u⟩ := p
          cases r'' with
          | inl rs' =>
            rw [Blocks.next] at hn
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (PoisonOr.value_inj.mp (Option.some.inj hn))
            exact hpost.1 _ rfl
          | inr t' =>
            rw [Blocks.next] at hn
            exact ih (hpost.2 t' rfl) hn

namespace Wnaf

/-! ## The buffer model

Every state the walk reaches is the entry state with some 4096 bits `w` at
`slides`; `slot w k` is entry `k` of them. -/

/-- The entry state with `w` written over the 256 entries at `slides`. -/
abbrev Sw (s : GlobalState) (slides : Pointer) (w : BitVec 4096) : GlobalState :=
  { s with mem := s.mem.splice slides w }

/-- Entry `k` of the buffer. -/
def slot (w : BitVec 4096) (k : Nat) : BitVec 16 := w.extractLsb' (16 * k) 16

/-- `slides + 2k`, the pointer `getelementptr i16` computes for entry `k`. -/
def slotPtr (slides : Pointer) (k : Nat) : Pointer :=
  { slides with offset := slides.offset + BitVec.ofNat 64 (2 * k) }

theorem slotPtr_offsetInBits {slides : Pointer} {k : Nat}
    (h : slides.offset.toNat + 512 ≤ 2 ^ 64) (hk : k < 256) :
    (slotPtr slides k).offsetInBits = slides.offsetInBits + 16 * k := by
  simp only [slotPtr, Pointer.offsetInBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 2 * k) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- A store into the buffer is a store into `w`. -/
theorem spliceBits_slot {n : Nat} (b : BitVec n) (off k : Nat) (hk : k < 256)
    (w : BitVec 4096) (x : BitVec 16) :
    spliceBits (spliceBits b off w) (off + 16 * k) x = spliceBits b off (spliceBits w (16 * k) x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  by_cases h1 : off + 16 * k ≤ i ∧ i < off + 16 * k + 16 ∧ i < n
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
    congr 1; omega
  · rw [if_neg h1]
    by_cases h2 : off ≤ i ∧ i < off + 4096 ∧ i < n
    · rw [if_pos h2, if_pos h2, if_neg (by omega)]
    · rw [if_neg h2, if_neg h2]

/-- ... and reading entry `k` back reads `w`. -/
theorem extract_spliceBits_slot {n : Nat} (b : BitVec n) (off k : Nat) (hk : k < 256)
    (hn : off + 4096 ≤ n) (w : BitVec 4096) :
    (spliceBits b off w).extractLsb' (off + 16 * k) 16 = slot w k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [slot, BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi, decide_true,
    Bool.true_and]
  rw [if_pos (by omega)]
  congr 1; omega

theorem slot_spliceBits (w : BitVec 4096) (x : BitVec 16) {j k : Nat} (hj : j < 256) (hk : k < 256) :
    slot (spliceBits w (16 * k) x) j = if j = k then x else slot w j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hjk : j = k
  · subst hjk
    simp only [slot, if_true, BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi, decide_true,
      Bool.true_and]
    rw [if_pos (by omega)]
    congr 1; omega
  · simp only [slot, hjk, if_false, BitVec.getLsbD_extractLsb', getLsbD_spliceBits, hi,
      decide_true, Bool.true_and]
    rw [if_neg (by omega)]

variable {s u : GlobalState} {slides : Pointer} {w : BitVec 4096}

/-- `u`'s block at `slides`, given the entry block. -/
theorem live?_slides (hu : u ≈ Sw s slides w) {blk : LiveBlock} (hblk : s.mem.live? slides.id = some blk) :
    u.mem.live? slides.id = some { length := blk.length, bytes := spliceBits blk.bytes slides.offsetInBits w } :=
  (hu.live slides.id).trans (splicedLive s.mem slides blk hblk w)

/-- Storing entry `k` moves the buffer model from `w` to `w` with entry `k` replaced. -/
theorem store_slot_equiv (hoff : slides.offset.toNat + 512 ≤ 2 ^ 64) (hu : u ≈ Sw s slides w)
    {k : Nat} (hk : k < 256) (x : BitVec 16) :
    ({ u with mem := u.mem.splice (slotPtr slides k) x } : GlobalState)
      ≈ Sw s slides (spliceBits w (16 * k) x) := by
  refine GlobalState.Equiv.trans (splice_equiv (p := slotPtr slides k) (x := x) hu) ⟨rfl, rfl, fun q => ?_⟩
  show ((s.mem.splice slides w).splice (slotPtr slides k) x).live? q
    = (s.mem.splice slides (spliceBits w (16 * k) x)).live? q
  by_cases hq : slides.id = q
  · subst hq
    show ((s.mem.splice slides w).splice (slotPtr slides k) x).live? (slotPtr slides k).id = _
    cases hb : s.mem.live? slides.id with
    | none =>
        rw [splicedDead (m := s.mem.splice slides w) (p := slotPtr slides k) (splicedDead hb),
          splicedDead hb]
    | some b =>
        rw [splicedLive _ (slotPtr slides k) _ (splicedLive s.mem slides b hb w) x,
          splicedLive s.mem slides b hb, slotPtr_offsetInBits hoff hk, spliceBits_slot _ _ _ hk]
  · rw [live?_splice_ne (p := slotPtr slides k) hq, live?_splice_ne (p := slides) hq,
      live?_splice_ne (p := slides) hq]

/-- Writing a block's own bits back changes nothing. -/
theorem live?_splice_self {m : MemoryState} {p : Pointer} {blk : LiveBlock}
    (hl : m.live? p.id = some blk) (q : BlockId) :
    (m.splice p (blk.bytes.extractLsb' p.offsetInBits 4096)).live? q = m.live? q := by
  by_cases hq : p.id = q
  · subst hq
    rw [splicedLive m p blk hl, hl]
    cases blk with
    | mk len bytes =>
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [getLsbD_spliceBits, BitVec.getLsbD_extractLsb']
      split_ifs with h1
      · simp only [show i - p.offsetInBits < 4096 by omega, decide_true, Bool.true_and]
        congr 1; omega
      · rfl
  · exact live?_splice_ne hq

/-- Entry `k` fits in every state the walk reaches. -/
theorem fits_slot (hsl : IsSlidesPtr s.mem slides) (hu : u ≈ Sw s slides w) {k : Nat} (hk : k < 256) :
    Fits u.mem (slotPtr slides k) 16 := by
  obtain ⟨blk, hblk, hlen⟩ := hsl.1
  have hl : s.mem.live? slides.id = some blk := by simp [MemoryState.live?, hblk]
  refine ⟨{ length := blk.length, bytes := spliceBits blk.bytes slides.offsetInBits w },
    getElem?_of_live? (live?_slides hu hl), ?_⟩
  simp only [LiveBlock.lengthInBits] at hlen ⊢
  rw [slotPtr_offsetInBits hsl.2 hk]
  omega

/-- Loading entry `k` reads `slot w k`. -/
theorem run_load_slot (hsl : IsSlidesPtr s.mem slides) (hu : u ≈ Sw s slides w) {k : Nat}
    (hk : k < 256) :
    (load (.value (slotPtr slides k)) (.bitvec (.concrete 16))).run u.mem
      = .value (.value (slot w k), u.mem) := by
  obtain ⟨blk, hblk, hlen⟩ := hsl.1
  have hl : s.mem.live? slides.id = some blk := by simp [MemoryState.live?, hblk]
  simp only [LiveBlock.lengthInBits] at hlen
  rw [run_load (p := slotPtr slides k) (getElem?_of_live? (live?_slides hu hl))
    (by simp only [LiveBlock.lengthInBits, LLVM.Ty.width]; rw [slotPtr_offsetInBits hsl.2 hk]; omega)]
  simp only [LLVM.Ty.unflatten, LLVM.Ty.width]
  rw [slotPtr_offsetInBits hsl.2 hk, extract_spliceBits_slot _ _ _ hk (by omega)]

/-- Storing entry `k`. -/
theorem run_store_slot (hsl : IsSlidesPtr s.mem slides) (hu : u ≈ Sw s slides w) {k : Nat}
    (hk : k < 256) (x : BitVec 16) :
    (store (.value (slotPtr slides k)) (.bitvec (.concrete 16)) (.value x)).run u.mem
      = .value ((), u.mem.splice (slotPtr slides k) x) :=
  run_store rfl (fits_slot hsl hu hk)

/-! ## Stepping a tail block

The stepper's impure-instruction lemmas carry the `>>= k` an entry block sits
under; a tail block is walked on its own. -/

private theorem nil_append' {Γ : Ctxt SLLVM.Ty} (V : Γ.Valuation) :
    ((.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)) ++ V) = V := by
  show (Ctxt.Valuation.ofHVector
      (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty))) ++ V = V
  simp only [Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.nil_append]

/-- A store in a tail block, given that it succeeds. -/
theorem run_denote_var_of_nil {Γ Γout : Ctxt SLLVM.Ty} {rets succs}
    {e : Expr SLLVM Γ .impure []}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s s' : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .value (.nil, s')) :
    StateT.run ((BlockCom.var e body).denote V) s = StateT.run (body.denote V) s' := by
  rw [BlockCom.denote_var, Expr.denote_unfold,
    EffectM.run_bind_of_value
      (a := (HVector.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)) ++ V) (s' := s')
      (by rw [EffectM.run_map, h]; rfl),
    nil_append']

/-- An instruction that is UB poisons the rest of the block. -/
theorem run_denote_var_of_poison {Γ Γout : Ctxt SLLVM.Ty} {rets succs ts}
    {e : Expr SLLVM Γ .impure ts} {body : BlockCom (ts ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {s : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .poison) :
    StateT.run ((BlockCom.var e body).denote V) s = .poison := by
  rw [BlockCom.denote_var, Expr.denote_unfold, EffectM.run_bind, EffectM.run_map, h]; rfl

/-- A store handed poison is UB. -/
theorem run_store_of_poison {t : LLVM.Ty} {x : TyDenote.toType t} {p : Pointer}
    {m : MemoryState} (hx : LLVM.Ty.flatten t x = .poison) :
    (store (.value p) t x).run m = .poison := by
  simp [store, PoisonOr.getOrUB, hx]

theorem run_liftM_of_poison {α : Type} {x : MemorySSAM α} {s : GlobalState}
    (h : x.run s.mem = .poison) : (liftM x : EffectM α).run s = .poison := by
  cases s
  simp only [liftM, monadLift, MonadLift.monadLift, StateT.run] at *
  rw [h]

/-- Case on a register in continuation form. -/
theorem poison_cases {α : Type} {v : PoisonOr α} {P : Prop}
    (hp : v = .poison → P) (hv : ∀ a, v = .value a → P) : P := by
  cases v with
  | poison => exact hp rfl
  | value a => exact hv a rfl

/-- The named-result goal, closed on a poison run. -/
theorem res_poison {α : Type} {r : PoisonOr (α × GlobalState)} {P : α → GlobalState → Prop}
    (h : r = .poison) : ∃ res, r = res ∧ ∀ p u', res = .value (p, u') → P p u' :=
  ⟨.poison, h, fun _ _ h' => absurd h'.symm (PoisonOr.value_ne_poison _)⟩

/-- ... and on a run that returns. -/
theorem res_value {α : Type} {p : α} {u : GlobalState} {P : α → GlobalState → Prop}
    (h : P p u) : ∃ res, (PoisonOr.value (p, u) : PoisonOr (α × GlobalState)) = res
      ∧ ∀ p' u', res = .value (p', u') → P p' u' :=
  ⟨_, rfl, fun p' u' h' => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (PoisonOr.value_inj.mp h'); exact h⟩

/-- A load either traps or returns something, and never moves the state. -/
theorem load_cases_cont {P : Prop} (p : SLLVM.Ptr) (t : LLVM.Ty) (m : MemoryState)
    (hp : (load p t).run m = .poison → P) (hv : ∀ x, (load p t).run m = .value (x, m) → P) : P := by
  match p with
  | .poison => exact hp (by simp [load, PoisonOr.getOrUB])
  | .value p =>
    cases hb : m[p.id]? with
    | none => exact hp (by simp [load, getLiveBlockOrUB, hb, PoisonOr.getOrUB])
    | some b =>
      cases b with
      | dead => exact hp (by simp [load, getLiveBlockOrUB, hb, PoisonOr.getOrUB])
      | live blk =>
        by_cases hlen : p.offsetInBits + LLVM.Ty.width t ≤ blk.lengthInBits
        · exact hv _ (run_load hb hlen)
        · exact hp (by simp [load, getLiveBlockOrUB, hb, throwUBIf, Nat.lt_of_not_le hlen,
            PoisonOr.getOrUB])

/-- `getelementptr i16, slides, k` is entry `k`. -/
theorem gep_slot (p : Pointer) (k : Nat) :
    gep (PoisonOr.value p) 2 0 (PoisonOr.value (BitVec.ofNat 64 k)) = PoisonOr.value (slotPtr p k) := by
  simp only [gep, ptradd, LLVM.mul, LLVM.add, LLVM.const?, LLVM.mul?, LLVM.add?, slotPtr,
    PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  rw [show (BitVec.ofInt 64 ((2 : Nat) : Int)) = 2#64 from rfl,
    show (BitVec.ofInt 64 ((0 : Nat) : Int)) = 0#64 from rfl]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- A block that ends in `llvm.br`. -/
theorem term_br {Γ : Ctxt SLLVM.Ty} {rets succs} {tgt : Target Γ succs} {V : Γ.Valuation}
    {u : GlobalState} {P : _ → GlobalState → Prop}
    (h : P (V, (.inr (tgt.denote V) : HVector toType rets ⊕ SuccArgs succs)) u) :
    ∃ res, StateT.run ((BlockCom.term (.br tgt) : BlockCom Γ Γ rets succs).denote V) u = res
      ∧ ∀ p u', res = .value (p, u') → P p u' :=
  res_value h

/-- A block that ends in `llvm.cond_br`: poison traps, a value picks the target. -/
theorem term_condBr {Γ : Ctxt SLLVM.Ty} {rets succs} {c : Γ.Var (SLLVM.Ty.bitvec 1)}
    {tT tF : Target Γ succs} {V : Γ.Valuation} {u : GlobalState} {P : _ → GlobalState → Prop}
    (h : ∀ b, V c = .value b →
      P (V, (.inr ((if b = 1 then tT else tF).denote V) : HVector toType rets ⊕ SuccArgs succs)) u) :
    ∃ res, StateT.run ((BlockCom.term (.condBr c tT tF) : BlockCom Γ Γ rets succs).denote V) u = res
      ∧ ∀ p u', res = .value (p, u') → P p u' := by
  match hc : V c with
  | .poison => exact res_poison (by simp [BlockCom.denote_term, Terminator.denote_condBr_poison hc])
  | .value b =>
    refine ⟨_, rfl, fun p' u' h' => ?_⟩
    have h'' : (PoisonOr.value ((V, .inr ((if b = 1 then tT else tF).denote V)), u) :
        PoisonOr ((Γ.Valuation × (HVector toType rets ⊕ SuccArgs succs)) × GlobalState))
        = .value (p', u') := by
      rw [← h']; simp [BlockCom.denote_term, Terminator.denote_condBr_value hc]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (PoisonOr.value_inj.mp h'')
    exact h b hc

/-- A block that ends in `llvm.return`. -/
theorem term_ret {Γ : Ctxt SLLVM.Ty} {succs} {V : Γ.Valuation}
    {u : GlobalState} {P : _ → GlobalState → Prop}
    (h : P (V, (.inl .nil : HVector toType [] ⊕ SuccArgs succs)) u) :
    ∃ res, StateT.run ((BlockCom.term (.ret .nil) : BlockCom Γ Γ [] succs).denote V) u = res
      ∧ ∀ p u', res = .value (p, u') → P p u' :=
  res_value h

/-! ## Register arithmetic on small naturals

Every index the region computes stays far below any wrap, so it is carried as
`BitVec.ofNat w k` and these fold its operations. -/

theorem add64 {a b : Nat} (f : LLVM.NoWrapFlags) (h : a + b < 2 ^ 63) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 64 a)) (PoisonOr.value (BitVec.ofNat 64 b)) f
      = PoisonOr.value (BitVec.ofNat 64 (a + b)) := by
  have hs : BitVec.saddOverflow (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
    simp only [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> simp <;> omega
  have hu : BitVec.uaddOverflow (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = false := by
    simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp; omega
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, hs, hu, Bool.false_eq_true, and_false,
    if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add32 {a b : Nat} (f : LLVM.NoWrapFlags) (h : a + b < 2 ^ 31) :
    LLVM.add (PoisonOr.value (BitVec.ofNat 32 a)) (PoisonOr.value (BitVec.ofNat 32 b)) f
      = PoisonOr.value (BitVec.ofNat 32 (a + b)) := by
  have hs : BitVec.saddOverflow (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = false := by
    simp only [BitVec.saddOverflow, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> simp <;> omega
  have hu : BitVec.uaddOverflow (BitVec.ofNat 32 a) (BitVec.ofNat 32 b) = false := by
    simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp; omega
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, hs, hu, Bool.false_eq_true, and_false,
    if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem trunc32 {a : Nat} (_h : a < 2 ^ 32) :
    LLVM.trunc 32 (PoisonOr.value (BitVec.ofNat 64 a)) = PoisonOr.value (BitVec.ofNat 32 a) := by
  simp only [LLVM.trunc, LLVM.trunc?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sext64 {a : Nat} (h : a < 2 ^ 31) :
    LLVM.sext 64 (PoisonOr.value (BitVec.ofNat 32 a)) = PoisonOr.value (BitVec.ofNat 64 a) := by
  simp only [LLVM.sext, LLVM.sext?, PoisonOr.value_bind]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_ofNat, BitVec.msb_eq_getLsbD_last]
  by_cases hi32 : i < 32
  · simp [hi32, hi]
  · simp [hi32, hi]
    rw [Nat.testBit_lt_two_pow (show a < 2 ^ 31 from h),
      Nat.testBit_lt_two_pow (show a < 2 ^ i from
        lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem icmp_eq_ofNat {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    LLVM.icmp .eq (PoisonOr.value (BitVec.ofNat w a)) (PoisonOr.value (BitVec.ofNat w b))
      = PoisonOr.value (BitVec.ofBool (decide (a = b))) := by
  simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind]
  congr 2
  by_cases hab : a = b
  · subst hab; simp
  · simp only [hab, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact hab this

theorem icmp_slt32 {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    LLVM.icmp .slt (PoisonOr.value (BitVec.ofNat 32 a)) (PoisonOr.value (BitVec.ofNat 32 b))
      = PoisonOr.value (BitVec.ofBool (decide (a < b))) := by
  simp only [LLVM.icmp, LLVM.icmp?_slt_eq, PoisonOr.value_bind]
  congr 2
  simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_decide]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  split_ifs <;> omega

theorem ofBool_eq_one {p : Prop} [Decidable p] : BitVec.ofBool (decide p) = (1 : BitVec 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ofBool_beq_one {w : Nat} {x y : BitVec w} : BitVec.ofBool (x == y) = (1 : BitVec 1) ↔ x = y := by
  by_cases h : x = y
  · simp [h]
  · have hb : (x == y) = false := by simpa using h
    simp [h, hb]

/-! ## The entry valuation, as the tail blocks read it

`%k` is `Γout` variable `18 - k`; `%arg2`, `%arg1`, `%arg0` are 19, 20, 21. -/

structure EntryEnv (V : fd_curve25519_scalar_wnaf.Γout.Valuation) (slides : Pointer) : Prop where
  c1 : V (⟨17, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 0#64
  c5 : V (⟨13, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 16)) = .value 1#16
  c6 : V (⟨12, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 1#64
  c7 : V (⟨11, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 255#64
  c8 : V (⟨10, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 16)) = .value 0#16
  c9 : V (⟨9, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 256#32
  c13 : V (⟨5, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 255#32
  c14 : V (⟨4, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 2#32
  c16 : V (⟨2, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 32)) = .value 1#32
  c17 : V (⟨1, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var (SLLVM.Ty.bitvec 64)) = .value 256#64
  arg0 : V (⟨21, by rfl⟩ : fd_curve25519_scalar_wnaf.Γout.Var SLLVM.Ty.ptr) = .value slides

/-! ## The invariant -/

local notation "v64 " k => (PoisonOr.value (BitVec.ofNat 64 k) : LLVM.IntW 64)
local notation "v32 " k => (PoisonOr.value (BitVec.ofNat 32 k) : LLVM.IntW 32)
local notation "vp " q => (PoisonOr.value q : SLLVM.Ptr)

/-- Where the walk can stand, and what holds there. -/
inductive Reach (s : GlobalState) (slides : Pointer) :
    SuccArgs fd_curve25519_scalar_wnaf.sigs → GlobalState → Prop
  | bb1 {u w} (hu : u ≈ Sw s slides w) : Reach s slides ⟨0, rfl, .nil⟩ u
  | bb2 {u w} (k : Nat) (hk : k ≤ 254) (hu : u ≈ Sw s slides w) :
      Reach s slides ⟨1, rfl, [v64 k]ₕ⟩ u
  | bb3 {u w} (k : Nat) (x19 : LLVM.IntW 32) (hk : k ≤ 255) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) : Reach s slides ⟨2, rfl, [v64 k, x19]ₕ⟩ u
  | bb4 {u w} (k : Nat) (x19 : LLVM.IntW 32) (hk : k ≤ 255) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) : Reach s slides ⟨3, rfl, [x19, v64 k]ₕ⟩ u
  | bb5 {u w} (k : Nat) (x19 : LLVM.IntW 32) (hk : k ≤ 254) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) : Reach s slides ⟨4, rfl, [x19, v64 k]ₕ⟩ u
  | bb6 {u w} (i : Nat) (x19 : LLVM.IntW 32) (hi : i ≤ 254) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) : Reach s slides ⟨5, rfl, [x19, v32 i]ₕ⟩ u
  | bb7 {u w} (i : Nat) (x43 x44 x45 : LLVM.IntW 32) (hi : i ≤ 255) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0 ∨ i = 255) : Reach s slides ⟨6, rfl, [v32 i, x43, x44, x45]ₕ⟩ u
  | bb8 {u w} (i : Nat) (x43 x44 x45 : LLVM.IntW 32) (hi : i ≤ 254) (hu : u ≈ Sw s slides w)
      (ht : slot w 255 = 0) : Reach s slides ⟨7, rfl, [x43, x44, x45, v32 i]ₕ⟩ u
  | bb9 {u w} (j m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32) (hj : j ≤ 254)
      (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨8, rfl, [v32 (j + 2), v64 j, x52, x43, x44, x45, x46, v64 m]ₕ⟩ u
  | bb10 {u w} (j m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
      (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨9, rfl, [x43, x44, x45, x46, v64 m, v32 (j + 2), v64 j, x52, v64 (j + 1),
        vp (slotPtr slides (j + 1))]ₕ⟩ u
  | bb11 {u w} (j m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 x46 x61 : LLVM.IntW 32)
      (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨10, rfl, [x43, x44, x45, x46, v64 m, v32 (j + 2), v64 j, x52, v64 (j + 1),
        vp (slotPtr slides (j + 1)), x61]ₕ⟩ u
  | bb12 {u w} (j m : Nat) (x64 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
      (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨11, rfl, [x43, x44, x45, x46, v64 m, v32 (j + 2), v64 (j + 1),
        vp (slotPtr slides (j + 1)), x64]ₕ⟩ u
  | bb13 {u w} (j m : Nat) (x52 x63 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨12, rfl, [x43, x44, x45, v64 m, v32 (j + 2), v64 j, x52, v64 (j + 1),
        vp (slotPtr slides (j + 1)), x63]ₕ⟩ u
  | bb14 {u w} (j m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨13, rfl, [x43, x44, x45, v64 m, v32 (j + 2), v64 j,
        vp (slotPtr slides (j + 1)), x68]ₕ⟩ u
  | bb15 {u w} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hc : c ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨14, rfl, [x43, x44, x45, v64 m, v32 c, x68, vp (slotPtr slides c)]ₕ⟩ u
  | bb16 {u w} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨15, rfl, [x43, x44, x45, v64 m, x68, v64 c, vp (slotPtr slides c)]ₕ⟩ u
  | bb17 {u w} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨16, rfl, [v32 c, vp (slotPtr slides c), x43, x44, x45, v64 m, x68]ₕ⟩ u
  | bb18 {u w} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hc : c ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨17, rfl, [v64 c, vp (slotPtr slides c), x43, x44, x45, v64 m, x68]ₕ⟩ u
  | bb19 {u w} (c m : Nat) (x87 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
      (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨18, rfl, [x87, x43, x44, x45, x46, v64 m, v32 (c + 1), v64 c]ₕ⟩ u
  | bb20 {u w} (m : Nat) (x91 : LLVM.IntW 16) (hm : m ≤ 255) (hu : u ≈ Sw s slides w) :
      Reach s slides ⟨19, rfl, [v64 m, x91]ₕ⟩ u
  | bb21 {u w} (c m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hc : c ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
      Reach s slides ⟨20, rfl, [x43, x44, x45, v64 m, x52, v64 c]ₕ⟩ u
  | bb22 {u w} (c m : Nat) (x95 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
      (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0 ∨ c = 255) :
      Reach s slides ⟨21, rfl, [v32 c, x95, x43, x44, x45, v64 m]ₕ⟩ u
  | bb23 {u w} (hu : u ≈ Sw s slides w) : Reach s slides ⟨22, rfl, .nil⟩ u

/-- What the walk ends in. -/
def Done (s : GlobalState) (slides : Pointer) (u : GlobalState) : Prop :=
  ∃ w, u ≈ Sw s slides w

/-- A block's outcome, as the rule consumes it. -/
abbrev Post (s : GlobalState) (slides : Pointer) {Γ : Ctxt SLLVM.Ty}
    (p : Γ.Valuation × (HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty) ⊕
      SuccArgs fd_curve25519_scalar_wnaf.sigs))
    (u : GlobalState) : Prop :=
  (∀ rs, p.2 = .inl rs → Done s slides u) ∧ (∀ t, p.2 = .inr t → Reach s slides t u)

/-! ## The blocks -/

section Steps
variable {s : GlobalState} {slides : Pointer} {V : fd_curve25519_scalar_wnaf.Γout.Valuation}

set_option maxRecDepth 100000 in
theorem step_bb1 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (hu : u ≈ Sw s slides w) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 0 rfl).2.denote
      (Ctxt.Valuation.ofHVector (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 19
  denote_step_reduce v 20 [LLVM.const?] fold
  try simp only [simp_spine] at hv19 hv20
  simp only [hV.c7, hV.arg0] at hv20
  have h20 : v20 = PoisonOr.value (slotPtr slides 255) := by rw [hv20]; exact gep_slot slides 255
  clear hv20
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (255)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8, h20]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show 255 < 256 by omega) 0#16
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hV.c1]
  exact Reach.bb3 0 v19 (by omega) hu' (by rw [slot_spliceBits _ _ (by omega) (by omega), if_pos rfl]; rfl)

set_option maxRecDepth 100000 in
theorem step_bb2 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (hk : k ≤ 254) (hu : u ≈ Sw s slides w) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 1 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 k]ₕ : HVector toType [SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 22
  denote_step_reduce v 25 [LLVM.const?] fold
  -- `%26`: the scalar's byte; its value is irrelevant
  refine load_cases_cont v25 (.bitvec (.concrete 8)) u.mem (fun h => ?_) (fun x26 h => ?_)
  · rw [run_denote_var_of_poison (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM_of_poison h]; rfl)]
    exact res_poison rfl
  rw [BlockCom.run_denote_var_of_value (x := x26) (s' := u) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      rw [run_liftM h]; rfl)]
  denote_step_reduce v 31 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv31
  have h31 : v31 = PoisonOr.value (slotPtr slides k) := by rw [hv31, gep_slot]
  clear hv31
  -- `%31`: entry `k`
  refine poison_cases (v := v30) (fun h30 => ?_) (fun x30 h30 => ?_)
  · rw [run_denote_var_of_poison (by
        simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        simp only [simp_spine, h30, h31]
        rw [run_liftM_of_poison (run_store_of_poison rfl)]; rfl)]
    exact res_poison rfl
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (k)) x30 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h30, h31]
      rw [run_liftM (run_store_slot hsl hu (by omega) x30)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show k < 256 by omega) x30
  denote_step_reduce v 33 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.c7] at hv32 hv33
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv33] at hb
  rw [add64 _ (by omega), icmp_eq_ofNat (by omega) (by omega), PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hk1 : k + 1 = 255
  · rw [if_pos (ofBool_eq_one.mpr hk1)]
    exact Reach.bb1 hu'
  · rw [if_neg (mt ofBool_eq_one.mp hk1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv32, add64 _ (show k + 1 < 2 ^ 63 by omega)]
    exact Reach.bb2 (k + 1) (by omega) hu'

set_option maxRecDepth 100000 in
theorem step_bb3 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (x19 : LLVM.IntW 32) (hk : k ≤ 255)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 2 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 k, x19]ₕ : HVector toType [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 35
  denote_step_reduce v 35 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv35
  have h35 : v35 = PoisonOr.value (slotPtr slides k) := by rw [hv35, gep_slot]
  clear hv35
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot w (k)) : LLVM.IntW 16)) (s' := u) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h35]
      rw [run_liftM (run_load_slot hsl hu (by omega))]; rfl)]
  denote_step_reduce v 37 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv37
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv37, LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind,
    PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot w k = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb4 k x19 hk hu ht
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    have hk' : k ≠ 255 := fun h => hz (h ▸ ht)
    exact Reach.bb5 k x19 (by omega) hu ht

set_option maxRecDepth 100000 in
theorem step_bb4 (hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (x19 : LLVM.IntW 32) (hk : k ≤ 255)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 3 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x19, v64 k]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 38
  denote_step_reduce v 39 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.c17] at hv38 hv39
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv39] at hb
  rw [add64 _ (by omega), icmp_eq_ofNat (by omega) (by omega), PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hk1 : k + 1 = 256
  · rw [if_pos (ofBool_eq_one.mpr hk1)]
    exact Reach.bb23 hu
  · rw [if_neg (mt ofBool_eq_one.mp hk1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv38, add64 _ (show k + 1 < 2 ^ 63 by omega)]
    exact Reach.bb3 (k + 1) x19 (by omega) hu ht

set_option maxRecDepth 100000 in
theorem step_bb5 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (k : Nat) (x19 : LLVM.IntW 32) (hk : k ≤ 254)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 4 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x19, v64 k]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 40
  denote_step_reduce v 41 [LLVM.const?] fold
  try simp only [simp_spine] at hv40
  refine term_condBr (fun b hb => ?_)
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine, hv40, trunc32 (show k < 2 ^ 32 by omega)]
    exact Reach.bb6 k x19 hk hu ht
  · exact Reach.bb23 hu

set_option maxRecDepth 100000 in
theorem step_bb6 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (i : Nat) (x19 : LLVM.IntW 32) (hi : i ≤ 254)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 5 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x19, v32 i]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 42
  denote_step_reduce v 45 [LLVM.const?] fold
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine]
  exact Reach.bb7 i _ _ _ (by omega) hu (Or.inl ht)

set_option maxRecDepth 100000 in
theorem step_bb7 (hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (i : Nat) (x43 x44 x45 : LLVM.IntW 32) (hi : i ≤ 255)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0 ∨ i = 255) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 6 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 i, x43, x44, x45]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 47
  denote_step_reduce v 47 [LLVM.const?] fold
  simp only [simp_spine, hV.c13] at hv47
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv47] at hb
  rw [icmp_slt32 (by omega) (by omega), PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hi1 : i < 255
  · rw [if_pos (ofBool_eq_one.mpr hi1)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb8 i x43 x44 x45 (by omega) hu (ht.resolve_right (by omega))
  · rw [if_neg (mt ofBool_eq_one.mp hi1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hV.c7, hV.c5]
    exact Reach.bb20 255 _ (by omega) hu

set_option maxRecDepth 100000 in
theorem step_bb8 (hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (i : Nat) (x43 x44 x45 : LLVM.IntW 32) (hi : i ≤ 254)
    (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 7 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, v32 i]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 48
  denote_step_reduce v 49 [LLVM.const?] fold
  try simp only [simp_spine] at hv48 hv49
  simp only [hV.c14] at hv49
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv48, hv49, hV.c5,
    sext64 (show i < 2 ^ 31 by omega), add32 _ (show i + 2 < 2 ^ 31 by omega)]
  exact Reach.bb9 i i _ x43 x44 x45 _ hi hi hu ht

set_option maxRecDepth 100000 in
theorem step_bb9 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
    (hj : j ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 8 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 (j + 2), v64 j, x52, x43, x44, x45, x46, v64 m]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 53
  denote_step_reduce v 54 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.arg0] at hv53 hv54
  rw [add64 _ (show j + 1 < 2 ^ 63 by omega)] at hv53 hv54
  have h54 : v54 = PoisonOr.value (slotPtr slides (j + 1)) := by rw [hv54, gep_slot]
  clear hv54
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot w (j + 1)) : LLVM.IntW 16)) (s' := u) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h54]
      rw [run_liftM (run_load_slot hsl hu (by omega))]; rfl)]
  denote_step_reduce v 56 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv56
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv56, LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind,
    PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot w (j + 1) = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv53, h54]
    exact Reach.bb19 (j + 1) m x52 x43 x44 x45 x46 (by omega) hm hu ht
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv53, h54]
    have hj' : j + 1 ≠ 255 := fun h => hz (h ▸ ht)
    exact Reach.bb10 j m x52 x43 x44 x45 x46 (by omega) hm hu ht

set_option maxRecDepth 100000 in
theorem step_bb10 (hs : s.WF) (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides)
    {u : GlobalState} {w : BitVec 4096} (j m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
    (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 9 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, x46, v64 m, v32 (j + 2), v64 j, x52, v64 (j + 1),
          vp (slotPtr slides (j + 1))]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32,
          SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32,
          SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 57
  denote_step_reduce v 58 [LLVM.const?] fold
  have hwf : u.WF := (GlobalState.WF.splice hs).of_equiv hu.symm
  obtain ⟨u1, hcall, he⟩ := fd_int_min_conforms v58 u hwf
  rw [BlockCom.run_denote_call_cfg_of_value (c := fd_int_min) (argTys := [SLLVM.Ty.bitvec 32])
    (argVals := [v58]ₕ) (x := SLLVM.smin v58 (.value 14#32)) (s' := u1) (by simp only [simp_spine])
    hcall]
  have hu1 := he.symm.trans hu
  denote_step_reduce v 62 [LLVM.const?] fold
  refine term_condBr (fun b hb => ?_)
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb21 (j + 1) m x52 x43 x44 x45 hj hm hu1 ht
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb11 j m x52 x43 x44 x45 x46 _ hj hm hu1 ht

set_option maxRecDepth 100000 in
theorem step_bb11 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 x46 x61 : LLVM.IntW 32)
    (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 10 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, x46, v64 m, v32 (j + 2), v64 j, x52, v64 (j + 1), vp (slotPtr slides (j + 1)), x61]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 63
  denote_step_reduce v 66 [LLVM.const?] fold
  refine term_condBr (fun b hb => ?_)
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb13 j m x52 _ x43 x44 x45 hj hm hu ht
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb12 j m _ x43 x44 x45 x46 hj hm hu ht

set_option maxRecDepth 100000 in
theorem step_bb12 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (x64 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
    (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 11 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, x46, v64 m, v32 (j + 2), v64 (j + 1), vp (slotPtr slides (j + 1)), x64]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (j + 1)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show j + 1 < 256 by omega) 0#16
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine]
  exact Reach.bb19 (j + 1) m x64 x43 x44 x45 x46 (by omega) hm hu' (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)

set_option maxRecDepth 100000 in
theorem step_bb13 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (x52 x63 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 12 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, v64 m, v32 (j + 2), v64 j, x52, v64 (j + 1), vp (slotPtr slides (j + 1)), x63]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 67
  denote_step_reduce v 70 [LLVM.const?] fold
  try simp only [simp_spine] at hv67
  refine term_condBr (fun b hb => ?_)
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  split
  · simp only [Target.denote_mk, HVector.map, simp_spine, hv67, trunc32 (show j + 1 < 2 ^ 32 by omega)]
    exact Reach.bb22 (j + 1) m x52 x43 x44 x45 (by omega) hm hu (Or.inl ht)
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb14 j m _ x43 x44 x45 hj hm hu ht

set_option maxRecDepth 100000 in
theorem step_bb14 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (j m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hj : j + 1 ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 13 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, v64 m, v32 (j + 2), v64 j, vp (slotPtr slides (j + 1)), x68]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 71
  denote_step_reduce v 71 [LLVM.const?] fold
  try simp only [simp_spine] at hv71
  rw [trunc32 (show j < 2 ^ 32 by omega)] at hv71
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (j + 1)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show j + 1 < 256 by omega) 0#16
  have ht' : slot (spliceBits w (16 * (j + 1)) 0#16) 255 = 0 := (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)
  denote_step_reduce v 74 [LLVM.const?] fold
  simp only [simp_spine, hV.c14, hV.arg0, hv71] at hv72 hv73 hv74
  rw [add32 _ (show j + 2 < 2 ^ 31 by omega)] at hv72 hv73 hv74
  rw [sext64 (show j + 2 < 2 ^ 31 by omega)] at hv73 hv74
  have h74 : v74 = PoisonOr.value (slotPtr slides (j + 2)) := by rw [hv74, gep_slot]
  clear hv74
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot (spliceBits w (16 * (j + 1)) 0#16) (j + 2)) : LLVM.IntW 16)) (s' := { u with mem := u.mem.splice (slotPtr slides (j + 1)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h74]
      rw [run_liftM (run_load_slot hsl hu' (by omega))]; rfl)]
  denote_step_reduce v 76 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv76
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv76, LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind,
    PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot (spliceBits w (16 * (j + 1)) 0#16) (j + 2) = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv72, h74]
    exact Reach.bb17 (j + 2) m x68 x43 x44 x45 (by omega) hm hu' ht'
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, h74]
    have hj' : j + 2 ≠ 255 := fun h => hz (h ▸ ht')
    exact Reach.bb15 (j + 2) m x68 x43 x44 x45 (by omega) hm hu' ht'

set_option maxRecDepth 100000 in
theorem step_bb15 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hc : c ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 14 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, v64 m, v32 c, x68, vp (slotPtr slides c)]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 16, SLLVM.Ty.ptr]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 77
  denote_step_reduce v 77 [LLVM.const?] fold
  try simp only [simp_spine] at hv77
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv77, sext64 (show c < 2 ^ 31 by omega)]
  exact Reach.bb18 c m x68 x43 x44 x45 hc hm hu ht

set_option maxRecDepth 100000 in
theorem step_bb16 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 15 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, v64 m, x68, v64 c, vp (slotPtr slides c)]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 78
  denote_step_reduce v 78 [LLVM.const?] fold
  try simp only [simp_spine] at hv78
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv78, trunc32 (show c < 2 ^ 32 by omega)]
  exact Reach.bb17 c m x68 x43 x44 x45 hc hm hu ht

set_option maxRecDepth 100000 in
theorem step_bb17 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 16 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 c, vp (slotPtr slides c), x43, x44, x45, v64 m, x68]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (c)) 1#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c5]
      rw [run_liftM (run_store_slot hsl hu (by omega) 1#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show c < 256 by omega) 1#16
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine]
  refine Reach.bb22 c m x68 x43 x44 x45 hc hm hu' ?_
  by_cases hc1 : c = 255
  · exact Or.inr hc1
  · exact Or.inl (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)

set_option maxRecDepth 100000 in
theorem step_bb18 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x68 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hc : c ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 17 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 c, vp (slotPtr slides c), x43, x44, x45, v64 m, x68]ₕ : HVector toType [SLLVM.Ty.bitvec 64, SLLVM.Ty.ptr, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (c)) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, hV.c8]
      rw [run_liftM (run_store_slot hsl hu (by omega) 0#16)]; rfl)]
  have hu' := store_slot_equiv hsl.2 hu (show c < 256 by omega) 0#16
  have ht' : slot (spliceBits w (16 * c) 0#16) 255 = 0 := (by rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht)
  denote_number_from 83
  denote_step_reduce v 84 [LLVM.const?] fold
  simp only [simp_spine, hV.c6, hV.arg0] at hv83 hv84
  rw [add64 _ (show c + 1 < 2 ^ 63 by omega)] at hv83 hv84
  have h84 : v84 = PoisonOr.value (slotPtr slides (c + 1)) := by rw [hv84, gep_slot]
  clear hv84
  rw [BlockCom.run_denote_var_of_value (x := (PoisonOr.value (slot (spliceBits w (16 * c) 0#16) (c + 1)) : LLVM.IntW 16)) (s' := { u with mem := u.mem.splice (slotPtr slides c) 0#16 }) (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm]
      simp only [simp_spine, h84]
      rw [run_liftM (run_load_slot hsl hu' (by omega))]; rfl)]
  denote_step_reduce v 86 [LLVM.const?] fold
  simp only [simp_spine, hV.c8] at hv86
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv86, LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind,
    PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hz : slot (spliceBits w (16 * c) 0#16) (c + 1) = 0#16
  · rw [if_pos (ofBool_beq_one.mpr hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv83, h84]
    exact Reach.bb16 (c + 1) m x68 x43 x44 x45 (by omega) hm hu' ht'
  · rw [if_neg (mt ofBool_beq_one.mp hz)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv83, h84]
    have hc' : c + 1 ≠ 255 := fun h => hz (h ▸ ht')
    exact Reach.bb18 (c + 1) m x68 x43 x44 x45 (by omega) hm hu' ht'

set_option maxRecDepth 100000 in
theorem step_bb19 (hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x87 : LLVM.IntW 16) (x43 x44 x45 x46 : LLVM.IntW 32)
    (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 18 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x87, x43, x44, x45, x46, v64 m, v32 (c + 1), v64 c]ₕ : HVector toType [SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 88
  denote_step_reduce v 89 [LLVM.const?] fold
  simp only [simp_spine, hV.c7, hV.c16] at hv88 hv89
  refine term_condBr (fun b hb => ?_)
  simp only [simp_spine, hv88] at hb
  rw [icmp_eq_ofNat (by omega) (by omega), PoisonOr.value_inj] at hb
  subst hb
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  by_cases hc1 : c = 255
  · rw [if_pos (ofBool_eq_one.mpr hc1)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact Reach.bb20 m x87 (by omega) hu
  · rw [if_neg (mt ofBool_eq_one.mp hc1)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv89, add32 _ (show c + 1 + 1 < 2 ^ 31 by omega)]
    exact Reach.bb9 c m x87 x43 x44 x45 x46 (by omega) hm hu ht

set_option maxRecDepth 100000 in
theorem step_bb20 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (m : Nat) (x91 : LLVM.IntW 16) (hm : m ≤ 255) (hu : u ≈ Sw s slides w) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 19 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v64 m, x91]ₕ : HVector toType [SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 92
  denote_step_reduce v 92 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv92
  have h92 : v92 = PoisonOr.value (slotPtr slides m) := by rw [hv92, gep_slot]
  clear hv92
  match x91 with
  | .poison =>
    rw [run_denote_var_of_poison (by
        simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        simp only [simp_spine, h92]
        rw [run_liftM_of_poison (run_store_of_poison rfl)]; rfl)]
    exact res_poison rfl
  | .value x91 =>
    rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (m)) x91 }) (by
        simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        simp only [simp_spine, h92]
        rw [run_liftM (run_store_slot hsl hu (by omega) x91)]; rfl)]
    have hu' := store_slot_equiv hsl.2 hu (show m < 256 by omega) x91
    refine term_br ?_
    refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
    obtain rfl := Sum.inr.inj hT
    exact Reach.bb23 hu'


set_option maxRecDepth 100000 in
theorem step_bb21 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x52 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hc : c ≤ 254) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 20 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([x43, x44, x45, v64 m, x52, v64 c]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 93
  denote_step_reduce v 93 [LLVM.const?] fold
  try simp only [simp_spine] at hv93
  refine term_br ?_
  refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
  obtain rfl := Sum.inr.inj hT
  simp only [Target.denote_mk, HVector.map, simp_spine, hv93, trunc32 (show c < 2 ^ 32 by omega)]
  exact Reach.bb22 c m x52 x43 x44 x45 (by omega) hm hu (Or.inl ht)

set_option maxRecDepth 100000 in
theorem step_bb22 (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (c m : Nat) (x95 : LLVM.IntW 16) (x43 x44 x45 : LLVM.IntW 32)
    (hc : c ≤ 255) (hm : m ≤ 254) (hu : u ≈ Sw s slides w) (ht : slot w 255 = 0 ∨ c = 255) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 21 rfl).2.denote
      (Ctxt.Valuation.ofHVector ([v32 c, x95, x43, x44, x45, v64 m]ₕ : HVector toType [SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 16, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 32, SLLVM.Ty.bitvec 64]).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  denote_number_from 96
  denote_step_reduce v 96 [LLVM.const?] fold
  simp only [simp_spine, hV.arg0] at hv96
  have h96 : v96 = PoisonOr.value (slotPtr slides m) := by rw [hv96, gep_slot]
  clear hv96
  match x95 with
  | .poison =>
    rw [run_denote_var_of_poison (by
        simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        simp only [simp_spine, h96]
        rw [run_liftM_of_poison (run_store_of_poison rfl)]; rfl)]
    exact res_poison rfl
  | .value x95 =>
    rw [run_denote_var_of_nil (s' := { u with mem := u.mem.splice (slotPtr slides (m)) x95 }) (by
        simp only [Expr.denoteOp, simp_denote, simp_sllvm]
        simp only [simp_spine, h96]
        rw [run_liftM (run_store_slot hsl hu (by omega) x95)]; rfl)]
    have hu' := store_slot_equiv hsl.2 hu (show m < 256 by omega) x95
    have ht' : slot (spliceBits w (16 * m) x95) 255 = 0 ∨ c = 255 := by
      rw [slot_spliceBits _ _ (by omega) (by omega), if_neg (by omega)]; exact ht
    denote_step_reduce v 97 [LLVM.const?] fold
    refine term_condBr (fun b hb => ?_)
    refine ⟨fun _ h => Sum.noConfusion h, fun t hT => ?_⟩
    obtain rfl := Sum.inr.inj hT
    split
    · simp only [Target.denote_mk, HVector.map, simp_spine]
      exact Reach.bb7 c x43 x44 x45 hc hu' ht'
    · exact Reach.bb23 hu'


set_option maxRecDepth 100000 in
theorem step_bb23 (_hV : EntryEnv V slides) (_hsl : IsSlidesPtr s.mem slides) {u : GlobalState}
    {w : BitVec 4096} (hu : u ≈ Sw s slides w) :
    ∃ res, StateT.run ((fd_curve25519_scalar_wnaf.blocks.get 22 rfl).2.denote
      (Ctxt.Valuation.ofHVector (.nil : HVector (@TyDenote.toType SLLVM.Ty _) ([] : List SLLVM.Ty)).reverse ++ V)) u
        = res ∧ ∀ p u', res = .value (p, u') → Post s slides p u' := by
  dsimp only [fd_curve25519_scalar_wnaf, Blocks.get]
  refine term_ret ?_
  exact ⟨fun _ _ => ⟨w, hu⟩, fun _ h => Sum.noConfusion h⟩

end Steps

/-! ## Entering and leaving -/

theorem run_runFunction_inv {α : Type} {body : EffectM α} {s s' : GlobalState} {r : α}
    (h : StateT.run (runFunction body) s = .value (r, s')) :
    ∃ t, StateT.run body s = .value (r, t) ∧ s' = s.popFrame t.mem := by
  match hb : StateT.run body s with
  | .poison =>
    rw [run_runFunction_poison hb] at h
    exact absurd h.symm (PoisonOr.value_ne_poison _)
  | .value (r', t) =>
    rw [run_runFunction hb] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (PoisonOr.value_inj.mp h)
    exact ⟨t, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `^bb0`: nineteen constants and `-1 << bits`, then `br ^bb2(0)`. -/
theorem entry_run (slides n : Pointer) (bits : BitVec 32) (s : GlobalState) :
    ∃ Vout, StateT.run (fd_curve25519_scalar_wnaf.entry.denote (Ctxt.Valuation.ofHVector
        [PoisonOr.value bits, PoisonOr.value n, PoisonOr.value slides]ₕ)) s
      = .value ((Vout, .inr ⟨1, rfl, [v64 0]ₕ⟩), s) ∧ EntryEnv Vout slides := by
  denote_step_reduce v 18 [LLVM.const?] fold
  subst hv1 hv5 hv6 hv7 hv8 hv9 hv13 hv14 hv16 hv17
  refine ⟨?V, ?run, ?env⟩
  case run =>
    simp only [BlockCom.denote_term, Terminator.denote_br, simp_denote, simp_sllvm]
    rfl
  case env => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem steps {s : GlobalState} {slides : Pointer} {V : fd_curve25519_scalar_wnaf.Γout.Valuation}
    (hs : s.WF) (hV : EntryEnv V slides) (hsl : IsSlidesPtr s.mem slides) :
    ∀ t u, Reach s slides t u → ∃ res,
      StateT.run ((fd_curve25519_scalar_wnaf.blocks.get t.idx t.hidx).2.denote
          (Ctxt.Valuation.ofHVector t.args.reverse ++ V)) u = res ∧ ∀ p u',
      res = .value (p, u') →
      (∀ rs, p.2 = .inl rs → Done s slides u') ∧ (∀ t', p.2 = .inr t' → Reach s slides t' u') := by
  intro t u h
  cases h with
  | bb1 => exact step_bb1 hV hsl ‹_›
  | bb2 => exact step_bb2 hV hsl _ ‹_› ‹_›
  | bb3 => exact step_bb3 hV hsl _ _ ‹_› ‹_› ‹_›
  | bb4 => exact step_bb4 hV hsl _ _ ‹_› ‹_› ‹_›
  | bb5 => exact step_bb5 hV hsl _ _ ‹_› ‹_› ‹_›
  | bb6 => exact step_bb6 hV hsl _ _ ‹_› ‹_› ‹_›
  | bb7 => exact step_bb7 hV hsl _ _ _ _ ‹_› ‹_› ‹_›
  | bb8 => exact step_bb8 hV hsl _ _ _ _ ‹_› ‹_› ‹_›
  | bb9 => exact step_bb9 hV hsl _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb10 => exact step_bb10 hs hV hsl _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb11 => exact step_bb11 hV hsl _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb12 => exact step_bb12 hV hsl _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb13 => exact step_bb13 hV hsl _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb14 => exact step_bb14 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb15 => exact step_bb15 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb16 => exact step_bb16 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb17 => exact step_bb17 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb18 => exact step_bb18 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb19 => exact step_bb19 hV hsl _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb20 => exact step_bb20 hV hsl _ _ ‹_› ‹_›
  | bb21 => exact step_bb21 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb22 => exact step_bb22 hV hsl _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | bb23 => exact step_bb23 hV hsl ‹_›

end Wnaf

open Wnaf in
/-- **`fd_curve25519_scalar_wnaf` writes nowhere but `slides`.** -/
theorem fd_curve25519_scalar_wnaf_frame (slides n : Pointer) (bits : BitVec 32) (s : GlobalState)
    (hs : s.WF) (hsl : IsSlidesPtr s.mem slides) :
    fd_curve25519_scalar_wnaf_frame_spec slides n bits s := by
  simp only [fd_curve25519_scalar_wnaf_frame_spec, Cfg.denote]
  refine ⟨_, rfl, fun s' h => ?_⟩
  obtain ⟨t, hbody, rfl⟩ := run_runFunction_inv h
  obtain ⟨Vout, hentry, hV⟩ := entry_run slides n bits s
  rw [EffectM.run_bind, hentry, PoisonOr.value_bind] at hbody
  -- the buffer as it is on entry
  obtain ⟨blk, hblk, -⟩ := hsl.1
  have hl : s.mem.live? slides.id = some blk := by simp [MemoryState.live?, hblk]
  have hu₀ : s ≈ Sw s slides (blk.bytes.extractLsb' slides.offsetInBits 4096) :=
    ⟨rfl, rfl, fun q => (live?_splice_self hl q).symm⟩
  obtain ⟨w, hw⟩ := Blocks.run_inv (bs := fd_curve25519_scalar_wnaf.blocks) (Vamb := Vout)
    (Reach s slides) (fun _ u => Done s slides u) (steps hs hV hsl)
    (Reach.bb2 0 (by omega) hu₀) _ _ hbody
  refine ⟨w, (popFrame_equiv_splice hs (lt_nextFreeBlock_of_fits hs hsl.1)
    (fun b _ hb => ?_) (hw.live slides.id)).symm⟩
  rw [hw.live b, live?_splice_ne (fun h => hb h.symm)]

end Firedancer.Common
