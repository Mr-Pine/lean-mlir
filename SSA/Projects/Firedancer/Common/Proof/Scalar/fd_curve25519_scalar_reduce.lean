/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Common.Proof.fd_ulong_load_8
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_curve25519_scalar_reduce` writes nowhere but `out`

The memory-footprint half of the specification. What the four stored words *are*
is not proved here -- see `Common/Spec/Scalar/fd_curve25519_scalar_reduce.lean` for why,
and the `wip/scalar-reduce-arithmetic` branch for how far that got.

The derivation is a straight walk. The eight `fd_ulong_load_8` calls are taken in
continuation form; everything from `%61` to `%454` is pure and is stepped without
reduction, which is what makes a 394-instruction stretch cheap -- the stepper is
term surgery, and nothing here needs to know what the arithmetic computes. The
four stores are then peeled, each after a case split on whether its operand is
poison.

That case split is the whole reason the statement has a poison disjunct: an
`nsw` operation whose bound is unproved may be poison for all this file knows,
and `SLLVM.store` takes `getOrUB` of the value it is handed, so a poison operand
sends the entire run to poison.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

-- reached only through its conformance theorem
attribute [local irreducible] fd_ulong_load_8

/-! ## Poison propagation

`SLLVM.store` takes `getOrUB` of the value it is handed, so a store fed poison
is UB and everything after it is poison. These four carry that from the operand
to the whole run; they are the poison-side counterparts of what `peel_store`
does on the value side. -/

/-- A poison step poisons everything after it. -/
theorem run_bind_of_poison {α β : Type} {x : EffectM α} {f : α → EffectM β}
    {s : GlobalState} (h : StateT.run x s = .poison) :
    StateT.run (x >>= f) s = .poison := by
  rw [EffectM.run_bind, h]; rfl

/-- ... and mapping over it does not rescue it. -/
theorem run_map_of_poison {α β : Type} {f : α → β} {x : EffectM α} {s : GlobalState}
    (h : StateT.run x s = .poison) : StateT.run (f <$> x) s = .poison := by
  rw [EffectM.run_map, h]; rfl

/-- ... nor does lifting a memory action that is itself UB. -/
theorem run_liftM_of_poison {α : Type} {x : MemorySSAM α} {s : GlobalState}
    (h : x.run s.mem = .poison) : (liftM x : EffectM α).run s = .poison := by
  cases s
  simp only [liftM, monadLift, MonadLift.monadLift, StateT.run] at *
  rw [h]

/-- A store whose value is poison is UB. -/
theorem run_store_of_poison {t : LLVM.Ty} {x : TyDenote.toType t} {p : Pointer}
    {m : MemoryState} (hx : LLVM.Ty.flatten t x = .poison) :
    (store (.value p) t x).run m = .poison := by
  simp [store, PoisonOr.getOrUB, hx]

/-- An impure instruction that is UB poisons the rest of the block. -/
theorem BlockCom.run_bind_denote_var_of_poison {Γ Γout : Ctxt SLLVM.Ty} {rets succs β}
    {e : Expr SLLVM Γ .impure []}
    {body : BlockCom (([] : List SLLVM.Ty) ++ Γ) Γout rets succs}
    {V : Γ.Valuation} {k : _ → EffectM β} {s : GlobalState}
    (h : StateT.run (e.denoteOp V) s = .poison) :
    StateT.run ((BlockCom.var e body).denote V >>= k) s = .poison := by
  rw [BlockCom.denote_var, bind_assoc, Expr.denote_unfold]
  exact run_bind_of_poison (run_map_of_poison h)

/-- Two memories that agree everywhere still agree after the same store: the
block written is settled by `live?_splice_congr`, every other one is missed.

Stated as a `∀ r`, so four stores are four applications and the pointers are
whatever the goal has -- no need for them to be syntactically `withOffset`s of
a common base. -/
private theorem live?_splice_both {m₁ m₂ : MemoryState} {p : Pointer} {w : Nat} {x : BitVec w}
    (h : ∀ r, m₁.live? r = m₂.live? r) (r : BlockId) :
    (m₁.splice p x).live? r = (m₂.splice p x).live? r := by
  by_cases hr : r = p.id
  · subst hr; exact live?_splice_congr (h p.id)
  · rw [live?_splice_ne (fun e => hr e.symm), live?_splice_ne (fun e => hr e.symm)]
    exact h r

/-- The four-store instance of `live?_splice_both`, with the shape spelled out.

The chained form elaborates by unifying a nest of four splices against the
goal, and at this point both sides are large; giving the pattern directly keeps
that search from running away. -/
private theorem live?_four {m₁ m₂ : MemoryState} {p q r t : Pointer} {a b c d : BitVec 64}
    (h : ∀ z, m₁.live? z = m₂.live? z) (z : BlockId) :
    ((((m₁.splice p a).splice q b).splice r c).splice t d).live? z
      = ((((m₂.splice p a).splice q b).splice r c).splice t d).live? z :=
  live?_splice_both (live?_splice_both (live?_splice_both (live?_splice_both h))) z

/-- Name a subterm without reverting the goal, as `obtain` would. -/
private theorem name_of {α : Sort u} (a : α) {P : Prop} (k : ∀ x, x = a → P) : P := k a rfl

/-- Case on a register being poison or a value, in continuation form: the
register stays abstract in the goal, so a later `peel_store` matches on the
program rather than on a substituted `PoisonOr` literal. -/
private theorem poison_cases {α : Type} {v : PoisonOr α} {P : Prop}
    (hp : v = .poison → P) (hv : ∀ a, v = .value a → P) : P := by
  cases v with
  | poison => exact hp rfl
  | value a => exact hv a rfl

/-- The poison branch of a store: the value handed to it is poison, so the store
is UB, the run is poison, and the specification's implication is vacuous. Four
stores, one tactic. -/
macro "store_poison " h:term : tactic =>
  `(tactic|
    (refine ⟨.poison, ?_, by intro s' h'; exact absurd h'.symm (PoisonOr.value_ne_poison _)⟩
     refine BlockCom.run_bind_denote_var_of_poison ?_
     simp only [Expr.denoteOp, $h:term, simp_denote, simp_sllvm]
     rfl))

/-- `run_runFunction'` for the named-result shape: cross the call boundary once,
carrying whatever the body left. Poison passes straight through and makes the
conclusion vacuous, which is the whole point of naming the result. -/
private theorem runFunction_res {α : Type} {body : EffectM α} {s : GlobalState}
    {rets : α} (P : GlobalState → Prop)
    (h : ∃ res, StateT.run body s = res
      ∧ ∀ t : GlobalState, res = .value (rets, t) → P (s.popFrame t.mem)) :
    ∃ res, StateT.run (runFunction body) s = res
      ∧ ∀ s' : GlobalState, res = .value (rets, s') → P s' := by
  obtain ⟨res, hres, hQ⟩ := h
  cases res with
  | poison =>
      exact ⟨.poison, run_runFunction_poison hres,
        by intro s' h'; exact absurd h'.symm (PoisonOr.value_ne_poison _)⟩
  | value p =>
      obtain ⟨r, t⟩ := p
      refine ⟨.value (r, s.popFrame t.mem), run_runFunction hres, ?_⟩
      intro s' h'
      rw [PoisonOr.value_inj, Prod.mk.injEq] at h'
      exact h'.2 ▸ hQ t (by rw [h'.1])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem fd_curve25519_scalar_reduce_frame (out inp : Pointer) (s : GlobalState)
    (hs : s.WF) (hin : Fits s.mem inp (64 * 8)) (hout : IsByteBufPtr s.mem out) :
    fd_curve25519_scalar_reduce_frame_spec out inp s := by
  simp only [fd_curve25519_scalar_reduce_frame_spec, Cfg.denote]
  refine runFunction_res _ ?_

  -- `%0`-`%45`: the constants, left unsubstituted so they don't inline into every later term.
  denote_step_reduce v 45 [LLVM.const?] fold

  -- `%46`: `fd_ulong_load_8( in )`
  have hf₀ : Fits s.mem inp 64 := Fits.mono hin (by omega)
  refine fd_ulong_load_8_conforms_cont inp s hs hf₀ fun t₀ hcall₀ he₀ => ?_
  peel_call hcall₀
  have hwf₀ : t₀.WF := hs.of_equiv he₀
  have hin₀ : Fits t₀.mem inp (64 * 8) := fits_of_live?_eq (he₀.live inp.id).symm hin

  -- `%47`/`%48`: `in + 8`
  peel_gep 8 with inp, hin₀, t₀ as in8
  refine fd_ulong_load_8_conforms_cont in8 t₀ hwf₀ (Fits.mono hin8 (by decide)) fun t₁ hcall₁ he₁ => ?_
  peel_call hcall₁
  have hwf₁ : t₁.WF := hwf₀.of_equiv he₁
  have hin₁ : Fits t₁.mem inp (64 * 8) := fits_of_live?_eq (he₁.live inp.id).symm hin₀

  -- `%49`/`%50`: `in + 16`
  peel_gep 16 with inp, hin₁, t₁ as in16
  refine fd_ulong_load_8_conforms_cont in16 t₁ hwf₁ (Fits.mono hin16 (by decide)) fun t₂ hcall₂ he₂ => ?_
  peel_call hcall₂
  have hwf₂ : t₂.WF := hwf₁.of_equiv he₂
  have hin₂ : Fits t₂.mem inp (64 * 8) := fits_of_live?_eq (he₂.live inp.id).symm hin₁

  -- `%51`/`%52`: `in + 24`
  peel_gep 24 with inp, hin₂, t₂ as in24
  refine fd_ulong_load_8_conforms_cont in24 t₂ hwf₂ (Fits.mono hin24 (by decide)) fun t₃ hcall₃ he₃ => ?_
  peel_call hcall₃
  have hwf₃ : t₃.WF := hwf₂.of_equiv he₃
  have hin₃ : Fits t₃.mem inp (64 * 8) := fits_of_live?_eq (he₃.live inp.id).symm hin₂

  -- `%53`/`%54`: `in + 32`
  peel_gep 32 with inp, hin₃, t₃ as in32
  refine fd_ulong_load_8_conforms_cont in32 t₃ hwf₃ (Fits.mono hin32 (by decide)) fun t₄ hcall₄ he₄ => ?_
  peel_call hcall₄
  have hwf₄ : t₄.WF := hwf₃.of_equiv he₄
  have hin₄ : Fits t₄.mem inp (64 * 8) := fits_of_live?_eq (he₄.live inp.id).symm hin₃

  -- `%55`/`%56`: `in + 40`
  peel_gep 40 with inp, hin₄, t₄ as in40
  refine fd_ulong_load_8_conforms_cont in40 t₄ hwf₄ (Fits.mono hin40 (by decide)) fun t₅ hcall₅ he₅ => ?_
  peel_call hcall₅
  have hwf₅ : t₅.WF := hwf₄.of_equiv he₅
  have hin₅ : Fits t₅.mem inp (64 * 8) := fits_of_live?_eq (he₅.live inp.id).symm hin₄

  -- `%57`/`%58`: `in + 48`
  peel_gep 48 with inp, hin₅, t₅ as in48
  refine fd_ulong_load_8_conforms_cont in48 t₅ hwf₅ (Fits.mono hin48 (by decide)) fun t₆ hcall₆ he₆ => ?_
  peel_call hcall₆
  have hwf₆ : t₆.WF := hwf₅.of_equiv he₆
  have hin₆ : Fits t₆.mem inp (64 * 8) := fits_of_live?_eq (he₆.live inp.id).symm hin₅

  -- `%59`/`%60`: `in + 56`
  peel_gep 56 with inp, hin₆, t₆ as in56
  refine fd_ulong_load_8_conforms_cont in56 t₆ hwf₆ (Fits.mono hin56 (by decide)) fun t₇ hcall₇ he₇ => ?_
  peel_call hcall₇
  have hwf₇ : t₇.WF := hwf₆.of_equiv he₇

  -- the eight loads are done and no store has run, so the state is still `s`
  have heq : s ≈ t₇ :=
    he₀.trans (he₁.trans (he₂.trans (he₃.trans (he₄.trans (he₅.trans (he₆.trans he₇))))))

  -- `%61`-`%454`: the unpacking, the reduction and the carry chains. Pure, and
  -- stepped without reduction -- what the arithmetic computes is irrelevant to
  -- the footprint, and not reducing is what keeps 394 instructions cheap.
  denote_step_all v 454

  -- `out` is still a 32-byte buffer at every state the loads left
  have hout₇ : Fits t₇.mem out (32 * 8) := fits_of_live?_eq (heq.live out.id).symm hout.left

  -- the first store, `out + 0`. Poison here is UB, and UB is the whole run.
  refine poison_cases (v := v454) (fun hb0 => ?_) (fun b0 hb0 => ?_)
  · store_poison hb0
  refine name_of ({ t₇ with mem := t₇.mem.splice out b0 } : GlobalState) fun u₀ hu₀ => ?_
  rw [hb0]
  peel_store b0, out, hout₇, t₇ as u₀ := hu₀
  have hout₀ : Fits u₀.mem out (32 * 8) := by rw [hu₀]; exact fits_splice hout₇

  -- `%455`-`%464`, then `%465 = out + 8` and the second store
  denote_step_all v 464
  peel_gep 8 with out, hout₀, u₀ as out8
  -- `peel_store`'s own `omega` needs a literal width, and `peel_gep` leaves
  -- `256 - BitVec.toNat 8 * 8`; normalise it once.
  have hout8N : Fits u₀.mem out8 64 := Fits.mono hout8 (by decide)
  refine poison_cases (v := v464) (fun hb1 => ?_) (fun b1 hb1 => ?_)
  · store_poison hb1
  refine name_of ({ u₀ with mem := u₀.mem.splice out8 b1 } : GlobalState) fun u₁ hu₁ => ?_
  rw [hb1]
  peel_store b1, out8, hout8N, u₀ as u₁ := hu₁
  have hout₁ : Fits u₁.mem out (32 * 8) := by rw [hu₁]; exact fits_splice hout₀

  -- `%466`-`%475`, then `%476 = out + 16` and the third store
  denote_step_all v 475
  peel_gep 16 with out, hout₁, u₁ as out16
  -- `peel_store`'s own `omega` needs a literal width, and `peel_gep` leaves
  -- `256 - BitVec.toNat 16 * 8`; normalise it once.
  have hout16N : Fits u₁.mem out16 64 := Fits.mono hout16 (by decide)
  refine poison_cases (v := v475) (fun hb2 => ?_) (fun b2 hb2 => ?_)
  · store_poison hb2
  refine name_of ({ u₁ with mem := u₁.mem.splice out16 b2 } : GlobalState) fun u₂ hu₂ => ?_
  rw [hb2]
  peel_store b2, out16, hout16N, u₁ as u₂ := hu₂
  have hout₂ : Fits u₂.mem out (32 * 8) := by rw [hu₂]; exact fits_splice hout₁

  -- `%477`-`%483`, then `%484 = out + 24` and the fourth store
  denote_step_all v 483
  peel_gep 24 with out, hout₂, u₂ as out24
  -- `peel_store`'s own `omega` needs a literal width, and `peel_gep` leaves
  -- `256 - BitVec.toNat 24 * 8`; normalise it once.
  have hout24N : Fits u₂.mem out24 64 := Fits.mono hout24 (by decide)
  refine poison_cases (v := v483) (fun hb3 => ?_) (fun b3 hb3 => ?_)
  · store_poison hb3
  refine name_of ({ u₂ with mem := u₂.mem.splice out24 b3 } : GlobalState) fun u₃ hu₃ => ?_
  rw [hb3]
  peel_store b3, out24, hout24N, u₂ as u₃ := hu₃

  -- `llvm.return %arg0`: the region hands back `out`, and the memory it leaves
  -- is `t₇`'s with the four stores. `t₇` is `s` up to equivalence, and all four
  -- stores address the same block, so the two sides agree block for block.
  -- The four states differ from `t₇` only in `mem`; project one level at a time
  -- rather than `simp`ing with the four equations, which would unfold `mem`.
  have m₃ : u₃.mem = u₂.mem.splice out24 b3 := by rw [hu₃]
  have m₂ : u₂.mem = u₁.mem.splice out16 b2 := by rw [hu₂]
  have m₁ : u₁.mem = u₀.mem.splice out8 b1 := by rw [hu₁]
  have m₀ : u₀.mem = t₇.mem.splice out b0 := by rw [hu₀]

  -- `llvm.return %arg0`: the region hands back `out`.
  refine ⟨.value ([.value out]ₕ, u₃), ?_, ?_⟩
  · simp_return
  · intro s' h'
    rw [PoisonOr.value_inj, Prod.mk.injEq] at h'
    refine ⟨![b0, b1, b2, b3], ?_⟩
    rw [← h'.2]
    -- The body's state is popped on return, so this is `popFrame_equiv_block`:
    -- `out`'s block is the only one written, and nothing was allocated.
    have hoblk : out.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hout.left
    refine popFrame_equiv_block hs hoblk ?_ ?_ ?_
    · -- every other block reads as it did on entry
      intro b _ hb
      have e0 : out.id ≠ b := fun e => hb e.symm
      have e1 : out8.id ≠ b := fun e => hb e.symm
      have e2 : out16.id ≠ b := fun e => hb e.symm
      have e3 : out24.id ≠ b := fun e => hb e.symm
      rw [m₃, m₂, m₁, m₀, live?_splice_ne e3, live?_splice_ne e2, live?_splice_ne e1,
        live?_splice_ne e0]
      exact (heq.live b).symm
    · -- ... and the four stores miss it on the specification's side too
      intro b hb
      have e0 : out.id ≠ b := fun e => hb e.symm
      have e1 : (out.withOffset 8).id ≠ b := fun e => hb e.symm
      have e2 : (out.withOffset 16).id ≠ b := fun e => hb e.symm
      have e3 : (out.withOffset 24).id ≠ b := fun e => hb e.symm
      simp only [scalarOutMem, live?_splice_ne e3, live?_splice_ne e2, live?_splice_ne e1,
        live?_splice_ne e0]
    · -- on `out`'s own block the two agree, store for store
      rw [m₃, m₂, m₁, m₀]
      -- `out8`/`out16`/`out24` are `peel_gep`'s local definitions; unfold them so
      -- both sides name the same pointers and the four congruences line up.
      simp only [out8, out16, out24, scalarOutMem, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
      exact live?_four (fun z => (heq.live z).symm) out.id

/-! ## The call is decided by the 512 bits at `in`

One walk, with the eight loaded words rewritten to slices of the 512 bits `k` at `in`, so every
value the stepper produces is a term in `k` alone. The witness for `ScalarReduceDetermined` is
then read off the four store operands by unification: it is never written down, and what the
arithmetic computes is still never needed.
-/

/-- A read of the same block at the same place, across states that agree on it. -/
private theorem readWord_congr {m m' : MemoryState} {p : Pointer} {w : Nat}
    (hl : m'.live? p.id = m.live? p.id) (h : Fits m p w) {h' : Fits m' p w} :
    readWord h' = readWord h := (readWord_of_live?_eq hl h).2

/-- `p + o` in bits, when the sum does not wrap. -/
private theorem offsetInBits_withOffset (p : Pointer) (o : BitVec 64)
    (h : p.offset.toNat + o.toNat < 2 ^ 64) :
    (p.withOffset o).offsetInBits = p.offsetInBits + 8 * o.toNat := by
  simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, Nat.mod_eq_of_lt h]
  omega

/-! ### Values as functions of the input bits

`Det k v g` is the bare equation `v = g k`. The point is where `g` comes from: it is never
written here, but built one instruction at a time by `det₁`/`det₂`, which only abstract -- they
never look at what the operation computes. A value whose operands are made of `k` is made of `k`.
-/

variable {α β γ K : Type}

/-- `v` is what `g` makes of the input `k`. -/
def Det (k : K) (v : α) (g : K → α) : Prop := v = g k

/-- A constant is made of nothing. -/
theorem det_const (k : K) (c : α) : Det k c (fun _ => c) := rfl

theorem det₁ (k : K) {v : α} {g : K → α} (F : α → β) (h : Det k v g) :
    Det k (F v) (fun x => F (g x)) := by unfold Det at h ⊢; rw [h]

theorem det₂ (k : K) {v₁ : α} {v₂ : β} {g₁ : K → α} {g₂ : K → β} (F : α → β → γ)
    (h₁ : Det k v₁ g₁) (h₂ : Det k v₂ g₂) :
    Det k (F v₁ v₂) (fun x => F (g₁ x) (g₂ x)) := by unfold Det at h₁ h₂ ⊢; rw [h₁, h₂]

/-- The stepper leaves `hvᵢ : vᵢ = …`; this turns such an equation into a `Det`. -/
theorem det_of_eq {k : K} {v v' : α} {g : K → α} (h : v = v') (hd : Det k v' g) : Det k v g := by
  unfold Det at hd ⊢; rw [h, hd]

/-- What a load contributes: its slice of the input bits. -/
theorem det_slice (k : BitVec (64 * 8)) (i : Nat) :
    Det k (k.extractLsb' (64 * i) 64) (fun x => x.extractLsb' (64 * i) 64) := rfl

/-- A value made only of the input. Covers constants and the loads' slices alike: `F` is `e`
with `k` abstracted out. -/
theorem det₀' (k : K) (F : K → α) : Det k (F k) (fun x => F x) := rfl

/-- One threaded operand. `F` takes `k` too, since the rest of the term may mention it. -/
theorem det₁' (k : K) (F : K → α → β) {v : α} {g : K → α} (h : Det k v g) :
    Det k (F k v) (fun x => F x (g x)) := by unfold Det at h ⊢; rw [h]

theorem det₂' (k : K) (F : K → α → β → γ) {v₁ : α} {v₂ : β} {g₁ : K → α} {g₂ : K → β}
    (h₁ : Det k v₁ g₁) (h₂ : Det k v₂ g₂) :
    Det k (F k v₁ v₂) (fun x => F x (g₁ x) (g₂ x)) := by unfold Det at h₁ h₂ ⊢; rw [h₁, h₂]

theorem det₃' (k : K) (F : K → α → β → γ → δ) {v₁ : α} {v₂ : β} {v₃ : γ}
    {g₁ : K → α} {g₂ : K → β} {g₃ : K → γ}
    (h₁ : Det k v₁ g₁) (h₂ : Det k v₂ g₂) (h₃ : Det k v₃ g₃) :
    Det k (F k v₁ v₂ v₃) (fun x => F x (g₁ x) (g₂ x) (g₃ x)) := by
  unfold Det at h₁ h₂ h₃ ⊢; rw [h₁, h₂, h₃]

theorem det₄' (k : K) (F : K → α → β → γ → δ → ε) {v₁ : α} {v₂ : β} {v₃ : γ} {v₄ : δ}
    {g₁ : K → α} {g₂ : K → β} {g₃ : K → γ} {g₄ : K → δ}
    (h₁ : Det k v₁ g₁) (h₂ : Det k v₂ g₂) (h₃ : Det k v₃ g₃) (h₄ : Det k v₄ g₄) :
    Det k (F k v₁ v₂ v₃ v₄) (fun x => F x (g₁ x) (g₂ x) (g₃ x) (g₄ x)) := by
  unfold Det at h₁ h₂ h₃ h₄ ⊢; rw [h₁, h₂, h₃, h₄]

-- the lemmas above are all the ways a `Det` is built or used; unfolding it during a walk means
-- defeq checks against every stepped equation in the context
attribute [irreducible] Det

open Lean Elab Tactic Meta in
/-- `det_range k lo hi` turns each `hvᵢ` the stepper left, `lo ≤ i ≤ hi`, into `dᵢ : Det k vᵢ _`.

The witness is built, never searched for: the operands are read off `hvᵢ`'s right-hand side, `F`
is that side with `k` and those operands abstracted out, and the matching `detₙ'` is applied. A
`refine detₙ _ _ ?_ ?_` instead leaves `?F ?a ?b =?= rhs` to higher-order unification, which cost
about 1.3s per instruction. -/
elab "det_range " kt:ident ppSpace lo:num ppSpace hi:num : tactic => do
  for i in [lo.getNat : hi.getNat + 1] do
    let goal ← getMainGoal
    let prf ← goal.withContext do
      let kfv ← elabTerm kt none
      let lctx ← getLCtx
      let some hvDecl := lctx.findFromUserName? (Name.mkSimple ("hv" ++ toString i))
        | throwError "det_range: no hv{i}"
      let some (_, _, rhs) := (← instantiateMVars hvDecl.type).eq?
        | throwError "det_range: hv{i} is not an equation"
      -- the operands already threaded: the `vⱼ` in `rhs` that have a `dⱼ`
      let mut vs : Array Expr := #[]
      let mut ds : Array Expr := #[]
      for fid in (Lean.collectFVars {} rhs).fvarIds do
        let n := (← fid.getUserName).toString
        if n.startsWith "v" then
          if let some dDecl := lctx.findFromUserName? (Name.mkSimple ("d" ++ n.drop 1)) then
            vs := vs.push (mkFVar fid)
            ds := ds.push dDecl.toExpr
      let F ← mkLambdaFVars (#[kfv] ++ vs) rhs
      let lemmaName := match vs.size with
        | 0 => ``det₀' | 1 => ``det₁' | 2 => ``det₂' | 3 => ``det₃' | 4 => ``det₄'
        | n => panic! s!"det_range: {n} operands"
      let core ← mkAppM lemmaName (#[kfv, F] ++ ds)
      mkAppM ``det_of_eq #[hvDecl.toExpr, core]
    let goal ← goal.assert (Name.mkSimple ("d" ++ toString i)) (← inferType prf) prf
    let (_, goal) ← goal.intro1P
    replaceMainGoal [goal]

/-- The four store operands as an outcome: `none` as soon as one of them is poison. -/
def wordsOf (a b c d : PoisonOr (BitVec 64)) : Option (Fin 4 → BitVec 64) :=
  match a, b, c, d with
  | .value a, .value b, .value c, .value d => some ![a, b, c, d]
  | _, _, _, _ => none

/-- A load inside the 512 bits at `inp` returns its slice of them. -/
theorem readWord_load_slice {m : MemoryState} {inp q : Pointer} (hin : Fits m inp (64 * 8))
    (hid : q.id = inp.id) {i : Nat} (hi : i < 8)
    (hoff : q.offsetInBits = inp.offsetInBits + 64 * i) {hp : Fits m q 64} :
    readWord hp = (readWord hin).extractLsb' (64 * i) 64 := by
  obtain ⟨blk, hlive⟩ : ∃ blk, m.live? inp.id = some blk := by
    obtain ⟨blk, hblk, -⟩ := hin
    exact ⟨blk, by simp only [MemoryState.live?, hblk]⟩
  have hw : readWord hin = blk.bytes.extractLsb' inp.offsetInBits (64 * 8) :=
    readWord_eq_of (by
      simp only [readWord?, hlive, Option.bind_eq_bind, Option.bind_some, Option.pure_def])
  apply readWord_eq_of
  simp only [readWord?, hid, hlive, hoff, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq, hw]
  ext k hk
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_extractLsb', decide_eq_true (by omega : 64 * i + k < 64 * 8), Bool.true_and]
  congr 1
  omega

/-- What the run does, with the four store operands left abstract: the result is named, as in
`fd_curve25519_scalar_reduce_frame_spec`, so a walk can step it in place. -/
private def Stores (out inp : Pointer) (s : GlobalState) (a b c d : PoisonOr (BitVec 64)) : Prop :=
  ∃ res, StateT.run (runFunction (fd_curve25519_scalar_reduce.denote
      (Ctxt.Valuation.ofHVector [.value inp, .value out]ₕ))) s = res
    ∧ (∀ w, wordsOf a b c d = some w →
        ∃ s' : GlobalState, res = .value ([.value out]ₕ, s')
          ∧ s' ≈ ({ s with mem := scalarOutMem s.mem out w } : GlobalState))
    ∧ (wordsOf a b c d = none → res = .poison)

/-- `Det`'s equation, for rewriting. -/
theorem Det.eq {k : K} {v : α} {g : K → α} (h : Det k v g) : v = g k := by unfold Det at h; exact h

open Lean Elab Tactic Meta in
/-- `det_pin d₀ d₁ …` fixes the goal's witnesses to the functions those `Det` facts carry, left
to right. The witnesses are metavariables shared by every branch of the walk, and a branch that
stops early -- a store handed poison -- still has to pin the ones it knows. -/
elab "det_pin" ds:(ppSpace colGt ident)* : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some app := tgt.find? (·.isAppOfArity ``wordsOf 4)
    | throwError "det_pin: no `wordsOf` in the goal"
  let args := app.getAppArgs
  for h : i in [0 : ds.size] do
    let dTy ← instantiateMVars (← inferType (← elabTerm ds[i] none))
    let dargs := dTy.getAppArgs
    unless dargs.size ≥ 3 do throwError "det_pin: {ds[i]} is not a `Det` fact"
    unless ← isDefEq args[i]! (mkApp dargs[dargs.size - 1]! dargs[dargs.size - 3]!) do
      throwError "det_pin: could not pin witness {i}"

/-- The witness, assembled from four functions of the input bits. `E₀ … E₃` are never written:
the walk below supplies them, and unification abstracts them over `k`. -/
private theorem scalarReduceBy_of_stores (E₀ E₁ E₂ E₃ : BitVec (64 * 8) → PoisonOr (BitVec 64))
    (h : ∀ (out inp : Pointer) (s : GlobalState), s.WF → IsByteBufPtr s.mem out →
      inp.offset.toNat + 64 ≤ 2 ^ 64 → ∀ hin : Fits s.mem inp (64 * 8),
        Stores out inp s (E₀ (readWord hin)) (E₁ (readWord hin)) (E₂ (readWord hin))
          (E₃ (readWord hin))) :
    ScalarReduceBy (fun k => wordsOf (E₀ k) (E₁ k) (E₂ k) (E₃ k)) := by
  intro out inp s hs hout hoff hin
  obtain ⟨res, hres, hsome, hnone⟩ := h out inp s hs hout hoff hin
  refine ⟨fun w hw => ?_, fun hn => ?_⟩
  · obtain ⟨s', hs', he⟩ := hsome w hw
    exact ⟨s', hres.trans hs', he⟩
  · exact hres.trans (hnone hn)

/-- `runFunction_res` for the `Stores` shape: cross the call boundary once, carrying whatever the
body left. -/
private theorem stores_runFunction {body : EffectM (HVector (@TyDenote.toType SLLVM.Ty _)
      [SLLVM.Ty.ptr])} {s : GlobalState} {out : Pointer} {a b c d : PoisonOr (BitVec 64)}
    {M : (Fin 4 → BitVec 64) → GlobalState}
    (h : ∃ res, StateT.run body s = res
      ∧ (∀ w, wordsOf a b c d = some w →
          ∃ t : GlobalState, res = .value ([.value out]ₕ, t) ∧ s.popFrame t.mem ≈ M w)
      ∧ (wordsOf a b c d = none → res = .poison)) :
    ∃ res, StateT.run (runFunction body) s = res
      ∧ (∀ w, wordsOf a b c d = some w →
          ∃ s' : GlobalState, res = .value ([.value out]ₕ, s') ∧ s' ≈ M w)
      ∧ (wordsOf a b c d = none → res = .poison) := by
  obtain ⟨res, hres, hsome, hnone⟩ := h
  cases res with
  | poison =>
      refine ⟨.poison, run_runFunction_poison hres, ?_, fun _ => rfl⟩
      intro w hw
      exact absurd (hsome w hw).choose_spec.1 (PoisonOr.value_ne_poison _).symm
  | value p =>
      obtain ⟨r, t⟩ := p
      refine ⟨.value (r, s.popFrame t.mem), run_runFunction hres, ?_, ?_⟩
      · intro w hw
        obtain ⟨t', ht', he⟩ := hsome w hw
        rw [PoisonOr.value_inj, Prod.mk.injEq] at ht'
        exact ⟨s.popFrame t.mem, by rw [ht'.1], ht'.2 ▸ he⟩
      · intro hn
        exact absurd (hnone hn) (PoisonOr.value_ne_poison _)

set_option maxHeartbeats 2000000 in
/-- **The call is decided by the 512 bits at `in`.** -/
theorem scalarReduce_determined : ScalarReduceDetermined := by
  -- `apply`, not `refine ⟨?E, …⟩`: the witnesses have to stay assignable by unification, and a
  -- `?`-named hole is synthetic opaque
  apply Exists.intro
  apply scalarReduceBy_of_stores
  · intro out inp s hs hout hinoff hin
    simp only [Stores, Cfg.denote]
    -- the 512 bits the call reads; every value below is a term in `k`
    generalize hk : readWord hin = k
    refine stores_runFunction (M := fun w => { s with mem := scalarOutMem s.mem out w }) ?_
    -- `%0`-`%45`: the constants, as in the frame walk
    denote_step_reduce v 45 [LLVM.const?] fold
    det_range k 0 45

    -- `%46`: `fd_ulong_load_8( in )`, returning the low 64 bits of `k`
    have hf₀ : Fits s.mem inp 64 := Fits.mono hin (by omega)
    refine fd_ulong_load_8_conforms_cont inp s hs hf₀ fun t0 hcall0 he0 => ?_
    rw [readWord_load_slice hin rfl (i := 0) (by omega) (by simp), hk] at hcall0
    peel_call hcall0
    -- `%47`/`%48`: `in + 8`, returning bits `64` to `128` of `k`
    have hwf0 : t0.WF := hs.of_equiv he0
    have hin0 : Fits t0.mem inp (64 * 8) :=
      fits_of_live?_eq (he0.live inp.id).symm hin
    have hk0 : readWord hin0 = k := by
      rw [readWord_congr (he0.live inp.id).symm hin]
      exact hk
    peel_gep 8 with inp, hin0, t0 as in8
    refine fd_ulong_load_8_conforms_cont in8 t0 hwf0 (Fits.mono hin8 (by decide))
      fun t1 hcall1 he1 => ?_
    rw [readWord_load_slice (q := in8) hin0 rfl (i := 1) (by omega)
      (by rw [offsetInBits_withOffset inp 8 (by simp; omega)]; rfl), hk0] at hcall1
    peel_call hcall1
    -- `%49`/`%50`: `in + 16`, returning bits `128` to `192` of `k`
    have hwf1 : t1.WF := hwf0.of_equiv he1
    have hin1 : Fits t1.mem inp (64 * 8) :=
      fits_of_live?_eq (he1.live inp.id).symm hin0
    have hk1 : readWord hin1 = k := by
      rw [readWord_congr (he1.live inp.id).symm hin0]
      exact hk0
    peel_gep 16 with inp, hin1, t1 as in16
    refine fd_ulong_load_8_conforms_cont in16 t1 hwf1 (Fits.mono hin16 (by decide))
      fun t2 hcall2 he2 => ?_
    rw [readWord_load_slice (q := in16) hin1 rfl (i := 2) (by omega)
      (by rw [offsetInBits_withOffset inp 16 (by simp; omega)]; rfl), hk1] at hcall2
    peel_call hcall2
    -- `%51`/`%52`: `in + 24`, returning bits `192` to `256` of `k`
    have hwf2 : t2.WF := hwf1.of_equiv he2
    have hin2 : Fits t2.mem inp (64 * 8) :=
      fits_of_live?_eq (he2.live inp.id).symm hin1
    have hk2 : readWord hin2 = k := by
      rw [readWord_congr (he2.live inp.id).symm hin1]
      exact hk1
    peel_gep 24 with inp, hin2, t2 as in24
    refine fd_ulong_load_8_conforms_cont in24 t2 hwf2 (Fits.mono hin24 (by decide))
      fun t3 hcall3 he3 => ?_
    rw [readWord_load_slice (q := in24) hin2 rfl (i := 3) (by omega)
      (by rw [offsetInBits_withOffset inp 24 (by simp; omega)]; rfl), hk2] at hcall3
    peel_call hcall3
    -- `%53`/`%54`: `in + 32`, returning bits `256` to `320` of `k`
    have hwf3 : t3.WF := hwf2.of_equiv he3
    have hin3 : Fits t3.mem inp (64 * 8) :=
      fits_of_live?_eq (he3.live inp.id).symm hin2
    have hk3 : readWord hin3 = k := by
      rw [readWord_congr (he3.live inp.id).symm hin2]
      exact hk2
    peel_gep 32 with inp, hin3, t3 as in32
    refine fd_ulong_load_8_conforms_cont in32 t3 hwf3 (Fits.mono hin32 (by decide))
      fun t4 hcall4 he4 => ?_
    rw [readWord_load_slice (q := in32) hin3 rfl (i := 4) (by omega)
      (by rw [offsetInBits_withOffset inp 32 (by simp; omega)]; rfl), hk3] at hcall4
    peel_call hcall4
    -- `%55`/`%56`: `in + 40`, returning bits `320` to `384` of `k`
    have hwf4 : t4.WF := hwf3.of_equiv he4
    have hin4 : Fits t4.mem inp (64 * 8) :=
      fits_of_live?_eq (he4.live inp.id).symm hin3
    have hk4 : readWord hin4 = k := by
      rw [readWord_congr (he4.live inp.id).symm hin3]
      exact hk3
    peel_gep 40 with inp, hin4, t4 as in40
    refine fd_ulong_load_8_conforms_cont in40 t4 hwf4 (Fits.mono hin40 (by decide))
      fun t5 hcall5 he5 => ?_
    rw [readWord_load_slice (q := in40) hin4 rfl (i := 5) (by omega)
      (by rw [offsetInBits_withOffset inp 40 (by simp; omega)]; rfl), hk4] at hcall5
    peel_call hcall5
    -- `%57`/`%58`: `in + 48`, returning bits `384` to `448` of `k`
    have hwf5 : t5.WF := hwf4.of_equiv he5
    have hin5 : Fits t5.mem inp (64 * 8) :=
      fits_of_live?_eq (he5.live inp.id).symm hin4
    have hk5 : readWord hin5 = k := by
      rw [readWord_congr (he5.live inp.id).symm hin4]
      exact hk4
    peel_gep 48 with inp, hin5, t5 as in48
    refine fd_ulong_load_8_conforms_cont in48 t5 hwf5 (Fits.mono hin48 (by decide))
      fun t6 hcall6 he6 => ?_
    rw [readWord_load_slice (q := in48) hin5 rfl (i := 6) (by omega)
      (by rw [offsetInBits_withOffset inp 48 (by simp; omega)]; rfl), hk5] at hcall6
    peel_call hcall6
    -- `%59`/`%60`: `in + 56`, returning bits `448` to `512` of `k`
    have hwf6 : t6.WF := hwf5.of_equiv he6
    have hin6 : Fits t6.mem inp (64 * 8) :=
      fits_of_live?_eq (he6.live inp.id).symm hin5
    have hk6 : readWord hin6 = k := by
      rw [readWord_congr (he6.live inp.id).symm hin5]
      exact hk5
    peel_gep 56 with inp, hin6, t6 as in56
    refine fd_ulong_load_8_conforms_cont in56 t6 hwf6 (Fits.mono hin56 (by decide))
      fun t7 hcall7 he7 => ?_
    rw [readWord_load_slice (q := in56) hin6 rfl (i := 7) (by omega)
      (by rw [offsetInBits_withOffset inp 56 (by simp; omega)]; rfl), hk6] at hcall7
    peel_call hcall7

    -- `%61`-`%454`: the reduction, threaded
    denote_step_all v 454
    det_range k 61 454

    -- `out` is still a 32-byte buffer at the state the loads left
    have heqs : s ≈ t7 :=
      he0.trans (he1.trans (he2.trans (he3.trans (he4.trans (he5.trans (he6.trans he7))))))
    have hout7 : Fits t7.mem out (32 * 8) := fits_of_live?_eq (heqs.live out.id).symm hout.left

    -- the first store, `out + 0`. Poison here is UB, and UB is the whole run.
    refine poison_cases (v := v454) (fun hb0 => ?_) (fun b0 hb0 => ?_)
    · refine ⟨.poison, ?_, ?_, fun _ => rfl⟩
      · refine BlockCom.run_bind_denote_var_of_poison ?_
        simp only [Expr.denoteOp, hb0, simp_denote, simp_sllvm]
        rfl
      · -- pin here, not before the run: the witness is the whole reduction as a term, and a
        -- `simp` over the run would then walk it
        det_pin d454
        intro w hw
        rw [← d454.eq, hb0] at hw
        simp [wordsOf] at hw
    refine name_of ({ t7 with mem := t7.mem.splice out b0 } : GlobalState) fun u₀ hu₀ => ?_
    rw [hb0]
    peel_store b0, out, hout7, t7 as u₀ := hu₀
    have hout₀ : Fits u₀.mem out (32 * 8) := by rw [hu₀]; exact fits_splice hout7
    sorry
  -- the four witnesses, left for the walk above to assign
  all_goals exact sorry

end Firedancer.Common
