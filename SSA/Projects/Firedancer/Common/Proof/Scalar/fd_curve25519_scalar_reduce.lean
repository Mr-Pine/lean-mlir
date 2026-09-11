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
continuation form; everything from `%66` to `%459` is pure and is stepped without
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
    (hs : s.WF) (hin : Fits s.mem inp (64 * 8)) (hout : IsScalar256Ptr s.mem out) :
    fd_curve25519_scalar_reduce_frame_spec out inp s := by
  simp only [fd_curve25519_scalar_reduce_frame_spec, Cfg.denote]
  refine runFunction_res _ ?_

  -- `%0`-`%50`: the constants. Only `%0`-`%6` (8, 16, ..., 56) are substituted;
  -- `peel_gep` matches on the literal offset. The rest stay as variables and
  -- are supplied to each step's own `simp` set instead -- substituting all
  -- fifty-one inlines them into every later term and costs more than it saves.
  denote_step_reduce v 50 [LLVM.const?] fold
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6

  -- `%51`: `fd_ulong_load_8( in )`
  have hf₀ : Fits s.mem inp 64 := Fits.mono hin (by omega)
  refine fd_ulong_load_8_conforms_cont inp s hs hf₀ fun t₀ hcall₀ he₀ => ?_
  peel_call hcall₀
  have hwf₀ : t₀.WF := hs.of_equiv he₀
  have hin₀ : Fits t₀.mem inp (64 * 8) := fits_of_live?_eq (he₀.live inp.id).symm hin

  -- `%52`/`%53`: `in + 8`
  peel_gep 8 with inp, hin₀, t₀ as in8
  refine fd_ulong_load_8_conforms_cont in8 t₀ hwf₀ (Fits.mono hin8 (by bv_omega)) fun t₁ hcall₁ he₁ => ?_
  peel_call hcall₁
  have hwf₁ : t₁.WF := hwf₀.of_equiv he₁
  have hin₁ : Fits t₁.mem inp (64 * 8) := fits_of_live?_eq (he₁.live inp.id).symm hin₀

  -- `%54`/`%55`: `in + 16`
  peel_gep 16 with inp, hin₁, t₁ as in16
  refine fd_ulong_load_8_conforms_cont in16 t₁ hwf₁ (Fits.mono hin16 (by bv_omega)) fun t₂ hcall₂ he₂ => ?_
  peel_call hcall₂
  have hwf₂ : t₂.WF := hwf₁.of_equiv he₂
  have hin₂ : Fits t₂.mem inp (64 * 8) := fits_of_live?_eq (he₂.live inp.id).symm hin₁

  -- `%56`/`%57`: `in + 24`
  peel_gep 24 with inp, hin₂, t₂ as in24
  refine fd_ulong_load_8_conforms_cont in24 t₂ hwf₂ (Fits.mono hin24 (by bv_omega)) fun t₃ hcall₃ he₃ => ?_
  peel_call hcall₃
  have hwf₃ : t₃.WF := hwf₂.of_equiv he₃
  have hin₃ : Fits t₃.mem inp (64 * 8) := fits_of_live?_eq (he₃.live inp.id).symm hin₂

  -- `%58`/`%59`: `in + 32`
  peel_gep 32 with inp, hin₃, t₃ as in32
  refine fd_ulong_load_8_conforms_cont in32 t₃ hwf₃ (Fits.mono hin32 (by bv_omega)) fun t₄ hcall₄ he₄ => ?_
  peel_call hcall₄
  have hwf₄ : t₄.WF := hwf₃.of_equiv he₄
  have hin₄ : Fits t₄.mem inp (64 * 8) := fits_of_live?_eq (he₄.live inp.id).symm hin₃

  -- `%60`/`%61`: `in + 40`
  peel_gep 40 with inp, hin₄, t₄ as in40
  refine fd_ulong_load_8_conforms_cont in40 t₄ hwf₄ (Fits.mono hin40 (by bv_omega)) fun t₅ hcall₅ he₅ => ?_
  peel_call hcall₅
  have hwf₅ : t₅.WF := hwf₄.of_equiv he₅
  have hin₅ : Fits t₅.mem inp (64 * 8) := fits_of_live?_eq (he₅.live inp.id).symm hin₄

  -- `%62`/`%63`: `in + 48`
  peel_gep 48 with inp, hin₅, t₅ as in48
  refine fd_ulong_load_8_conforms_cont in48 t₅ hwf₅ (Fits.mono hin48 (by bv_omega)) fun t₆ hcall₆ he₆ => ?_
  peel_call hcall₆
  have hwf₆ : t₆.WF := hwf₅.of_equiv he₆
  have hin₆ : Fits t₆.mem inp (64 * 8) := fits_of_live?_eq (he₆.live inp.id).symm hin₅

  -- `%64`/`%65`: `in + 56`
  peel_gep 56 with inp, hin₆, t₆ as in56
  refine fd_ulong_load_8_conforms_cont in56 t₆ hwf₆ (Fits.mono hin56 (by bv_omega)) fun t₇ hcall₇ he₇ => ?_
  peel_call hcall₇
  have hwf₇ : t₇.WF := hwf₆.of_equiv he₇

  -- the eight loads are done and no store has run, so the state is still `s`
  have heq : s ≈ t₇ :=
    he₀.trans (he₁.trans (he₂.trans (he₃.trans (he₄.trans (he₅.trans (he₆.trans he₇))))))

  -- `%66`-`%459`: the unpacking, the reduction and the carry chains. Pure, and
  -- stepped without reduction -- what the arithmetic computes is irrelevant to
  -- the footprint, and not reducing is what keeps 394 instructions cheap.
  denote_step_all v 459

  -- `out` is still a 32-byte buffer at every state the loads left
  have hout₇ : Fits t₇.mem out (32 * 8) := fits_of_live?_eq (heq.live out.id).symm hout.left

  -- the first store, `out + 0`. Poison here is UB, and UB is the whole run.
  refine poison_cases (v := v459) (fun hb0 => ?_) (fun b0 hb0 => ?_)
  · store_poison hb0
  refine name_of ({ t₇ with mem := t₇.mem.splice out b0 } : GlobalState) fun u₀ hu₀ => ?_
  rw [hb0]
  peel_store b0, out, hout₇, t₇ as u₀ := hu₀
  have hout₀ : Fits u₀.mem out (32 * 8) := by rw [hu₀]; exact fits_splice hout₇

  -- `%460`-`%469`, then `%470 = out + 8` and the second store
  denote_step_all v 469
  peel_gep 8 with out, hout₀, u₀ as out8
  -- `peel_store`'s own `omega` needs a literal width, and `peel_gep` leaves
  -- `256 - BitVec.toNat 8 * 8`; normalise it once.
  have hout8N : Fits u₀.mem out8 64 := Fits.mono hout8 (by bv_omega)
  refine poison_cases (v := v469) (fun hb1 => ?_) (fun b1 hb1 => ?_)
  · store_poison hb1
  refine name_of ({ u₀ with mem := u₀.mem.splice out8 b1 } : GlobalState) fun u₁ hu₁ => ?_
  rw [hb1]
  peel_store b1, out8, hout8N, u₀ as u₁ := hu₁
  have hout₁ : Fits u₁.mem out (32 * 8) := by rw [hu₁]; exact fits_splice hout₀

  -- `%471`-`%480`, then `%481 = out + 16` and the third store
  denote_step_all v 480
  peel_gep 16 with out, hout₁, u₁ as out16
  -- `peel_store`'s own `omega` needs a literal width, and `peel_gep` leaves
  -- `256 - BitVec.toNat 16 * 8`; normalise it once.
  have hout16N : Fits u₁.mem out16 64 := Fits.mono hout16 (by bv_omega)
  refine poison_cases (v := v480) (fun hb2 => ?_) (fun b2 hb2 => ?_)
  · store_poison hb2
  refine name_of ({ u₁ with mem := u₁.mem.splice out16 b2 } : GlobalState) fun u₂ hu₂ => ?_
  rw [hb2]
  peel_store b2, out16, hout16N, u₁ as u₂ := hu₂
  have hout₂ : Fits u₂.mem out (32 * 8) := by rw [hu₂]; exact fits_splice hout₁

  -- `%482`-`%488`, then `%489 = out + 24` and the fourth store
  denote_step_all v 488
  peel_gep 24 with out, hout₂, u₂ as out24
  -- `peel_store`'s own `omega` needs a literal width, and `peel_gep` leaves
  -- `256 - BitVec.toNat 24 * 8`; normalise it once.
  have hout24N : Fits u₂.mem out24 64 := Fits.mono hout24 (by bv_omega)
  refine poison_cases (v := v488) (fun hb3 => ?_) (fun b3 hb3 => ?_)
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

end Firedancer.Common
