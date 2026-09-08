/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_repsqr_mul2
import SSA.Projects.Firedancer.Avx512.Proof.Fold
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.MLIR.DenoteStep

/-!
# `fd_r43x6_repsqr_mul2` conforms to its spec

The region is three blocks: `^bb0` computes `n == 0` and jumps into the loop
(or straight past it), `^bb1` is the loop -- `n` squarings of both chains,
each a `fd_r43x6_sqr_fast` call followed by the `FD_R43X6_FOLD_UNSIGNED`
and/lshr/shuffle/`vpmadd52lo` sequence -- and `^bb2` is the two multiplies
and the two stores.

The three blocks are one lemma each -- `bb0_run`, `bb1_run`, `bb2_run` -- and
`fd_r43x6_repsqr_mul2_conforms` is their composition, splitting on `n = 0` the
way `^bb0` does. `bb1_run` is `Blocks.run_loop_args` (the data-carrying-header
form of `Blocks.run_loop`, since the φs here hold the chains rather than a
counter alone) over `bb1_step`, one iteration.

The two calls each block makes are `Proof/Step/`'s `sqr_step`/`mul_step`, and
the four fold instructions that follow each are `Proof/Fold.lean`'s
`denote_foldVec`; `sqr_inl`/`mul_inl` are what the whole macro leaves.

`Chain` is the invariant one chain carries: the `u44` limbs the fold leaves,
the two ignored lanes zero -- `fd_r43x6_sqr_fast`'s contract on its input --
and the value reached. The state is carried only up to `≈`: the calls
allocate nothing, but `runFunction` still pops a frame, so what comes back is
`s.popFrame s.mem` rather than `s`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/- Scaffolding for the `fd_r43x6_repsqr_mul2` derivation. Only
`fd_r43x6_repsqr_mul2_conforms`, below, escapes. -/
namespace RepsqrMul2

/-- The region's vector type, `vector<8xi64>`. -/
private abbrev V8 : SLLVM.Ty := SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))

/-! ### The two tail blocks as branch targets

`^bb1` is block 0 and `^bb2` block 1. The `^bb1` φs are `(%7, %8, %9)`: the
`a` chain, the `b` chain, the counter. The `^bb2` φs are `(%22, %23)`, and
both edges into it pass the `b` chain first. -/

/-- The loop header `^bb1` with the chains at `a`/`b` and the counter at `m`. -/
private abbrev hdr1 (a b : Vector (BitVec 64) 8) (m : BitVec 64) :
    SuccArgs fd_r43x6_repsqr_mul2.sigs :=
  ⟨0, by rfl, ([a.map PoisonOr.value, b.map PoisonOr.value, PoisonOr.value m]ₕ :
    HVector TyDenote.toType [V8, V8, SLLVM.Ty.bitvec 64])⟩

/-- The loop's exit block `^bb2`, `b` chain first. -/
private abbrev hdr2 (b a : Vector (BitVec 64) 8) :
    SuccArgs fd_r43x6_repsqr_mul2.sigs :=
  ⟨1, by rfl, ([b.map PoisonOr.value, a.map PoisonOr.value]ₕ :
    HVector TyDenote.toType [V8, V8])⟩

/-- The ambient environment the tail blocks read: the entry block's six
constants and the four region arguments `^bb2` uses. The `Γout` indices are
spelled here once, so no later segment has to reduce the `Cfg` to look a
value up.

`%3`, the `llvm.poison` the shuffles take as their dead second operand, is
listed too. No lane of it is ever read -- every mask index is below 8 -- but
pinning it keeps an opaque `V ⟨3, _⟩` out of the shuffle's denotation, where
it would otherwise block a syntactic match. -/
structure EntryEnv (V : fd_r43x6_repsqr_mul2.Γout.Valuation)
    (za zb : Pointer) (ya yb : Vector (BitVec 64) 8) : Prop where
  /-- `%5 = -1`, the loop's decrement -/
  cm1 : V (⟨1, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 18446744073709551615#64
  /-- `%4 = [19, 1, 1, 1, 1, 1, 0, 0]`, the fold's multipliers -/
  cfold : V (⟨2, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var V8)
    = toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0]
  /-- `%3`, the `llvm.poison` the shuffles take as their dead second operand -/
  cpoison : V (⟨3, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var V8)
    = Vector.replicate 8 PoisonOr.poison
  /-- `%2 = [43, 43, 43, 43, 43, 40, 0, 0]`, the fold's shifts -/
  cshift : V (⟨4, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var V8)
    = toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0]
  /-- `%1 = [2^43-1, …, 2^40-1, 0, 0]`, the fold's masks -/
  cmask : V (⟨5, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var V8)
    = toBitVecValue 64
      #v[8796093022207, 8796093022207, 8796093022207, 8796093022207, 8796093022207,
         1099511627775, 0, 0]
  /-- `%0 = 0`, the counter's sentinel -/
  c0 : V (⟨6, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 0#64
  /-- `%arg5`, the `b` chain's multiplier -/
  vyb : V (⟨8, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var V8) = yb.map PoisonOr.value
  /-- `%arg3`, the `b` chain's out-parameter -/
  vzb : V (⟨10, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var SLLVM.Ty.ptr) = .value zb
  /-- `%arg2`, the `a` chain's multiplier -/
  vya : V (⟨11, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var V8) = ya.map PoisonOr.value
  /-- `%arg0`, the `a` chain's out-parameter -/
  vza : V (⟨13, by rfl⟩ : fd_r43x6_repsqr_mul2.Γout.Var SLLVM.Ty.ptr) = .value za

/-- What one squaring chain carries between iterations: the input contract of
`fd_r43x6_sqr_fast` (`u47` limbs, the two ignored lanes zero) and the value
reached, `x` squared `k` times. `u44` is the tighter bound the fold leaves,
so it holds only once an iteration has run -- and it is what `^bb2` hands to
`fd_r43x6_mul_fast`. -/
private structure Chain (x : Vector (BitVec 64) 8) (k : Nat)
    (v : Vector (BitVec 64) 8) : Prop where
  /-- `fd_r43x6_sqr_fast`'s input bound. -/
  u47 : R43x6.U47 (v.take R43x6.limbCount)
  /-- After a fold, `u44` -- the `FD_R43X6_MUL2_INL` contract at `^bb2`. -/
  u44 : 0 < k → R43x6.U44 (v.take R43x6.limbCount)
  /-- Lane 6 of an `fd_r43x6_t` is zero. -/
  z6 : v[6] = 0
  /-- Lane 7 of an `fd_r43x6_t` is zero: `fd_r43x6_sqr_fast`'s `h7`. -/
  z7 : v[7] = 0
  /-- `k` squarings of `x`. -/
  value : vecValue v = vecValue x ^ 2 ^ k

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **One iteration of `^bb1`**: `fd_r43x6_sqr_fast` and the fold on each
chain, the counter decremented by `%5 = -1`, and the branch taken -- out to
`^bb2` when the decremented counter reaches `%0 = 0`, back to `^bb1`
otherwise.

`m.toNat < 2 ^ 63` is what keeps the `nsw` decrement from poisoning: it is
the whole descent `n, n-1, …, 1` that must avoid `-2 ^ 63`, and only a
counter at exactly `2 ^ 63` does not.

The two calls allocate nothing and write nothing, so the state comes back
equivalent to the one they ran in -- equivalent, not equal: `runFunction`
pops a frame either way. -/
private lemma bb1_step {za zb : Pointer} {ya yb : Vector (BitVec 64) 8}
    {V : fd_r43x6_repsqr_mul2.Γout.Valuation} (env : EntryEnv V za zb ya yb)
    {xa xb a b : Vector (BitVec 64) 8} {k : Nat} {m : BitVec 64}
    (ha : Chain xa k a) (hb : Chain xb k b)
    (_hm : m ≠ 0) (hm63 : m.toNat < 2 ^ 63)
    {s : GlobalState} (hs : s.WF) :
    ∃ (a' b' : Vector (BitVec 64) 8), ∃ Vout, ∃ s' : GlobalState,
      StateT.run ((fd_r43x6_repsqr_mul2.blocks.get 0 (by rfl)).2.denote
          (Ctxt.Valuation.ofHVector (hdr1 a b m).args.reverse ++ V)) s
        = .value ((Vout, .inr (if m = 1 then hdr2 b' a' else hdr1 a' b' (m - 1))), s')
      ∧ Chain xa (k + 1) a' ∧ Chain xb (k + 1) b' ∧ s' ≈ s ∧ s'.WF := by

  denote_reduce_get

  -- %10-%14: `FD_R43X6_SQR_INL` on the `a` chain -- `sqr_step_of_take` is the
  -- call, `denote_foldVec` the four fold instructions after it.
  peel_call (sqr_step_of_take ha.u47 ha.z6 ha.z7 s _ rfl) with simp_spine
  -- `only`: a full `simp` here normalises the lanes out of the shape
  -- `denote_foldVec` is stated in, and the `exact` below then grinds
  denote_step_reduce v 7 only [simp_spine, env.cmask, env.cshift, env.cfold, env.cpoison] fold
  replace hv7 : v7 = (foldVec (sqrVec a)).map PoisonOr.value := by
    rw [hv7]; exact denote_foldVec (sqrVec a) (limbNat_sqr_lt ha.u47) _
  -- %15-%19: the same on the `b` chain, one frame pop further on
  denote_clear v 4 6
  set s' := (s.popFrame s.mem) with hs'
  peel_call (sqr_step_of_take hb.u47 hb.z6 hb.z7 s' _ rfl) with simp_spine
  denote_step_reduce v 12 only [simp_spine, env.cmask, env.cshift, env.cfold, env.cpoison] fold
  replace hv12 : v12 = (foldVec (sqrVec b)).map PoisonOr.value := by
    rw [hv12]; exact denote_foldVec (sqrVec b) (limbNat_sqr_lt hb.u47) _
  denote_clear v 8 11

  denote_step_reduce v 14 only [simp_spine, env.cmask, env.cshift, env.cfold, env.cpoison,
    LLVM.add, LLVM.add?, LLVM.icmp, LLVM.icmp?, LLVM.icmp'] fold
  -- `%20 = add %9, -1 nsw`: the counter descends `n, n-1, …, 1`, so it never
  -- reaches `-2 ^ 63` and the `nsw` never poisons
  have hmi : m.toInt = (m.toNat : ℤ) := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hno : ¬ (m.saddOverflow 18446744073709551615#64) := by
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or, not_le,
      not_lt, hmi, show (18446744073709551615#64 : BitVec 64).toInt = -1 from by decide]
    omega
  simp [env.cm1, env.c0, hno] at hv14
  simp [env.cm1, hno] at hv13

  simp only [hv14, BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  -- Both branches leave the same four facts: the two chains, and the state
  -- after two frame pops. `sqr_inl` is `FD_R43X6_SQR_INL`'s whole contract.
  have e1 : s.popFrame s.mem ≈ s := hs.popFrame_equiv.symm
  have w1 : (s.popFrame s.mem).WF := hs.of_equiv hs.popFrame_equiv
  have e2 : (s.popFrame s.mem).popFrame (s.popFrame s.mem).mem ≈ s.popFrame s.mem :=
    w1.popFrame_equiv.symm
  have hend : Chain xa (k + 1) (foldVec (sqrVec a)) ∧ Chain xb (k + 1) (foldVec (sqrVec b))
      ∧ s'.popFrame s'.mem ≈ s ∧ (s'.popFrame s'.mem).WF :=
    ⟨⟨(sqr_inl ha.u47).u47, fun _ => (sqr_inl ha.u47).u44,
        (sqr_inl ha.u47).z6, (sqr_inl ha.u47).z7,
        by rw [(sqr_inl ha.u47).value, ha.value, ← pow_mul, ← pow_succ]⟩,
      ⟨(sqr_inl hb.u47).u47, fun _ => (sqr_inl hb.u47).u44,
        (sqr_inl hb.u47).z6, (sqr_inl hb.u47).z7,
        by rw [(sqr_inl hb.u47).value, hb.value, ← pow_mul, ← pow_succ]⟩,
      e2.trans e1, w1.of_equiv w1.popFrame_equiv⟩
  by_cases h : m = 1
  case pos =>
    simp only [h]
    simp
    simp only [Ctxt.Var.last, Ctxt.Valuation.cons_zero, hv7, hv12]
    refine ⟨foldVec (sqrVec a), foldVec (sqrVec b), ?_⟩
    simp

    exact hend

  have : (m + 18446744073709551615#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro hc
    exact h (by bv_omega)
  simp [this]
  simp only [Ctxt.Var.last, Ctxt.Valuation.cons_zero, hv7, hv12, hv13]
  refine ⟨foldVec (sqrVec a), foldVec (sqrVec b), ?_, hend⟩
  rw [if_neg (show ¬ (m = 1#64) from fun hc => h (by bv_omega)),
    show m + 18446744073709551615#64 = m - 1#64 from by bv_omega]

/-- **The loop.** From the `^bb1` header with the chains at `xa`/`xb` and the
counter at `n ≠ 0`, control reaches `^bb2` with each chain squared `n.toNat`
times, in a state equivalent to the one it started in.

`n ≠ 0` is not a restriction: `^bb0` branches straight to `^bb2` when the
counter is zero, so the loop is entered only with a nonzero one. -/
theorem bb1_run {za zb : Pointer} {ya yb : Vector (BitVec 64) 8}
    {V : fd_r43x6_repsqr_mul2.Γout.Valuation} (env : EntryEnv V za zb ya yb)
    {xa xb : Vector (BitVec 64) 8} {n : BitVec 64}
    (hn : n ≠ 0) (hn63 : n.toNat < 2 ^ 63)
    (hxa : R43x6.U47 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hxb : R43x6.U47 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0)
    {s : GlobalState} (hs : s.WF) :
    ∃ (a b : Vector (BitVec 64) 8) (s' : GlobalState),
      StateT.run (fd_r43x6_repsqr_mul2.blocks.run V (hdr1 xa xb n)) s
        = StateT.run (fd_r43x6_repsqr_mul2.blocks.run V (hdr2 b a)) s'
      ∧ s' ≈ s ∧ s'.WF
      ∧ R43x6.U44 (a.take R43x6.limbCount) ∧ R43x6.U44 (b.take R43x6.limbCount)
      ∧ a[6] = 0 ∧ a[7] = 0 ∧ b[6] = 0 ∧ b[7] = 0
      ∧ vecValue a = vecValue xa ^ 2 ^ n.toNat
      ∧ vecValue b = vecValue xb ^ 2 ^ n.toNat := by
  have hN : 0 < n.toNat := by bv_omega
  -- The invariant: `k` squarings done on each chain, the state still `≈ s`,
  -- and the walk standing at the header with a counter of `n - k` -- or, once
  -- `k` reaches `n`, at `^bb2`.
  obtain ⟨t, u, hrun, hInv⟩ :=
    Blocks.run_loop_args (bs := fd_r43x6_repsqr_mul2.blocks) (Vamb := V)
      (Inv := fun k t u =>
        ∃ a b : Vector (BitVec 64) 8, Chain xa k a ∧ Chain xb k b ∧ u ≈ s ∧ u.WF
          ∧ (if k = n.toNat then t = hdr2 b a
             else ∃ m : BitVec 64, m.toNat = n.toNat - k ∧ t = hdr1 a b m))
      (n := n.toNat) (t₀ := hdr1 xa xb n) (s₀ := s)
      -- one iteration
      (by
        rintro k t u hk ⟨a, b, ha, hb, hu, huwf, ht⟩
        rw [if_neg (by omega)] at ht
        obtain ⟨m, hm, rfl⟩ := ht
        have hm0 : m ≠ 0 := by rintro rfl; simp at hm; omega
        have hm63 : m.toNat < 2 ^ 63 := by omega
        obtain ⟨a', b', Vout, u', hstep, ha', hb', hu', hu'wf⟩ :=
          bb1_step env ha hb hm0 hm63 huwf
        refine ⟨Vout, _, u', hstep, a', b', ha', hb', hu'.trans hu, hu'wf, ?_⟩
        by_cases h1 : m = 1
        · subst h1
          rw [if_pos (by simp at hm; omega), if_pos rfl]
        · have hm1 : 1 < m.toNat := by
            have : m.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq (by simp [h]))
            omega
          rw [if_neg (by omega), if_neg h1]
          exact ⟨m - 1, by bv_omega, rfl⟩)
      -- entering the loop: nothing squared yet, the counter still `n`
      (by
        refine ⟨xa, xb, ⟨hxa, fun h => absurd h (by omega), hxa6, hxa7, by simp⟩,
          ⟨hxb, fun h => absurd h (by omega), hxb6, hxb7, by simp⟩, .refl _, hs, ?_⟩
        rw [if_neg (by omega)]
        exact ⟨n, by omega, rfl⟩)
  obtain ⟨a, b, ha, hb, hu, huwf, ht⟩ := hInv
  rw [if_pos rfl] at ht
  subst ht
  exact ⟨a, b, u, hrun, hu, huwf, ha.u44 hN, hb.u44 hN,
    ha.z6, ha.z7, hb.z6, hb.z7, ha.value, hb.value⟩

/-! ### The entry and exit blocks -/

private lemma bb0_run (za zb : Pointer) (xa ya xb yb : Vector (BitVec 64) 8)
    (n : BitVec 64) (s : GlobalState) :
    ∃ V : fd_r43x6_repsqr_mul2.Γout.Valuation,
      EntryEnv V za zb ya yb
      ∧ StateT.run (fd_r43x6_repsqr_mul2.denote (Ctxt.Valuation.ofHVector
          [.value n, yb.map PoisonOr.value, xb.map PoisonOr.value, .value zb,
            ya.map PoisonOr.value, xa.map PoisonOr.value, .value za]ₕ)) s
        = StateT.run (fd_r43x6_repsqr_mul2.blocks.run V
            (if n = 0 then hdr2 xb xa else hdr1 xa xb n)) s := by
  refine ⟨PoisonOr.value (BitVec.ofBool (n == 0#64)) ::ᵥ
    PoisonOr.value 18446744073709551615#64 ::ᵥ
    toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0] ::ᵥ
    Vector.replicate 8 PoisonOr.poison ::ᵥ
    toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0] ::ᵥ
    toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
      8796093022207, 1099511627775, 0, 0] ::ᵥ
    PoisonOr.value 0#64 ::ᵥ
    Ctxt.Valuation.ofHVector
      [.value n, yb.map PoisonOr.value, xb.map PoisonOr.value, .value zb,
        ya.map PoisonOr.value, xa.map PoisonOr.value, .value za]ₕ,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  simp only [Cfg.denote]
  denote_step_reduce v 6 [LLVM.const?, LLVM.Ty.poison]
  replace hv1 : v1 = toBitVecValue 64 #v[8796093022207, 8796093022207, 8796093022207,
      8796093022207, 8796093022207, 1099511627775, 0, 0] := by denote_dense hv1
  replace hv2 : v2 = toBitVecValue 64 #v[43, 43, 43, 43, 43, 40, 0, 0] := by
    denote_dense hv2
  replace hv4 : v4 = toBitVecValue 64 #v[19, 1, 1, 1, 1, 1, 0, 0] := by
    denote_dense hv4
  rw [hv0] at hv6
  simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp'] at hv6
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, if_pos (by decide)]
    rfl
  · have hb : (n == 0#64) = false := by simpa using hn
    rw [if_neg hn, hb, if_neg (by decide)]
    rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- **`^bb2`**: one `fd_r43x6_mul_fast` and fold per chain -- the `a` chain by
`%arg2`, the `b` chain by `%arg5` -- then the two whole-vector stores and the
`llvm.return`.

The `popFrame` is taken over `s₀`, the state the *region* was entered in,
which is where the spec's memory claim lives; `s` is where `^bb2` starts, and
`≈` is all the loop leaves of the connection between them. -/
private lemma bb2_run {za zb : Pointer} {ya yb : Vector (BitVec 64) 8}
    {V : fd_r43x6_repsqr_mul2.Γout.Valuation} (env : EntryEnv V za zb ya yb)
    {a b : Vector (BitVec 64) 8}
    (ha : R43x6.U47 (a.take R43x6.limbCount)) (ha6 : a[6] = 0) (ha7 : a[7] = 0)
    (hb : R43x6.U47 (b.take R43x6.limbCount)) (hb6 : b[6] = 0) (hb7 : b[7] = 0)
    (hya : R43x6.U47 (ya.take R43x6.limbCount)) (hya6 : ya[6] = 0) (hya7 : ya[7] = 0)
    (hyb : R43x6.U47 (yb.take R43x6.limbCount)) (hyb6 : yb[6] = 0) (hyb7 : yb[7] = 0)
    {s₀ s : GlobalState} (hs : s.WF) (hss₀ : s ≈ s₀)
    (hza : IsVecPtr s₀.mem za) (hzb : IsVecPtr s₀.mem zb) (hne : za.id ≠ zb.id) :
    ∃ s' : GlobalState,
      StateT.run (fd_r43x6_repsqr_mul2.blocks.run V (hdr2 b a)) s
        = .value (HVector.nil, s')
      ∧ ∃ oa ob : Vector (BitVec 64) 8,
        s₀.popFrame s'.mem
          ≈ ({ s₀ with mem := (s₀.mem.splice za (vecBV oa)).splice zb (vecBV ob) }
              : GlobalState)
        ∧ vecValue oa = vecValue a * vecValue ya
        ∧ vecValue ob = vecValue b * vecValue yb
        ∧ R43x6.U44 (oa.take R43x6.limbCount)
        ∧ R43x6.U44 (ob.take R43x6.limbCount) := by
  denote_enter_block
  -- `%24 = call @fd_r43x6_mul_fast(%23, %arg2)`: the `a` chain by `ya`
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8, V8])
    (by simp only [simp_spine, env.vya])
    (mul_step_of_take ha ha6 ha7 hya hya6 hya7 s)]
  denote_step_reduce v 6 only [simp_spine, env.cmask, env.cshift, env.cfold, env.cpoison] fold
  replace hv6 : v6 = (foldVec (mulVec a ya)).map PoisonOr.value := by
    rw [hv6]; exact denote_foldVec (mulVec a ya) (limbNat_mul_lt ha hya) _
  denote_clear v 3 5
  -- `%29 = call @fd_r43x6_mul_fast(%22, %arg5)`, then `%30`-`%33`: the fold
  rw [BlockCom.run_bind_denote_call_cfg_of_value (argTys := [V8, V8])
    (by simp only [simp_spine, env.vyb])
    (mul_step_of_take hb hb6 hb7 hyb hyb6 hyb7 _)]
  denote_step_reduce v 11 only [simp_spine, env.cmask, env.cshift, env.cfold, env.cpoison] fold
  replace hv11 : v11 = (foldVec (mulVec b yb)).map PoisonOr.value := by
    rw [hv11]; exact denote_foldVec (mulVec b yb) (limbNat_mul_lt hb hyb) _
  denote_clear v 8 10
  -- The two frame pops the calls made. Neither can touch `za`/`zb`: they are
  -- the caller's blocks, so they sit below the counter both pops kill from.
  have e1 : s ≈ s.popFrame s.mem := hs.popFrame_equiv
  have w1 : (s.popFrame s.mem).WF := hs.of_equiv e1
  have e2 : (s.popFrame s.mem)
      ≈ (s.popFrame s.mem).popFrame (s.popFrame s.mem).mem := w1.popFrame_equiv
  obtain ⟨u, hu⟩ :=
    GlobalState.exists_popFrame (s.popFrame s.mem) (s.popFrame s.mem).mem
  have eu : s ≈ u := hu ▸ e1.trans e2
  have hs₀ : s₀.WF := hs.of_equiv hss₀
  have hzau : Fits u.mem za (8 * 64) :=
    fits_of_live?_eq (eu.live za.id).symm (fits_of_live?_eq (hss₀.live za.id) hza.1)
  have hzbu : Fits u.mem zb (8 * 64) :=
    fits_of_live?_eq (eu.live zb.id).symm (fits_of_live?_eq (hss₀.live zb.id) hzb.1)
  rw [← hu]
  -- `llvm.store %28, %arg0` and `llvm.store %33, %arg3`, then `llvm.return`.
  -- The block's own spine has to come apart before the stores are reachable.
  simp only [simp_spine]
  rw [BlockCom.run_bind_denote_var_of_nil
    (s' := { u with mem := u.mem.splice za (vecBV (foldVec (mulVec a ya))) })
    (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm,
        env.vza, hv6]
      rw [run_liftM (run_store (t := .vector 8 (.bitvec (.concrete 64)))
        (x := (foldVec (mulVec a ya)).map PoisonOr.value)
        (flatten_vecBV (foldVec (mulVec a ya)))
        (show Fits u.mem za 512 from Fits.mono hzau (by omega)))]
      rfl)]
  rw [BlockCom.run_bind_denote_var_of_nil
    (s' := { u with
      mem := (u.mem.splice za (vecBV (foldVec (mulVec a ya)))).splice zb (vecBV (foldVec (mulVec b yb))) })
    (by
      simp only [Expr.denoteOp, simp_denote, simp_sllvm,
        env.vzb, hv11]
      rw [run_liftM (run_store (t := .vector 8 (.bitvec (.concrete 64)))
        (x := (foldVec (mulVec b yb)).map PoisonOr.value)
        (flatten_vecBV (foldVec (mulVec b yb)))
        (show Fits (u.mem.splice za (vecBV (foldVec (mulVec a ya)))) zb 512 from
          Fits.mono (fits_splice hzbu) (by omega)))]
      rfl)]
  simp_return
  refine ⟨foldVec (mulVec a ya), foldVec (mulVec b yb), ?_,
    (mul_inl ha hya).value, (mul_inl hb hyb).value,
    (mul_inl ha hya).u44, (mul_inl hb hyb).u44⟩
  -- The memory the region leaves is the caller's, with `za` and `zb` written.
  refine popFrame_equiv_written (fun q => q = za.id ∨ q = zb.id) hs₀ ?_ ?_ ?_ ?_
  · rintro b (rfl | rfl)
    · exact lt_nextFreeBlock_of_fits hs₀ hza.1
    · exact lt_nextFreeBlock_of_fits hs₀ hzb.1
  · intro b _ hw
    rw [live?_splice_ne (fun h => hw (Or.inr h.symm)),
      live?_splice_ne (fun h => hw (Or.inl h.symm)), ← eu.live b, hss₀.live b]
  · intro b hw
    rw [live?_splice_ne (fun h => hw (Or.inr h.symm)),
      live?_splice_ne (fun h => hw (Or.inl h.symm))]
  · rintro b (rfl | rfl)
    · rw [live?_splice_ne (fun h => hne h.symm), live?_splice_ne (fun h => hne h.symm)]
      exact live?_splice_congr ((eu.live za.id).symm.trans (hss₀.live za.id))
    · exact live?_splice_congr (by
        rw [live?_splice_ne (fun h => hne h), live?_splice_ne (fun h => hne h)]
        exact (eu.live zb.id).symm.trans (hss₀.live zb.id))


end RepsqrMul2

/-- **`fd_r43x6_repsqr_mul2` conforms to its spec.** `^bb0` picks the branch,
`bb1_run` runs the `n` squarings of both chains, and `bb2_run` multiplies and
stores.

Three hypotheses beyond the `u47` contract, all of them the region's:

* `hn63`: the `nsw` decrement of the counter poisons at `-2 ^ 63`, which the
  descent `n, n-1, …, 1` reaches exactly when `2 ^ 63 ≤ n`;
* the `[6]`/`[7]` zeros, `fd_r43x6_sqr_fast`'s and `fd_r43x6_mul_fast`'s
  contract on their inputs, which `u47` does not give.

Every caller has a literal `n` (`fd_r43x6_pow22523_2` uses 5, 10, 20, 50, 100
and 250), so `hn63` is a `decide` there. -/
theorem fd_r43x6_repsqr_mul2_conforms (za zb : Pointer)
    (xa ya xb yb : Vector (BitVec 64) 8) (n : BitVec 64) (s : GlobalState)
    (hs : s.WF) (hza : IsVecPtr s.mem za) (hzb : IsVecPtr s.mem zb)
    (hne : za.id ≠ zb.id) (hn63 : n.toNat < 2 ^ 63)
    (hxa : R43x6.U47 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hya : R43x6.U47 (ya.take R43x6.limbCount)) (hya6 : ya[6] = 0) (hya7 : ya[7] = 0)
    (hxb : R43x6.U47 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0)
    (hyb : R43x6.U47 (yb.take R43x6.limbCount)) (hyb6 : yb[6] = 0) (hyb7 : yb[7] = 0) :
    fd_r43x6_repsqr_mul2_spec za zb xa ya xb yb n s hza hzb := by
  simp only [fd_r43x6_repsqr_mul2_spec]
  refine Firedancer.run_runFunction' _ ?_
  obtain ⟨V, env, hentry⟩ := RepsqrMul2.bb0_run za zb xa ya xb yb n s
  rw [hentry]
  by_cases hn : n = 0
  · -- no squarings: `^bb0` branches straight past the loop, `xa ^ 2 ^ 0 = xa`
    subst hn
    rw [if_pos rfl]
    obtain ⟨s', hrun, oa, ob, hmem, hoa, hob, hoa44, hob44⟩ :=
      RepsqrMul2.bb2_run env hxa hxa6 hxa7 hxb hxb6 hxb7 hya hya6 hya7 hyb hyb6 hyb7
        hs (.refl _) hza hzb hne
    exact ⟨s', hrun, oa, ob, hmem, by simpa using hoa, by simpa using hob, hoa44, hob44⟩
  · rw [if_neg hn]
    obtain ⟨a, b, s₁, hloop, hs₁, hs₁wf, ha44, hb44, ha6, ha7, hb6, hb7, hva, hvb⟩ :=
      RepsqrMul2.bb1_run env hn hn63 hxa hxa6 hxa7 hxb hxb6 hxb7 hs
    rw [hloop]
    obtain ⟨s', hrun, oa, ob, hmem, hoa, hob, hoa44, hob44⟩ :=
      RepsqrMul2.bb2_run env (u47_of_u44 ha44) ha6 ha7
        (u47_of_u44 hb44) hb6 hb7 hya hya6 hya7 hyb hyb6 hyb7
        hs₁wf hs₁ hza hzb hne
    exact ⟨s', hrun, oa, ob, hmem, by rw [hoa, hva], by rw [hob, hvb], hoa44, hob44⟩

end Firedancer.Avx512
