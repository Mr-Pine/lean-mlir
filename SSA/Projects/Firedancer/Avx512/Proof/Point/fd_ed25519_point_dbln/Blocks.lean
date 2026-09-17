/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Lanes
public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_dbln
public import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Frame
public import SSA.Projects.Firedancer.MLIR.DenoteStep
public import SSA.Projects.Firedancer.Proof.Tactics

/-!
# `fd_ed25519_point_dbln`'s tail blocks

`^bb1` (block 0) stores the last doubling into `r`, `^bb2` (block 1) returns
`r`, `^bb3` (block 2) is the loop: one `FD_R43X6_GE_DBL` on the carried vectors
and the `i8` counter. Each reads `^bb0`'s definitions through `EntryEnv`;
`%k` is `Γout` variable `194 - k`, `%argN` is `197 - N`.
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointDbln
open Ge

/-! ### Branch targets -/

/-- `^bb1(%282, %284, %286)`, threaded by the lifter: the last doubling. -/
abbrev hdr1 (q : Quad) : SuccArgs fd_ed25519_point_dbln.sigs :=
  ⟨0, rfl, ([q.v03.map PoisonOr.value, q.v14.map PoisonOr.value, q.v25.map PoisonOr.value]ₕ :
    HVector TyDenote.toType [V8, V8, V8])⟩

/-- `^bb2`, the return. -/
abbrev hdr2 : SuccArgs fd_ed25519_point_dbln.sigs :=
  ⟨1, rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb3(%195, %196, %197, %198)`: the loop header, `25` vector first, and the counter. -/
abbrev hdr3 (q : Quad) (c : BitVec 8) : SuccArgs fd_ed25519_point_dbln.sigs :=
  ⟨2, rfl, ([q.v25.map PoisonOr.value, q.v14.map PoisonOr.value, q.v03.map PoisonOr.value,
    PoisonOr.value c]ₕ : HVector TyDenote.toType [V8, V8, V8, SLLVM.Ty.bitvec 8])⟩

/-! ### The ambient environment -/

/-- What the tail blocks read out of `^bb0`: `GE_DBL`'s constants, the loop's six
slots, `r`'s two field pointers, `r` and `n`. -/
structure EntryEnv (V : fd_ed25519_point_dbln.Γout.Valuation) (s : GlobalState) (r : Pointer)
    (n : BitVec 32) : Prop where
  c19 : V (⟨175, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 dblShift
  c32 : V (⟨162, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskG 8796093022189#64 8796093022207#64
  c41 : V (⟨153, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskG 8796093022207#64 8796093022207#64
  c50 : V (⟨144, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskG 8796093022207#64 1099511627775#64
  c59 : V (⟨135, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskE 8796093022189#64 8796093022207#64
  c68 : V (⟨126, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskE 8796093022207#64 8796093022207#64
  c77 : V (⟨117, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskE 8796093022207#64 1099511627775#64
  c9 : V (⟨185, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 nbias03
  c8 : V (⟨186, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 nbias
  c7 : V (⟨187, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadShift43
  c6 : V (⟨188, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadShift48
  c86 : V (⟨108, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = quadMul19
  c4 : V (⟨190, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadMask43
  c3 : V (⟨191, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 bias03
  c2 : V (⟨192, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 bias
  c1 : V (⟨193, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadMask48
  c0 : V (⟨194, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var (SLLVM.Ty.bitvec 8)) = .value 1#8
  s6 : V (⟨101, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 6)
  s7 : V (⟨100, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 7)
  s8 : V (⟨99, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 8)
  s9 : V (⟨98, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 9)
  s10 : V (⟨97, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 10)
  s11 : V (⟨96, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 11)
  r64 : V (⟨4, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (r.withOffset 64)
  r128 : V (⟨1, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr)
    = .value (r.withOffset 128)
  vr : V (⟨197, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value r
  vn : V (⟨195, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var (SLLVM.Ty.bitvec 32)) = .value n

/-! ### `^bb2` -/

theorem bb2_run {V : fd_ed25519_point_dbln.Γout.Valuation} {s : GlobalState} {r : Pointer}
    {n : BitVec 32} (env : EntryEnv V s r n) (u : GlobalState) :
    StateT.run (fd_ed25519_point_dbln.blocks.run V hdr2) u = .value ([.value r]ₕ, u) := by
  denote_enter_block
  simp only [BlockCom.denote_term, Terminator.denote_ret, simp_spine]
  rw [env.vr]; rfl

/-! ### `^bb1` -/

set_option maxHeartbeats 1000000 in
/-- **`^bb1`**: the last doubling's three stores into `r`, then `^bb2`. -/
theorem bb1_run {V : fd_ed25519_point_dbln.Γout.Valuation} {s : GlobalState} {r : Pointer}
    {n : BitVec 32} (env : EntryEnv V s r n) (q : Quad) {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame 12 s m₁ u) (hr : IsQuadPtr m₁ r) (hlt : r.id.id < s.alloc.nextFreeBlock) :
    ∃ u', StateT.run (fd_ed25519_point_dbln.blocks.run V (hdr1 q)) u = .value ([.value r]ₕ, u')
      ∧ Frame 12 s (m₁.writeQuad r q) u' := by
  have hlive := hF.below r.id hlt
  obtain ⟨f0, f64, f128⟩ := fits_field hr
  have g0 : Fits u.mem r 512 := fits_of_live?_eq hlive f0
  have g64 : Fits u.mem (r.withOffset 64) 512 := fits_of_live?_eq (p := r.withOffset 64) hlive f64
  have g128 : Fits u.mem (r.withOffset 128) 512 :=
    fits_of_live?_eq (p := r.withOffset 128) hlive f128
  have hF1 := hF.splice r (vecBV q.v03)
  have hF2 := hF1.splice (r.withOffset 64) (vecBV q.v14)
  have hF3 := hF2.splice (r.withOffset 128) (vecBV q.v25)
  denote_enter_block
  refine name_of ({ u with mem := u.mem.splice r (vecBV q.v03) }) fun u1 hu1 => ?_
  ge_store_amb q.v03, r, g0, u as u1 := hu1 with simp_spine, env.vr
  refine name_of ({ u1 with mem := u1.mem.splice (r.withOffset 64) (vecBV q.v14) }) fun u2 hu2 => ?_
  have g64' : Fits u1.mem (r.withOffset 64) 512 := by rw [hu1]; exact fits_splice g64
  ge_store_amb q.v14, (r.withOffset 64), g64', u1 as u2 := hu2
    with simp_spine, env.r64
  refine name_of ({ u2 with mem := u2.mem.splice (r.withOffset 128) (vecBV q.v25) })
    fun u3 hu3 => ?_
  have g128' : Fits u2.mem (r.withOffset 128) 512 := by
    rw [hu2, hu1]; exact fits_splice (fits_splice g128)
  ge_store_amb q.v25, (r.withOffset 128), g128', u2
    as u3 := hu3 with simp_spine, env.r128
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_spine]
  refine ⟨u3, ?_, by rw [hu3, hu2, hu1]; exact hF3⟩
  simp only [Target.denote_mk, HVector.map, pure_bind]
  exact bb2_run env u3

/-! ### `^bb3`, one iteration -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **One iteration of `^bb3`**: `FD_R43X6_GE_DBL` on the carried vectors through
slots 6-11, the counter incremented, and the branch: back to `^bb3` while
`zext(c + 1) <u n`, out to `^bb1` otherwise. -/
theorem bb3_step {V : fd_ed25519_point_dbln.Γout.Valuation} {s : GlobalState} {r : Pointer}
    {n : BitVec 32} (env : EntryEnv V s r n) {x : Quad} (hx : QuadU44 x) (c : BitVec 8)
    {m₁ : MemoryState} {u : GlobalState} (hF : Frame 12 s m₁ u) :
    ∃ Vout u', StateT.run ((fd_ed25519_point_dbln.blocks.get (hdr3 x c).idx (hdr3 x c).hidx).2.denote
        (Ctxt.Valuation.ofHVector (hdr3 x c).args.reverse ++ V) >>= pure) u
      = .value ((Vout, .inr (if BitVec.ult (BitVec.setWidth 32 (c + 1#8)) n
          then hdr3 (geDbl x) (c + 1#8) else hdr1 (geDbl x))), u')
      ∧ Frame 12 s m₁ u' := by
  denote_reduce_get
  denote_number_from 199
  denote_step_reduce v 207 only [simp_spine]
  have e03 := denote_addXY hx.1 hv199 hv202 hv203
  have e14 := denote_addXY hx.2.1 hv200 hv204 hv205
  have e25 := denote_addXY hx.2.2 hv201 hv206 hv207
  denote_clear v 199 207
  subst e03 e14 e25
  iterate 3 peel_lifetime
  refine sqr_step hF (dblTa x) (u47_dblTa hx) (i := 6) (j := 7) (k := 8) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    fun u1 hrun1 hF1 hp6 hp7 hp8 hr6 hr7 hr8 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8])
    (argVals := [(dblTa x).v25.map PoisonOr.value, (dblTa x).v14.map PoisonOr.value,
      (dblTa x).v03.map PoisonOr.value, PoisonOr.value (slot s 8), PoisonOr.value (slot s 7),
      PoisonOr.value (slot s 6)]ₕ)
    (by simp only [simp_spine, env.s6, env.s7, env.s8]; rfl) hrun1]
  ge_load_amb (quadSqrResult (dblTa x)).v03, (slot s 6), hp6, hr6, u1 with simp_spine, env.s6
  ge_load_amb (quadSqrResult (dblTa x)).v14, (slot s 7), hp7, hr7, u1 with simp_spine, env.s7
  ge_load_amb (quadSqrResult (dblTa x)).v25, (slot s 8), hp8, hr8, u1 with simp_spine, env.s8
  iterate 3 peel_lifetime
  denote_step_reduce v 272 only [simp_spine]
  have p03 := denote_egfh env.c19 env.c32 env.c59 hv211 hv214 hv217 hv220 hv221 hv226 hv227 hv228
    hv235 hv236 hv241 hv242 hv243
  have p14 := denote_egfh env.c19 env.c41 env.c68 hv212 hv215 hv218 hv222 hv223 hv229 hv230 hv231
    hv237 hv238 hv244 hv245 hv246
  have p25 := denote_egfh env.c19 env.c50 env.c77 hv213 hv216 hv219 hv224 hv225 hv232 hv233 hv234
    hv239 hv240 hv247 hv248 hv249
  clear hv211 hv212 hv213 hv214 hv215 hv216 hv217 hv218 hv219 hv220 hv221 hv222 hv223 hv224
    hv225 hv226 hv227 hv228 hv229 hv230 hv231 hv232 hv233 hv234 hv235 hv236 hv237 hv238 hv239
    hv240 hv241 hv242 hv243 hv244 hv245 hv246 hv247 hv248 hv249
  subst p03 p14 p25
  have r03 := denote_foldSigned03 (P := egfhQuad (quadSqrResult (dblTa x))) env.c9 env.c8
    env.c6 env.c86 env.c4 env.c3 hv250 hv252 hv255 hv256 hv257 hv258 hv259 hv260
  have r14 := denote_foldSigned14 (P := egfhQuad (quadSqrResult (dblTa x))) env.c9 env.c8
    env.c7 env.c4 env.c2 hv250 hv251 hv253 hv261 hv262 hv263
  have r25 := denote_foldSigned25 (P := egfhQuad (quadSqrResult (dblTa x))) env.c8 env.c7
    env.c2 env.c1 hv251 hv252 hv254 hv264 hv265 hv266
  clear hv250 hv251 hv252 hv253 hv254 hv255 hv256 hv257 hv258 hv259 hv260 hv261 hv262 hv263
    hv264 hv265 hv266
  subst r03 r14 r25
  have g03 := denote_permGE hv267
  have g14 := denote_permGE hv268
  have g25 := denote_permGE hv269
  have f03 := denote_permFH hv270
  have f14 := denote_permFH hv271
  have f25 := denote_permFH hv272
  clear hv267 hv268 hv269 hv270 hv271 hv272
  subst g03 g14 g25 f03 f14 f25
  have hR := u44_dblR hx
  iterate 3 peel_lifetime
  refine mul_step hF1 (geQuad (dblR x)) (fhQuad (dblR x))
    ⟨u47_of_u44 (u44_geQuad hR).1, u47_of_u44 (u44_geQuad hR).2.1, u47_of_u44 (u44_geQuad hR).2.2⟩
    ⟨u47_of_u44 (u44_fhQuad hR).1, u47_of_u44 (u44_fhQuad hR).2.1, u47_of_u44 (u44_fhQuad hR).2.2⟩
    (i := 9) (j := 10) (k := 11) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun u2 hrun2 hF2 hp9 hp10 hp11 hr9 hr10 hr11 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8, V8, V8, V8])
    (argVals := [(fhQuad (dblR x)).v25.map PoisonOr.value, (fhQuad (dblR x)).v14.map PoisonOr.value,
      (fhQuad (dblR x)).v03.map PoisonOr.value, (geQuad (dblR x)).v25.map PoisonOr.value,
      (geQuad (dblR x)).v14.map PoisonOr.value, (geQuad (dblR x)).v03.map PoisonOr.value,
      PoisonOr.value (slot s 11), PoisonOr.value (slot s 10), PoisonOr.value (slot s 9)]ₕ)
    (by simp only [simp_spine, env.s9, env.s10, env.s11]; rfl) hrun2]
  ge_load_amb (quadMulResult (geQuad (dblR x)) (fhQuad (dblR x))).v03, (slot s 9), hp9, hr9, u2
    with simp_spine, env.s9
  ge_load_amb (quadMulResult (geQuad (dblR x)) (fhQuad (dblR x))).v14, (slot s 10), hp10, hr10,
    u2 with simp_spine, env.s10
  ge_load_amb (quadMulResult (geQuad (dblR x)) (fhQuad (dblR x))).v25, (slot s 11), hp11, hr11,
    u2 with simp_spine, env.s11
  iterate 3 peel_lifetime
  denote_step_reduce v 289 only [simp_spine]
  have o03 := denote_foldU03 env.c6 env.c86 env.c4 hv278 hv279 hv280 hv281 hv282
  have o14 := denote_foldU14 env.c7 env.c4 hv276 hv283 hv284
  have o25 := denote_foldU25 env.c7 env.c1 hv277 hv285 hv286
  clear hv276 hv277 hv278 hv279 hv280 hv281 hv282 hv283 hv284 hv285 hv286
  subst o03 o14 o25
  replace hv287 : v287 = .value (c + 1#8) := by rw [hv287, env.c0]; rfl
  subst hv287
  replace hv288 : v288 = .value (BitVec.setWidth 32 (c + 1#8)) := by rw [hv288]; rfl
  subst hv288
  replace hv289 : v289 = .value (BitVec.ofBool (BitVec.ult (BitVec.setWidth 32 (c + 1#8)) n)) := by
    rw [hv289, env.vn]; rfl
  subst hv289
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_spine]
  by_cases hb : (BitVec.setWidth 32 (c + 1#8) <ᵤ n) = true
  · refine ⟨?V1, u2, ?e1, hF2⟩
    case e1 =>
      rw [if_pos hb]
      simp only [hb, BitVec.ofBool_true, ite_true, pure_bind, bind_pure]
      rfl
  · refine ⟨?V2, u2, ?e2, hF2⟩
    case e2 =>
      rw [if_neg hb]
      simp only [hb, BitVec.ofBool_false, pure_bind, bind_pure]
      rfl

/-! ### The loop -/

private theorem cond_iff {n : BitVec 32} {k : ℕ} (hk : k + 2 ≤ n.toNat) (hn : n.toNat < 256) :
    (BitVec.setWidth 32 (BitVec.ofNat 8 (k + 1) + 1#8) <ᵤ n) = decide (k + 1 + 1 < n.toNat) := by
  have e : (BitVec.setWidth 32 (BitVec.ofNat 8 (k + 1) + 1#8)).toNat = k + 2 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [BitVec.ult, e]

/-- **The loop**: from `^bb3` holding the first doubling with the counter at `1`, control
reaches `^bb1` holding `n - 1` more. -/
theorem loop_run {V : fd_ed25519_point_dbln.Γout.Valuation} {s : GlobalState} {r : Pointer}
    {n : BitVec 32} (env : EntryEnv V s r n) (h2 : 2 ≤ n.toNat) (hn : n.toNat < 256)
    {x : Quad} (hx : QuadU44 x) {m₁ : MemoryState} {u : GlobalState} (hF : Frame 12 s m₁ u) :
    ∃ u', StateT.run (fd_ed25519_point_dbln.blocks.run V (hdr3 x 1#8)) u
        = StateT.run (fd_ed25519_point_dbln.blocks.run V (hdr1 (geDbl^[n.toNat - 1] x))) u'
      ∧ Frame 12 s m₁ u' := by
  obtain ⟨t, u', hrun, hInv⟩ :=
    Blocks.run_loop_args (bs := fd_ed25519_point_dbln.blocks) (Vamb := V)
      (Inv := fun k t w => ∃ y, y = geDbl^[k] x ∧ QuadU44 y ∧ Frame 12 s m₁ w ∧
        t = if k + 1 < n.toNat then hdr3 y (BitVec.ofNat 8 (k + 1)) else hdr1 y)
      (n := n.toNat - 1) (t₀ := hdr3 x 1#8) (s₀ := u)
      (by
        rintro k t w hk ⟨y, rfl, hy, hw, ht⟩
        rw [if_pos (by omega)] at ht
        subst ht
        obtain ⟨Vout, w', hstep, hw'⟩ := bb3_step env hy (BitVec.ofNat 8 (k + 1)) hw
        refine ⟨Vout, _, w', by simpa only [bind_pure] using hstep, _, rfl, ?_, hw', ?_⟩
        · rw [Function.iterate_succ_apply']; exact u44_geDbl hy
        · rw [Function.iterate_succ_apply', cond_iff (by omega) hn,
            show BitVec.ofNat 8 (k + 1) + 1#8 = BitVec.ofNat 8 (k + 1 + 1) by
              rw [BitVec.ofNat_add (k + 1) 1]]
          by_cases h : k + 1 + 1 < n.toNat
          · simp only [h, decide_true, if_true]
          · simp only [h, decide_false, Bool.false_eq_true, if_false])
      ⟨x, rfl, hx, hF, by rw [if_pos (by omega)]⟩
  obtain ⟨y, rfl, -, hw, ht⟩ := hInv
  rw [if_neg (by omega)] at ht
  subst ht
  exact ⟨u', hrun, hw⟩

end PointDbln

end Firedancer.Avx512
