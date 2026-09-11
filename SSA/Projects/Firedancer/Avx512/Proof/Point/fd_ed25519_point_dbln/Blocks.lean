/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Lanes
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Mem
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# `fd_ed25519_point_dbln`'s tail blocks

`^bb1` (block 0) stores the last doubling into `r`, `^bb2` (block 1) returns
`r`, `^bb3` (block 2) is the loop: one `FD_R43X6_GE_DBL` on the carried vectors
and the `i8` counter. Each reads `^bb0`'s definitions through `EntryEnv`;
`%k` is `Γout` variable `245 - k`, `%argN` is `248 - N`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointDbln

/-! ### Branch targets -/

/-- `^bb1(%333, %335, %337)`, threaded by the lifter: the last doubling. -/
abbrev hdr1 (q : Quad) : SuccArgs fd_ed25519_point_dbln.sigs :=
  ⟨0, by rfl, ([q.v03.map PoisonOr.value, q.v14.map PoisonOr.value, q.v25.map PoisonOr.value]ₕ :
    HVector TyDenote.toType [V8, V8, V8])⟩

/-- `^bb2`, the return. -/
abbrev hdr2 : SuccArgs fd_ed25519_point_dbln.sigs :=
  ⟨1, by rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb3(%246, %247, %248, %249)`: the loop header, `25` vector first, and the counter. -/
abbrev hdr3 (q : Quad) (c : BitVec 8) : SuccArgs fd_ed25519_point_dbln.sigs :=
  ⟨2, by rfl, ([q.v25.map PoisonOr.value, q.v14.map PoisonOr.value, q.v03.map PoisonOr.value,
    PoisonOr.value c]ₕ : HVector TyDenote.toType [V8, V8, V8, SLLVM.Ty.bitvec 8])⟩

/-! ### The ambient environment -/

/-- What the tail blocks read out of `^bb0`: `GE_DBL`'s constants, the loop's six
slots, `r`'s two field pointers, `r` and `n`. -/
structure EntryEnv (V : fd_ed25519_point_dbln.Γout.Valuation) (s : GlobalState) (r : Pointer)
    (n : BitVec 32) : Prop where
  c4 : V (⟨241, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 dblShift
  c24 : V (⟨221, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskG 8796093022189#64 8796093022207#64
  c41 : V (⟨204, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskG 8796093022207#64 8796093022207#64
  c59 : V (⟨186, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskG 8796093022207#64 1099511627775#64
  c76 : V (⟨169, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskE 8796093022189#64 8796093022207#64
  c93 : V (⟨152, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskE 8796093022207#64 8796093022207#64
  c110 : V (⟨135, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8)
    = pmaskE 8796093022207#64 1099511627775#64
  c111 : V (⟨134, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 nbias03
  c112 : V (⟨133, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 nbias
  c113 : V (⟨132, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadShift43
  c114 : V (⟨131, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadShift48
  c132 : V (⟨113, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = quadMul19
  c133 : V (⟨112, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadMask43
  c134 : V (⟨111, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 bias03
  c135 : V (⟨110, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 bias
  c136 : V (⟨109, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var V8) = toBitVecValue 64 quadMask48
  c137 : V (⟨108, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var (SLLVM.Ty.bitvec 8)) = .value 1#8
  s6 : V (⟨101, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 6)
  s7 : V (⟨100, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 7)
  s8 : V (⟨99, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 8)
  s9 : V (⟨98, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 9)
  s10 : V (⟨97, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 10)
  s11 : V (⟨96, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (slot s 11)
  r64 : V (⟨4, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value (r.withOffset 64)
  r128 : V (⟨1, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr)
    = .value (r.withOffset 128)
  vr : V (⟨248, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var SLLVM.Ty.ptr) = .value r
  vn : V (⟨246, by rfl⟩ : fd_ed25519_point_dbln.Γout.Var (SLLVM.Ty.bitvec 32)) = .value n

/-! ### `^bb2` -/

theorem bb2_run {V : fd_ed25519_point_dbln.Γout.Valuation} {s : GlobalState} {r : Pointer}
    {n : BitVec 32} (env : EntryEnv V s r n) (u : GlobalState) :
    StateT.run (fd_ed25519_point_dbln.blocks.run V hdr2) u = .value ([.value r]ₕ, u) := by
  denote_enter_block
  simp only [BlockCom.denote_term, Terminator.denote_ret, simp_spine]
  rw [env.vr]; rfl

/-! ### Stores and loads through ambient pointers

`GeDecode2.peel_store_amb`/`peel_load_vec_amb`, restated: a tail block's
operands resolve in two passes, the block's spine and then the ambient facts. -/

macro "dbln_store_amb " x:term ", " p:term ", " hp:term ", " st:term
    " as " st':term " := " hst':term " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_nil (s' := $st')
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_store (t := .vector 8 (.bitvec (.concrete 64)))
            (x := ($x).map PoisonOr.value) (flatten_vecBV $x)
            (show Fits (($st).mem) $p 512 from Fits.mono $hp (by omega)))]
          rw [$hst':term]
          rfl)]))

macro "dbln_load_amb " v:term ", " p:term ", " hp:term ", " hval:term ", " st:term
    " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_value (x := ($v).map PoisonOr.value) (s' := $st)
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_load (t := .vector 8 (.bitvec (.concrete 64)))
            (($hp).1.choose_spec.1)
            (by have := ($hp).1.choose_spec.2
                show ($p).offsetInBits + 512 ≤ _
                simp only [LiveBlock.lengthInBits] at *
                omega))]
          rw [unflatten_readVec $hp (live?_of_getElem? ($hp).1.choose_spec.1), $hval:term]
          rfl)]))

/-! ### `^bb1` -/

theorem fits_field {m : MemoryState} {r : Pointer} (hr : IsQuadPtr m r) :
    Fits m r 512 ∧ Fits m (r.withOffset 64) 512 ∧ Fits m (r.withOffset 128) 512 :=
  ⟨Fits.mono hr.1 (by omega), Fits.mono (remainingFits m r hr.1 64 (by simp)) (by simp),
    Fits.mono (remainingFits m r hr.1 128 (by simp)) (by simp)⟩

set_option maxHeartbeats 1000000 in
/-- **`^bb1`**: the last doubling's three stores into `r`, then `^bb2`. -/
theorem bb1_run {V : fd_ed25519_point_dbln.Γout.Valuation} {s : GlobalState} {r : Pointer}
    {n : BitVec 32} (env : EntryEnv V s r n) (q : Quad) {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame s m₁ u) (hr : IsQuadPtr m₁ r) (hlt : r.id.id < s.alloc.nextFreeBlock) :
    ∃ u', StateT.run (fd_ed25519_point_dbln.blocks.run V (hdr1 q)) u = .value ([.value r]ₕ, u')
      ∧ Frame s (m₁.writeQuad r q) u' := by
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
  dbln_store_amb q.v03, r, g0, u as u1 := hu1 with simp_spine, env.vr
  refine name_of ({ u1 with mem := u1.mem.splice (r.withOffset 64) (vecBV q.v14) }) fun u2 hu2 => ?_
  have g64' : Fits u1.mem (r.withOffset 64) 512 := by rw [hu1]; exact fits_splice g64
  dbln_store_amb q.v14, (r.withOffset 64), g64', u1 as u2 := hu2
    with simp_spine, env.r64
  refine name_of ({ u2 with mem := u2.mem.splice (r.withOffset 128) (vecBV q.v25) })
    fun u3 hu3 => ?_
  have g128' : Fits u2.mem (r.withOffset 128) 512 := by
    rw [hu2, hu1]; exact fits_splice (fits_splice g128)
  dbln_store_amb q.v25, (r.withOffset 128), g128', u2
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
    {m₁ : MemoryState} {u : GlobalState} (hF : Frame s m₁ u) :
    ∃ Vout u', StateT.run ((fd_ed25519_point_dbln.blocks.get (hdr3 x c).idx (hdr3 x c).hidx).2.denote
        (Ctxt.Valuation.ofHVector (hdr3 x c).args.reverse ++ V) >>= pure) u
      = .value ((Vout, .inr (if BitVec.ult (BitVec.setWidth 32 (c + 1#8)) n
          then hdr3 (geDbl x) (c + 1#8) else hdr1 (geDbl x))), u')
      ∧ Frame s m₁ u' := by
  denote_reduce_get
  denote_number_from 250
  denote_step_reduce v 258 only [simp_spine]
  have e03 := denote_addXY hx.1 hv250 hv253 hv254
  have e14 := denote_addXY hx.2.1 hv251 hv255 hv256
  have e25 := denote_addXY hx.2.2 hv252 hv257 hv258
  denote_clear v 250 258
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
  dbln_load_amb (quadSqrResult (dblTa x)).v03, (slot s 6), hp6, hr6, u1 with simp_spine, env.s6
  dbln_load_amb (quadSqrResult (dblTa x)).v14, (slot s 7), hp7, hr7, u1 with simp_spine, env.s7
  dbln_load_amb (quadSqrResult (dblTa x)).v25, (slot s 8), hp8, hr8, u1 with simp_spine, env.s8
  iterate 3 peel_lifetime
  denote_step_reduce v 323 only [simp_spine]
  have p03 := denote_egfh env.c4 env.c24 env.c76 hv262 hv265 hv268 hv271 hv272 hv277 hv278 hv279
    hv286 hv287 hv292 hv293 hv294
  have p14 := denote_egfh env.c4 env.c41 env.c93 hv263 hv266 hv269 hv273 hv274 hv280 hv281 hv282
    hv288 hv289 hv295 hv296 hv297
  have p25 := denote_egfh env.c4 env.c59 env.c110 hv264 hv267 hv270 hv275 hv276 hv283 hv284 hv285
    hv290 hv291 hv298 hv299 hv300
  clear hv262 hv263 hv264 hv265 hv266 hv267 hv268 hv269 hv270 hv271 hv272 hv273 hv274 hv275
    hv276 hv277 hv278 hv279 hv280 hv281 hv282 hv283 hv284 hv285 hv286 hv287 hv288 hv289 hv290
    hv291 hv292 hv293 hv294 hv295 hv296 hv297 hv298 hv299 hv300
  subst p03 p14 p25
  have r03 := denote_foldSigned03 (P := egfhQuad (quadSqrResult (dblTa x))) env.c111 env.c112
    env.c114 env.c132 env.c133 env.c134 hv301 hv303 hv306 hv307 hv308 hv309 hv310 hv311
  have r14 := denote_foldSigned14 (P := egfhQuad (quadSqrResult (dblTa x))) env.c111 env.c112
    env.c113 env.c133 env.c135 hv301 hv302 hv304 hv312 hv313 hv314
  have r25 := denote_foldSigned25 (P := egfhQuad (quadSqrResult (dblTa x))) env.c112 env.c113
    env.c135 env.c136 hv302 hv303 hv305 hv315 hv316 hv317
  clear hv301 hv302 hv303 hv304 hv305 hv306 hv307 hv308 hv309 hv310 hv311 hv312 hv313 hv314
    hv315 hv316 hv317
  subst r03 r14 r25
  have g03 := denote_permGE hv318
  have g14 := denote_permGE hv319
  have g25 := denote_permGE hv320
  have f03 := denote_permFH hv321
  have f14 := denote_permFH hv322
  have f25 := denote_permFH hv323
  clear hv318 hv319 hv320 hv321 hv322 hv323
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
  dbln_load_amb (quadMulResult (geQuad (dblR x)) (fhQuad (dblR x))).v03, (slot s 9), hp9, hr9, u2
    with simp_spine, env.s9
  dbln_load_amb (quadMulResult (geQuad (dblR x)) (fhQuad (dblR x))).v14, (slot s 10), hp10, hr10,
    u2 with simp_spine, env.s10
  dbln_load_amb (quadMulResult (geQuad (dblR x)) (fhQuad (dblR x))).v25, (slot s 11), hp11, hr11,
    u2 with simp_spine, env.s11
  iterate 3 peel_lifetime
  denote_step_reduce v 340 only [simp_spine]
  have o03 := denote_foldU03 env.c114 env.c132 env.c133 hv329 hv330 hv331 hv332 hv333
  have o14 := denote_foldU14 env.c113 env.c133 hv327 hv334 hv335
  have o25 := denote_foldU25 env.c113 env.c136 hv328 hv336 hv337
  clear hv327 hv328 hv329 hv330 hv331 hv332 hv333 hv334 hv335 hv336 hv337
  subst o03 o14 o25
  replace hv338 : v338 = .value (c + 1#8) := by rw [hv338, env.c137]; rfl
  subst hv338
  replace hv339 : v339 = .value (BitVec.setWidth 32 (c + 1#8)) := by rw [hv339]; rfl
  subst hv339
  replace hv340 : v340 = .value (BitVec.ofBool (BitVec.ult (BitVec.setWidth 32 (c + 1#8)) n)) := by
    rw [hv340, env.vn]; rfl
  subst hv340
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
    {x : Quad} (hx : QuadU44 x) {m₁ : MemoryState} {u : GlobalState} (hF : Frame s m₁ u) :
    ∃ u', StateT.run (fd_ed25519_point_dbln.blocks.run V (hdr3 x 1#8)) u
        = StateT.run (fd_ed25519_point_dbln.blocks.run V (hdr1 (geDbl^[n.toNat - 1] x))) u'
      ∧ Frame s m₁ u' := by
  obtain ⟨t, u', hrun, hInv⟩ :=
    Blocks.run_loop_args (bs := fd_ed25519_point_dbln.blocks) (Vamb := V)
      (Inv := fun k t w => ∃ y, y = geDbl^[k] x ∧ QuadU44 y ∧ Frame s m₁ w ∧
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
