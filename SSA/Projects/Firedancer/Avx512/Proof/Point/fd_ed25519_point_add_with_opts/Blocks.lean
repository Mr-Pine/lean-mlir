/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_add_with_opts
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts.Lanes
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Frame

/-!
# `fd_ed25519_point_add_with_opts`'s tail blocks

`^bb1` (block 0) is `FD_R43X6_GE_ADD_TABLE_ALT` up to the last multiply; `^bb3`
(block 2) folds it and stores into `r`. Each reads `^bb0`'s definitions through
`EntryEnv`; `%k` is `Γout` variable `155 - k`, `%argN` is `159 - N`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointAdd
open Ge

/-! ### Branch targets -/

/-- `^bb1`, the precomputed path. -/
abbrev hdr1 : SuccArgs fd_ed25519_point_add_with_opts.sigs :=
  ⟨0, by rfl, (.nil : HVector TyDenote.toType [])⟩

/-- `^bb3(%400, %401, %402)`: the last product, before its fold. -/
abbrev hdr3 (q : Quad) : SuccArgs fd_ed25519_point_add_with_opts.sigs :=
  ⟨2, by rfl, ([q.v03.map PoisonOr.value, q.v14.map PoisonOr.value, q.v25.map PoisonOr.value]ₕ :
    HVector TyDenote.toType [V8, V8, V8])⟩

/-! ### The ambient environment -/

/-- What the tail blocks read out of `^bb0`. -/
structure EntryEnv (V : fd_ed25519_point_add_with_opts.Γout.Valuation) (s : GlobalState)
    (r a b : Pointer) : Prop where
  c2 : V (⟨153, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 0#64
  c24 : V (⟨131, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskE 8796093022189#64 8796093022207#64
  c41 : V (⟨114, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskE 8796093022207#64 8796093022207#64
  c59 : V (⟨96, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskE 8796093022207#64 1099511627775#64
  c60 : V (⟨95, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 nbias03
  c61 : V (⟨94, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 nbias
  c62 : V (⟨93, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadShift43
  c63 : V (⟨92, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadShift48
  c81 : V (⟨74, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = quadMul19
  c82 : V (⟨73, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadMask43
  c83 : V (⟨72, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 bias03
  c84 : V (⟨71, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 bias
  c85 : V (⟨70, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadMask48
  c102 : V (⟨53, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskEF 8796093022189#64 8796093022207#64
  c119 : V (⟨36, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskEF 8796093022207#64 8796093022207#64
  c136 : V (⟨19, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskEF 8796093022207#64 1099511627775#64
  s0 : V (⟨15, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 0)
  s1 : V (⟨14, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 1)
  s2 : V (⟨13, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 2)
  s3 : V (⟨12, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 3)
  s4 : V (⟨11, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 4)
  s5 : V (⟨10, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 5)
  vr : V (⟨159, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value r
  va : V (⟨158, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value a
  vb : V (⟨157, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value b

/-! ### `^bb3` -/

set_option maxHeartbeats 1000000 in
/-- **`^bb3`**: `FD_R43X6_QUAD_FOLD_UNSIGNED` on the carried product, its three stores
into `r`, and the return. -/
theorem bb3_run_ex {V : fd_ed25519_point_add_with_opts.Γout.Valuation} {s : GlobalState}
    {r a b : Pointer} (env : EntryEnv V s r a b) (q : Quad) {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame 15 s m₁ u) (hr : IsQuadPtr m₁ r) (hlt : r.id.id < s.alloc.nextFreeBlock) :
    ∃ u', StateT.run (fd_ed25519_point_add_with_opts.blocks.run V (hdr3 q)) u
        = .value ([.value r]ₕ, u')
      ∧ Frame 15 s (m₁.writeQuad r (foldQuad q)) u' := by
  have hlive := hF.below r.id hlt
  have f0 := (fits_field hr).1
  have f64 := (fits_field hr).2.1
  have f128 := (fits_field hr).2.2
  have g0 : Fits u.mem r 512 := fits_of_live?_eq hlive f0
  have g64 : Fits u.mem (r.withOffset 64) 512 := fits_of_live?_eq (p := r.withOffset 64) hlive f64
  have g128 : Fits u.mem (r.withOffset 128) 512 :=
    fits_of_live?_eq (p := r.withOffset 128) hlive f128
  have hF1 := hF.splice r (vecBV (foldQuad q).v03)
  have hF2 := hF1.splice (r.withOffset 64) (vecBV (foldQuad q).v14)
  have hF3 := hF2.splice (r.withOffset 128) (vecBV (foldQuad q).v25)
  denote_enter_block
  denote_number_from 403
  denote_step_reduce v 409 only [simp_spine]
  have o03 := denote_foldU03 env.c63 env.c81 env.c82 hv405 hv406 hv407 hv408 hv409
  clear hv405 hv406 hv407 hv408 hv409
  subst o03
  refine name_of ({ u with mem := u.mem.splice r (vecBV (foldQuad q).v03) }) fun u1 hu1 => ?_
  ge_store_amb (foldQuad q).v03, r, g0, u as u1 := hu1 with simp_spine, env.vr
  denote_step_reduce v 412 only [simp_spine]
  have o14 := denote_foldU14 env.c62 env.c82 hv403 hv410 hv411
  clear hv403 hv410 hv411
  subst o14
  have e412 : v412 = .value (r.withOffset 64) := by rw [hv412, env.vr, env.c2]; rfl
  clear hv412
  subst e412
  refine name_of ({ u1 with mem := u1.mem.splice (r.withOffset 64) (vecBV (foldQuad q).v14) })
    fun u2 hu2 => ?_
  have g64' : Fits u1.mem (r.withOffset 64) 512 := by rw [hu1]; exact fits_splice g64
  ge_store_amb (foldQuad q).v14, (r.withOffset 64), g64', u1 as u2 := hu2 with simp_spine
  denote_step_reduce v 415 only [simp_spine]
  have o25 := denote_foldU25 env.c62 env.c85 hv404 hv413 hv414
  clear hv404 hv413 hv414
  subst o25
  have e415 : v415 = .value (r.withOffset 128) := by rw [hv415, env.vr, env.c2]; rfl
  clear hv415
  subst e415
  refine name_of ({ u2 with mem := u2.mem.splice (r.withOffset 128) (vecBV (foldQuad q).v25) })
    fun u3 hu3 => ?_
  have g128' : Fits u2.mem (r.withOffset 128) 512 := by
    rw [hu2, hu1]; exact fits_splice (fits_splice g128)
  ge_store_amb (foldQuad q).v25, (r.withOffset 128), g128', u2 as u3 := hu3 with simp_spine
  refine ⟨u3, ?_, by rw [hu3, hu2, hu1]; exact hF3⟩
  simp_return
  simp [env.vr]

/-- `bb3_run_ex`, in continuation form. -/
theorem bb3_run {V : fd_ed25519_point_add_with_opts.Γout.Valuation} {s : GlobalState}
    {r a b : Pointer} (env : EntryEnv V s r a b) (q : Quad) {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame 15 s m₁ u) (hr : IsQuadPtr m₁ r) (hlt : r.id.id < s.alloc.nextFreeBlock)
    {P : Prop}
    (k : ∀ u', StateT.run (fd_ed25519_point_add_with_opts.blocks.run V (hdr3 q)) u
        = .value ([.value r]ₕ, u') → Frame 15 s (m₁.writeQuad r (foldQuad q)) u' → P) : P :=
  (bb3_run_ex env q hF hr hlt).elim fun u' h => k u' h.1 h.2

/-! ### `^bb1` -/

theorem u47s {q : Quad} (h : QuadU44 q) :
    R43x6.U47 q.v03 ∧ R43x6.U47 q.v14 ∧ R43x6.U47 q.v25 :=
  ⟨u47_of_u44 h.1, u47_of_u44 h.2.1, u47_of_u44 h.2.2⟩

/-- A caller's QUAD, as the three vector reads the region makes of it. -/
theorem quad_vecs {s : GlobalState} {m₁ : MemoryState} {u : GlobalState} (hF : Frame 15 s m₁ u)
    {a : Pointer} (ha : IsQuadPtr m₁ a) (hlt : a.id.id < s.alloc.nextFreeBlock) {P : Prop}
    (k : ∀ (h0 : IsVecPtr u.mem a) (h64 : IsVecPtr u.mem (a.withOffset 64))
      (h128 : IsVecPtr u.mem (a.withOffset 128)),
      readVec h0 = (readQuad ha).v03 → readVec h64 = (readQuad ha).v14
        → readVec h128 = (readQuad ha).v25 → P) : P := by
  have hl := hF.below a.id hlt
  obtain ⟨r03, r14, r25⟩ := readVec_quad ha hl
  have hf : Fits u.mem a (3 * 8 * 64) := fits_of_live?_eq hl ha.1
  have hoff : ∀ o : Nat, o ≤ 128 → (a.withOffset (BitVec.ofNat 64 o)).offset.toNat + 64 ≤ 2 ^ 64 :=
    fun o ho => by
      have := ha.2
      simp only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h0 : IsVecPtr u.mem a := ⟨Fits.mono hf (by omega), by have := ha.2; omega⟩
  have h64 : IsVecPtr u.mem (a.withOffset 64) :=
    ⟨Fits.mono (remainingFits u.mem a hf 64 (by decide)) (by decide), hoff 64 (by omega)⟩
  have h128 : IsVecPtr u.mem (a.withOffset 128) :=
    ⟨Fits.mono (remainingFits u.mem a hf 128 (by decide)) (by decide), hoff 128 (by omega)⟩
  exact k h0 h64 h128 (r03 h0) (r14 h64) (r25 h128)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **`^bb1`**: `FD_R43X6_GE_ADD_TABLE_ALT` through slots 0-5, up to the last product,
carried to `^bb3`. -/
theorem bb1_run_ex {V : fd_ed25519_point_add_with_opts.Γout.Valuation} {s : GlobalState}
    {r a b : Pointer} (env : EntryEnv V s r a b) (ha : IsQuadPtr s.mem a) (hb : IsQuadPtr s.mem b)
    (hua : QuadU44 (readQuad ha)) (hub : QuadU44 (readQuad hb))
    (hla : a.id.id < s.alloc.nextFreeBlock) (hlb : b.id.id < s.alloc.nextFreeBlock)
    {u : GlobalState} (hF : Frame 15 s s.mem u) :
    ∃ u', StateT.run (fd_ed25519_point_add_with_opts.blocks.run V hdr1) u
        = StateT.run (fd_ed25519_point_add_with_opts.blocks.run V
            (hdr3 (quadMulResult (egegQuad (addR (readQuad ha) (readQuad hb)))
              (fhfhQuad (addR (readQuad ha) (readQuad hb)))))) u'
      ∧ Frame 15 s s.mem u' := by
  refine quad_vecs hF hb hlb fun pb0 pb64 pb128 rb03 rb14 rb25 => ?_
  refine quad_vecs hF ha hla fun pa0 pa64 pa128 ra03 ra14 ra25 => ?_
  denote_enter_block
  denote_number_from 156
  -- `b`'s three vectors
  ge_load_amb (readQuad hb).v03, b, pb0, rb03, u with simp_spine, env.vb
  denote_step_reduce v 157 only [simp_spine]
  have e157 : v157 = .value (b.withOffset 64) := by rw [hv157, env.vb, env.c2]; rfl
  clear hv157
  subst e157
  ge_load_amb (readQuad hb).v14, (b.withOffset 64), pb64, rb14, u with simp_spine
  denote_step_reduce v 159 only [simp_spine]
  have e159 : v159 = .value (b.withOffset 128) := by rw [hv159, env.vb, env.c2]; rfl
  clear hv159
  subst e159
  ge_load_amb (readQuad hb).v25, (b.withOffset 128), pb128, rb25, u with simp_spine
  -- `a`'s, each permuted as it is loaded
  ge_load_amb (readQuad ha).v03, a, pa0, ra03, u with simp_spine, env.va
  denote_step_reduce v 163 only [simp_spine]
  have e163 : v163 = .value (a.withOffset 64) := by rw [hv163, env.va, env.c2]; rfl
  clear hv163
  subst e163
  ge_load_amb (readQuad ha).v14, (a.withOffset 64), pa64, ra14, u with simp_spine
  denote_step_reduce v 166 only [simp_spine]
  have e166 : v166 = .value (a.withOffset 128) := by rw [hv166, env.va, env.c2]; rfl
  clear hv166
  subst e166
  ge_load_amb (readQuad ha).v25, (a.withOffset 128), pa128, ra25, u with simp_spine
  -- `(Y-X, Y+X, 2Z, T)` and the signed fold
  denote_step_reduce v 200 only [simp_spine]
  have t03 := denote_tb env.c24 hv162 hv169 hv170 hv171 hv178 hv179
  have t14 := denote_tb env.c41 hv165 hv172 hv173 hv174 hv180 hv181
  have t25 := denote_tb env.c59 hv168 hv175 hv176 hv177 hv182 hv183
  clear hv162 hv165 hv168 hv169 hv170 hv171 hv172 hv173 hv174 hv175 hv176 hv177 hv178 hv180 hv182
  subst t03 t14 t25
  have f03 := denote_foldSigned03 (P := tbQuad (readQuad ha)) env.c60 env.c61 env.c63 env.c81
    env.c82 env.c83 hv184 hv186 hv189 hv190 hv191 hv192 hv193 hv194
  have f14 := denote_foldSigned14 (P := tbQuad (readQuad ha)) env.c60 env.c61 env.c62 env.c82
    env.c84 hv184 hv185 hv187 hv195 hv196 hv197
  have f25 := denote_foldSigned25 (P := tbQuad (readQuad ha)) env.c61 env.c62 env.c84 env.c85
    hv185 hv186 hv188 hv198 hv199 hv200
  clear hv184 hv185 hv186 hv187 hv188 hv189 hv190 hv191 hv192 hv193 hv195 hv196 hv198 hv199
  subst f03 f14 f25
  -- `(A, B, D, C)`
  iterate 3 peel_lifetime
  refine mul_step hF (readQuad hb) (tbF (readQuad ha)) (u47s hub) (u47s (u44_tbF hua))
    (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun u1 hrun1 hF1 hp0 hp1 hp2 hr0 hr1 hr2 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8, V8, V8, V8])
    (argVals := [(tbF (readQuad ha)).v25.map PoisonOr.value,
      (tbF (readQuad ha)).v14.map PoisonOr.value, (tbF (readQuad ha)).v03.map PoisonOr.value,
      (readQuad hb).v25.map PoisonOr.value, (readQuad hb).v14.map PoisonOr.value,
      (readQuad hb).v03.map PoisonOr.value,
      PoisonOr.value (slot s 2), PoisonOr.value (slot s 1), PoisonOr.value (slot s 0)]ₕ)
    (by simp only [simp_spine, env.s0, env.s1, env.s2]; rfl) hrun1]
  ge_load_amb (quadMulResult (readQuad hb) (tbF (readQuad ha))).v03, (slot s 0), hp0, hr0, u1
    with simp_spine, env.s0
  ge_load_amb (quadMulResult (readQuad hb) (tbF (readQuad ha))).v14, (slot s 1), hp1, hr1, u1
    with simp_spine, env.s1
  ge_load_amb (quadMulResult (readQuad hb) (tbF (readQuad ha))).v25, (slot s 2), hp2, hr2, u1
    with simp_spine, env.s2
  iterate 3 peel_lifetime
  denote_step_reduce v 214 only [simp_spine]
  have o03 := denote_foldU03 env.c63 env.c81 env.c82 hv206 hv207 hv208 hv209 hv210
  have o14 := denote_foldU14 env.c62 env.c82 hv204 hv211 hv212
  have o25 := denote_foldU25 env.c62 env.c85 hv205 hv213 hv214
  clear hv204 hv205 hv206 hv207 hv208 hv209 hv211 hv213
  subst o03 o14 o25
  -- `(E, H, G, F)` and the signed fold
  have hA := u44_addA hua hub
  denote_step_reduce v 232 only [simp_spine]
  have e03 := denote_ehgf (v := (addA (readQuad ha) (readQuad hb)).v03) hA.1 (by decide) (by decide)
    env.c102 hv215 hv218 hv219 hv220 hv227 hv228
  have e14 := denote_ehgf (v := (addA (readQuad ha) (readQuad hb)).v14) hA.2.1 (by decide)
    (by decide) env.c119 hv216 hv221 hv222 hv223 hv229 hv230
  have e25 := denote_ehgf (v := (addA (readQuad ha) (readQuad hb)).v25) hA.2.2 (by decide)
    (by decide) env.c136 hv217 hv224 hv225 hv226 hv231 hv232
  clear hv215 hv216 hv217 hv218 hv219 hv220 hv221 hv222 hv223 hv224 hv225 hv226 hv227 hv229 hv231
  subst e03 e14 e25
  denote_step_reduce v 249 only [simp_spine]
  have g03 := denote_foldSigned03' (P := ehgfQuad (addA (readQuad ha) (readQuad hb))) env.c60
    env.c61 env.c63 env.c81 env.c82 env.c83 hv233 hv235 hv238 hv239 hv240 hv241 hv242 hv243
  have g14 := denote_foldSigned14' (P := ehgfQuad (addA (readQuad ha) (readQuad hb))) env.c60
    env.c61 env.c62 env.c82 env.c84 hv233 hv234 hv236 hv244 hv245 hv246
  have g25 := denote_foldSigned25 (P := ehgfQuad (addA (readQuad ha) (readQuad hb))) env.c61
    env.c62 env.c84 env.c85 hv234 hv235 hv237 hv247 hv248 hv249
  clear hv233 hv234 hv235 hv236 hv237 hv238 hv239 hv240 hv241 hv242 hv244 hv245 hv247 hv248
  subst g03 g14 g25
  -- the permutes and the last product
  denote_step_reduce v 255 only [simp_spine]
  have p03 := denote_permEGGE hv250
  have p14 := denote_permEGGE hv251
  have p25 := denote_permEGGE hv252
  have q03 := denote_permFHFH hv253
  have q14 := denote_permFHFH hv254
  have q25 := denote_permFHFH hv255
  clear hv250 hv251 hv252 hv253 hv254 hv255
  subst p03 p14 p25 q03 q14 q25
  have hR := u44_addR hua hub
  iterate 3 peel_lifetime
  refine mul_step hF1 (egegQuad (addR (readQuad ha) (readQuad hb)))
    (fhfhQuad (addR (readQuad ha) (readQuad hb))) (u47s (u44_egegQuad hR))
    (u47s (u44_fhfhQuad hR)) (i := 3) (j := 4) (k := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) fun u2 hrun2 hF2 hp3 hp4 hp5 hr3 hr4 hr5 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8, V8, V8, V8])
    (argVals := [(fhfhQuad (addR (readQuad ha) (readQuad hb))).v25.map PoisonOr.value,
      (fhfhQuad (addR (readQuad ha) (readQuad hb))).v14.map PoisonOr.value,
      (fhfhQuad (addR (readQuad ha) (readQuad hb))).v03.map PoisonOr.value,
      (egegQuad (addR (readQuad ha) (readQuad hb))).v25.map PoisonOr.value,
      (egegQuad (addR (readQuad ha) (readQuad hb))).v14.map PoisonOr.value,
      (egegQuad (addR (readQuad ha) (readQuad hb))).v03.map PoisonOr.value,
      PoisonOr.value (slot s 5), PoisonOr.value (slot s 4), PoisonOr.value (slot s 3)]ₕ)
    (by simp only [simp_spine, env.s3, env.s4, env.s5]; rfl) hrun2]
  ge_load_amb (quadMulResult (egegQuad (addR (readQuad ha) (readQuad hb)))
    (fhfhQuad (addR (readQuad ha) (readQuad hb)))).v03, (slot s 3), hp3, hr3, u2
    with simp_spine, env.s3
  ge_load_amb (quadMulResult (egegQuad (addR (readQuad ha) (readQuad hb)))
    (fhfhQuad (addR (readQuad ha) (readQuad hb)))).v14, (slot s 4), hp4, hr4, u2
    with simp_spine, env.s4
  ge_load_amb (quadMulResult (egegQuad (addR (readQuad ha) (readQuad hb)))
    (fhfhQuad (addR (readQuad ha) (readQuad hb)))).v25, (slot s 5), hp5, hr5, u2
    with simp_spine, env.s5
  iterate 3 peel_lifetime
  refine ⟨u2, ?_, hF2⟩
  simp only [BlockCom.denote_term, Terminator.denote_br, simp_spine, pure_bind]
  rfl

/-- `bb1_run_ex`, in continuation form. -/
theorem bb1_run {V : fd_ed25519_point_add_with_opts.Γout.Valuation} {s : GlobalState}
    {r a b : Pointer} (env : EntryEnv V s r a b) (ha : IsQuadPtr s.mem a) (hb : IsQuadPtr s.mem b)
    (hua : QuadU44 (readQuad ha)) (hub : QuadU44 (readQuad hb))
    (hla : a.id.id < s.alloc.nextFreeBlock) (hlb : b.id.id < s.alloc.nextFreeBlock)
    {u : GlobalState} (hF : Frame 15 s s.mem u) {P : Prop}
    (k : ∀ u', StateT.run (fd_ed25519_point_add_with_opts.blocks.run V hdr1) u
        = StateT.run (fd_ed25519_point_add_with_opts.blocks.run V
            (hdr3 (quadMulResult (egegQuad (addR (readQuad ha) (readQuad hb)))
              (fhfhQuad (addR (readQuad ha) (readQuad hb)))))) u' → Frame 15 s s.mem u' → P) :
    P :=
  (bb1_run_ex env ha hb hua hub hla hlb hF).elim fun u' h => k u' h.1 h.2

end PointAdd

end Firedancer.Avx512
