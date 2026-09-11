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
`EntryEnv`; `%k` is `Γout` variable `103 - k`, `%argN` is `107 - N`.
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

/-- `^bb3(%348, %349, %350)`: the last product, before its fold. -/
abbrev hdr3 (q : Quad) : SuccArgs fd_ed25519_point_add_with_opts.sigs :=
  ⟨2, by rfl, ([q.v03.map PoisonOr.value, q.v14.map PoisonOr.value, q.v25.map PoisonOr.value]ₕ :
    HVector TyDenote.toType [V8, V8, V8])⟩

/-! ### The ambient environment -/

/-- What the tail blocks read out of `^bb0`. -/
structure EntryEnv (V : fd_ed25519_point_add_with_opts.Γout.Valuation) (s : GlobalState)
    (r a b : Pointer) : Prop where
  c33 : V (⟨70, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskE 8796093022189#64 8796093022207#64
  c42 : V (⟨61, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskE 8796093022207#64 8796093022207#64
  c51 : V (⟨52, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskE 8796093022207#64 1099511627775#64
  c11 : V (⟨92, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 nbias03
  c10 : V (⟨93, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 nbias
  c9 : V (⟨94, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadShift43
  c8 : V (⟨95, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadShift48
  c60 : V (⟨43, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = quadMul19
  c6 : V (⟨97, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadMask43
  c5 : V (⟨98, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 bias03
  c4 : V (⟨99, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8) = toBitVecValue 64 bias
  c3 : V (⟨100, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = toBitVecValue 64 quadMask48
  c69 : V (⟨34, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskEF 8796093022189#64 8796093022207#64
  c78 : V (⟨25, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskEF 8796093022207#64 8796093022207#64
  c87 : V (⟨16, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var V8)
    = pmaskEF 8796093022207#64 1099511627775#64
  s0 : V (⟨15, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 0)
  s1 : V (⟨14, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 1)
  s2 : V (⟨13, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 2)
  s3 : V (⟨12, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 3)
  s4 : V (⟨11, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 4)
  s5 : V (⟨10, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value (slot s 5)
  vr : V (⟨107, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value r
  va : V (⟨106, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value a
  vb : V (⟨105, by rfl⟩ : fd_ed25519_point_add_with_opts.Γout.Var SLLVM.Ty.ptr) = .value b

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
  denote_number_from 351
  denote_step_reduce v 357 only [simp_spine]
  have o03 := denote_foldU03 env.c8 env.c60 env.c6 hv353 hv354 hv355 hv356 hv357
  clear hv353 hv354 hv355 hv356 hv357
  subst o03
  refine name_of ({ u with mem := u.mem.splice r (vecBV (foldQuad q).v03) }) fun u1 hu1 => ?_
  ge_store_amb (foldQuad q).v03, r, g0, u as u1 := hu1 with simp_spine, env.vr
  denote_step_reduce v 360 only [simp_spine]
  have o14 := denote_foldU14 env.c9 env.c6 hv351 hv358 hv359
  clear hv351 hv358 hv359
  subst o14
  have e360 : v360 = .value (r.withOffset 64) := by rw [hv360, env.vr]; rfl
  clear hv360
  subst e360
  refine name_of ({ u1 with mem := u1.mem.splice (r.withOffset 64) (vecBV (foldQuad q).v14) })
    fun u2 hu2 => ?_
  have g64' : Fits u1.mem (r.withOffset 64) 512 := by rw [hu1]; exact fits_splice g64
  ge_store_amb (foldQuad q).v14, (r.withOffset 64), g64', u1 as u2 := hu2 with simp_spine
  denote_step_reduce v 363 only [simp_spine]
  have o25 := denote_foldU25 env.c9 env.c3 hv352 hv361 hv362
  clear hv352 hv361 hv362
  subst o25
  have e363 : v363 = .value (r.withOffset 128) := by rw [hv363, env.vr]; rfl
  clear hv363
  subst e363
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
  denote_number_from 104
  -- `b`'s three vectors
  ge_load_amb (readQuad hb).v03, b, pb0, rb03, u with simp_spine, env.vb
  denote_step_reduce v 105 only [simp_spine]
  have e105 : v105 = .value (b.withOffset 64) := by rw [hv105, env.vb]; rfl
  clear hv105
  subst e105
  ge_load_amb (readQuad hb).v14, (b.withOffset 64), pb64, rb14, u with simp_spine
  denote_step_reduce v 107 only [simp_spine]
  have e107 : v107 = .value (b.withOffset 128) := by rw [hv107, env.vb]; rfl
  clear hv107
  subst e107
  ge_load_amb (readQuad hb).v25, (b.withOffset 128), pb128, rb25, u with simp_spine
  -- `a`'s, each permuted as it is loaded
  ge_load_amb (readQuad ha).v03, a, pa0, ra03, u with simp_spine, env.va
  denote_step_reduce v 111 only [simp_spine]
  have e111 : v111 = .value (a.withOffset 64) := by rw [hv111, env.va]; rfl
  clear hv111
  subst e111
  ge_load_amb (readQuad ha).v14, (a.withOffset 64), pa64, ra14, u with simp_spine
  denote_step_reduce v 114 only [simp_spine]
  have e114 : v114 = .value (a.withOffset 128) := by rw [hv114, env.va]; rfl
  clear hv114
  subst e114
  ge_load_amb (readQuad ha).v25, (a.withOffset 128), pa128, ra25, u with simp_spine
  -- `(Y-X, Y+X, 2Z, T)` and the signed fold
  denote_step_reduce v 148 only [simp_spine]
  have t03 := denote_tb env.c33 hv110 hv117 hv118 hv119 hv126 hv127
  have t14 := denote_tb env.c42 hv113 hv120 hv121 hv122 hv128 hv129
  have t25 := denote_tb env.c51 hv116 hv123 hv124 hv125 hv130 hv131
  clear hv110 hv113 hv116 hv117 hv118 hv119 hv120 hv121 hv122 hv123 hv124 hv125 hv126 hv128 hv130
  subst t03 t14 t25
  have f03 := denote_foldSigned03 (P := tbQuad (readQuad ha)) env.c11 env.c10 env.c8 env.c60
    env.c6 env.c5 hv132 hv134 hv137 hv138 hv139 hv140 hv141 hv142
  have f14 := denote_foldSigned14 (P := tbQuad (readQuad ha)) env.c11 env.c10 env.c9 env.c6
    env.c4 hv132 hv133 hv135 hv143 hv144 hv145
  have f25 := denote_foldSigned25 (P := tbQuad (readQuad ha)) env.c10 env.c9 env.c4 env.c3
    hv133 hv134 hv136 hv146 hv147 hv148
  clear hv132 hv133 hv134 hv135 hv136 hv137 hv138 hv139 hv140 hv141 hv143 hv144 hv146 hv147
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
  denote_step_reduce v 162 only [simp_spine]
  have o03 := denote_foldU03 env.c8 env.c60 env.c6 hv154 hv155 hv156 hv157 hv158
  have o14 := denote_foldU14 env.c9 env.c6 hv152 hv159 hv160
  have o25 := denote_foldU25 env.c9 env.c3 hv153 hv161 hv162
  clear hv152 hv153 hv154 hv155 hv156 hv157 hv159 hv161
  subst o03 o14 o25
  -- `(E, H, G, F)` and the signed fold
  have hA := u44_addA hua hub
  denote_step_reduce v 180 only [simp_spine]
  have e03 := denote_ehgf (v := (addA (readQuad ha) (readQuad hb)).v03) hA.1 (by decide) (by decide)
    env.c69 hv163 hv166 hv167 hv168 hv175 hv176
  have e14 := denote_ehgf (v := (addA (readQuad ha) (readQuad hb)).v14) hA.2.1 (by decide)
    (by decide) env.c78 hv164 hv169 hv170 hv171 hv177 hv178
  have e25 := denote_ehgf (v := (addA (readQuad ha) (readQuad hb)).v25) hA.2.2 (by decide)
    (by decide) env.c87 hv165 hv172 hv173 hv174 hv179 hv180
  clear hv163 hv164 hv165 hv166 hv167 hv168 hv169 hv170 hv171 hv172 hv173 hv174 hv175 hv177 hv179
  subst e03 e14 e25
  denote_step_reduce v 197 only [simp_spine]
  have g03 := denote_foldSigned03' (P := ehgfQuad (addA (readQuad ha) (readQuad hb))) env.c11
    env.c10 env.c8 env.c60 env.c6 env.c5 hv181 hv183 hv186 hv187 hv188 hv189 hv190 hv191
  have g14 := denote_foldSigned14' (P := ehgfQuad (addA (readQuad ha) (readQuad hb))) env.c11
    env.c10 env.c9 env.c6 env.c4 hv181 hv182 hv184 hv192 hv193 hv194
  have g25 := denote_foldSigned25 (P := ehgfQuad (addA (readQuad ha) (readQuad hb))) env.c10
    env.c9 env.c4 env.c3 hv182 hv183 hv185 hv195 hv196 hv197
  clear hv181 hv182 hv183 hv184 hv185 hv186 hv187 hv188 hv189 hv190 hv192 hv193 hv195 hv196
  subst g03 g14 g25
  -- the permutes and the last product
  denote_step_reduce v 203 only [simp_spine]
  have p03 := denote_permEGGE hv198
  have p14 := denote_permEGGE hv199
  have p25 := denote_permEGGE hv200
  have q03 := denote_permFHFH hv201
  have q14 := denote_permFHFH hv202
  have q25 := denote_permFHFH hv203
  clear hv198 hv199 hv200 hv201 hv202 hv203
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
