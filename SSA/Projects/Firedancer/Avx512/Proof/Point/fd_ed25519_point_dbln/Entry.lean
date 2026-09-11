/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Blocks

/-!
# `fd_ed25519_point_dbln`'s entry block

`^bb0`: the constants, the twelve slots, `a`'s three vectors, `FD_R43X6_GE_DBL`
through slots 0-5, the three stores into `r`, and the branch on `n > 1`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace PointDbln
open Ge

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem bb0_run (r a : Pointer) (n : BitVec 32) (s : GlobalState) (hs : s.WF)
    (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) (hu : QuadU44 (readQuad ha)) :
    ∃ (W : fd_ed25519_point_dbln.Γout.Valuation) (u : GlobalState),
      EntryEnv W s r n ∧ Frame 12 s (s.mem.writeQuad r (geDbl (readQuad ha))) u
      ∧ StateT.run (fd_ed25519_point_dbln.denote
          (Ctxt.Valuation.ofHVector [.value n, .value a, .value r]ₕ)) s
        = StateT.run (fd_ed25519_point_dbln.blocks.run W
            (if BitVec.ofBool (n >ₛ 1#32) = 1 then hdr3 (geDbl (readQuad ha)) 1#8 else hdr2)) u := by
  simp only [Cfg.denote]
  denote_step_reduce v 86 [LLVM.const?, LLVM.Ty.poison] fold
  replace hv19 : v19 = toBitVecValue 64 dblShift := by simp only [dblShift]; denote_dense hv19
  replace hv32 : v32 = pmaskG 8796093022189#64 8796093022207#64 := by
    simp only [hv32]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskG]
  replace hv41 : v41 = pmaskG 8796093022207#64 8796093022207#64 := by
    simp only [hv41]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskG]
  replace hv50 : v50 = pmaskG 8796093022207#64 1099511627775#64 := by
    simp only [hv50]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskG]
  replace hv59 : v59 = pmaskE 8796093022189#64 8796093022207#64 := by
    simp only [hv59]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv68 : v68 = pmaskE 8796093022207#64 8796093022207#64 := by
    simp only [hv68]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv77 : v77 = pmaskE 8796093022207#64 1099511627775#64 := by
    simp only [hv77]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv86 : v86 = quadMul19 := by
    simp only [hv86]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]
  replace hv9 : v9 = toBitVecValue 64 nbias03 := by simp only [nbias03]; denote_dense hv9
  replace hv8 : v8 = toBitVecValue 64 nbias := by simp only [nbias]; denote_dense hv8
  replace hv7 : v7 = toBitVecValue 64 quadShift43 := by simp only [quadShift43]; denote_dense hv7
  replace hv6 : v6 = toBitVecValue 64 quadShift48 := by simp only [quadShift48]; denote_dense hv6
  replace hv4 : v4 = toBitVecValue 64 quadMask43 := by simp only [quadMask43]; denote_dense hv4
  replace hv3 : v3 = toBitVecValue 64 bias03 := by simp only [bias03]; denote_dense hv3
  replace hv2 : v2 = toBitVecValue 64 bias := by simp only [bias]; denote_dense hv2
  replace hv1 : v1 = toBitVecValue 64 quadMask48 := by simp only [quadMask48]; denote_dense hv1
  subst hv0 hv1 hv2 hv3 hv4 hv6 hv7 hv8 hv9 hv19 hv21 hv32 hv41 hv50 hv59 hv68 hv77 hv86
  denote_clear v 5 85
  obtain ⟨sA, hsA⟩ : ∃ t, t = s.allocaChain cw 12 := ⟨_, rfl⟩
  have hF0 : Frame 12 s s.mem sA := hsA ▸ frame_allocaChain hs 12
  peel_alloca_chain s, cw, 12
  simp only [slot_eq]
  rw [← hsA]
  -- `a`'s vectors
  have hla : sA.mem.live? a.id = s.mem.live? a.id := hF0.below a.id (lt_nextFreeBlock_of_fits hs ha.1)
  obtain ⟨ra03, ra14, ra25⟩ := readVec_quad ha hla
  have hfa : Fits sA.mem a (3 * 8 * 64) := fits_of_live?_eq hla ha.1
  have hpa : IsVecPtr sA.mem a := ⟨Fits.mono hfa (by omega), by have := ha.2; omega⟩
  peel_load_vec (readQuad ha).v03, a, hpa, (ra03 hpa), sA
  denote_step_all v 100
  have hoff : ∀ o : Nat, o ≤ 128 → (a.withOffset (BitVec.ofNat 64 o)).offset.toNat + 64 ≤ 2 ^ 64 :=
    fun o ho => by
      have := ha.2
      simp only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  peel_gep 64 with a, hfa, sA as aField
  have hpa64 : IsVecPtr sA.mem (a.withOffset 64) :=
    ⟨Fits.mono (remainingFits sA.mem a hfa 64 (by decide)) (by decide), hoff 64 (by omega)⟩
  peel_load_vec (readQuad ha).v14, (a.withOffset 64), hpa64, (ra14 hpa64), sA
  denote_step_all v 103
  peel_gep 128 with a, hfa, sA as aField25
  have hpa128 : IsVecPtr sA.mem (a.withOffset 128) :=
    ⟨Fits.mono (remainingFits sA.mem a hfa 128 (by decide)) (by decide), hoff 128 (by omega)⟩
  peel_load_vec (readQuad ha).v25, (a.withOffset 128), hpa128, (ra25 hpa128), sA
  denote_step_all v 112
  denote_eval v 100 112
  have e03 := denote_addXY hu.1 hv100 hv107 hv108
  have e14 := denote_addXY hu.2.1 hv103 hv109 hv110
  have e25 := denote_addXY hu.2.2 hv106 hv111 hv112
  clear hv100 hv103 hv106 hv107 hv108 hv109 hv110 hv111 hv112
  subst e03 e14 e25
  iterate 3 peel_lifetime
  refine sqr_step hF0 (dblTa (readQuad ha)) (u47_dblTa hu) (i := 0) (j := 1) (k := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    fun u1 hrun1 hF1 hp0 hp1 hp2 hr0 hr1 hr2 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8])
    (argVals := [(dblTa (readQuad ha)).v25.map PoisonOr.value,
      (dblTa (readQuad ha)).v14.map PoisonOr.value, (dblTa (readQuad ha)).v03.map PoisonOr.value,
      PoisonOr.value (slot s 2), PoisonOr.value (slot s 1), PoisonOr.value (slot s 0)]ₕ)
    (by simp only [simp_spine]; rfl) hrun1]
  peel_load_vec (quadSqrResult (dblTa (readQuad ha))).v03, (slot s 0), hp0, hr0, u1
  peel_load_vec (quadSqrResult (dblTa (readQuad ha))).v14, (slot s 1), hp1, hr1, u1
  peel_load_vec (quadSqrResult (dblTa (readQuad ha))).v25, (slot s 2), hp2, hr2, u1
  iterate 3 peel_lifetime
  denote_step_all v 177
  denote_eval v 116 177
  have p03 := denote_egfh rfl rfl rfl hv116 hv119 hv122 hv125 hv126 hv131 hv132 hv133 hv140 hv141 hv146 hv147 hv148
  have p14 := denote_egfh rfl rfl rfl hv117 hv120 hv123 hv127 hv128 hv134 hv135 hv136 hv142 hv143 hv149 hv150 hv151
  have p25 := denote_egfh rfl rfl rfl hv118 hv121 hv124 hv129 hv130 hv137 hv138 hv139 hv144 hv145 hv152 hv153 hv154
  clear hv116 hv117 hv118 hv119 hv120 hv121 hv122 hv123 hv124 hv125 hv126 hv127 hv128 hv129 hv130 hv131 hv132 hv133 hv134 hv135 hv136 hv137 hv138 hv139 hv140 hv141 hv142 hv143 hv144 hv145 hv146 hv147 hv148 hv149 hv150 hv151 hv152 hv153 hv154
  subst p03 p14 p25
  have r03 := denote_foldSigned03 (P := egfhQuad (quadSqrResult (dblTa (readQuad ha)))) rfl rfl
    rfl rfl rfl rfl hv155 hv157 hv160 hv161 hv162 hv163 hv164 hv165
  have r14 := denote_foldSigned14 (P := egfhQuad (quadSqrResult (dblTa (readQuad ha)))) rfl rfl
    rfl rfl rfl hv155 hv156 hv158 hv166 hv167 hv168
  have r25 := denote_foldSigned25 (P := egfhQuad (quadSqrResult (dblTa (readQuad ha)))) rfl rfl
    rfl rfl hv156 hv157 hv159 hv169 hv170 hv171
  clear hv155 hv156 hv157 hv158 hv159 hv160 hv161 hv162 hv163 hv164 hv165 hv166 hv167 hv168 hv169 hv170 hv171
  subst r03 r14 r25
  have g03 := denote_permGE hv172
  have g14 := denote_permGE hv173
  have g25 := denote_permGE hv174
  have f03 := denote_permFH hv175
  have f14 := denote_permFH hv176
  have f25 := denote_permFH hv177
  clear hv172 hv173 hv174 hv175 hv176 hv177
  subst g03 g14 g25 f03 f14 f25
  have hR := u44_dblR hu
  iterate 3 peel_lifetime
  refine mul_step hF1 (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha)))
    ⟨u47_of_u44 (u44_geQuad hR).1, u47_of_u44 (u44_geQuad hR).2.1, u47_of_u44 (u44_geQuad hR).2.2⟩
    ⟨u47_of_u44 (u44_fhQuad hR).1, u47_of_u44 (u44_fhQuad hR).2.1, u47_of_u44 (u44_fhQuad hR).2.2⟩
    (i := 3) (j := 4) (k := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun u2 hrun2 hF2 hp3 hp4 hp5 hr3 hr4 hr5 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8, V8, V8, V8])
    (argVals := [(fhQuad (dblR (readQuad ha))).v25.map PoisonOr.value,
      (fhQuad (dblR (readQuad ha))).v14.map PoisonOr.value,
      (fhQuad (dblR (readQuad ha))).v03.map PoisonOr.value,
      (geQuad (dblR (readQuad ha))).v25.map PoisonOr.value,
      (geQuad (dblR (readQuad ha))).v14.map PoisonOr.value,
      (geQuad (dblR (readQuad ha))).v03.map PoisonOr.value,
      PoisonOr.value (slot s 5), PoisonOr.value (slot s 4), PoisonOr.value (slot s 3)]ₕ)
    (by simp only [simp_spine]; rfl) hrun2]
  peel_load_vec (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha)))).v03,
    (slot s 3), hp3, hr3, u2
  peel_load_vec (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha)))).v14,
    (slot s 4), hp4, hr4, u2
  peel_load_vec (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha)))).v25,
    (slot s 5), hp5, hr5, u2
  iterate 3 peel_lifetime
  -- `FD_R43X6_QUAD_FOLD_UNSIGNED` and the stores into `r`
  have hrlt := lt_nextFreeBlock_of_fits hs hr.1
  have hlr : u2.mem.live? r.id = s.mem.live? r.id := hF2.below r.id hrlt
  obtain ⟨fr0, fr64, fr128⟩ := fits_field hr
  have hF3 := hF2.splice r (vecBV (geDbl (readQuad ha)).v03)
  have hF4 := hF3.splice (r.withOffset 64) (vecBV (geDbl (readQuad ha)).v14)
  have hF5 := hF4.splice (r.withOffset 128) (vecBV (geDbl (readQuad ha)).v25)
  denote_step_all v 187
  denote_eval v 181 187
  have o03 := denote_foldU03 rfl rfl rfl hv183 hv184 hv185 hv186 hv187
  refine name_of ({ u2 with mem := u2.mem.splice r (vecBV (foldQuad (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha))))).v03) })
    fun u3 hu3 => ?_
  have g0 : Fits u2.mem r 512 := fits_of_live?_eq hlr fr0
  subst o03
  peel_store (foldQuad (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha))))).v03, r, g0, u2 as u3 := hu3
  denote_step_all v 189
  denote_eval v 188 189
  have o14 := denote_foldU14 rfl rfl hv181 hv188 hv189
  subst o14
  have hfr3 : Fits u3.mem r (3 * 8 * 64) := by
    rw [hu3]; exact fits_splice (fits_of_live?_eq hlr hr.1)
  peel_gep 64 with r, hfr3, u3 as rField
  have g64 : Fits u3.mem rField 512 :=
    Fits.mono (remainingFits u3.mem r hfr3 64 (by decide)) (by decide)
  refine name_of ({ u3 with mem := u3.mem.splice rField (vecBV (foldQuad (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha))))).v14) })
    fun u4 hu4 => ?_
  peel_store (foldQuad (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha))))).v14, rField, g64, u3 as u4 := hu4
  denote_step_all v 192
  denote_eval v 191 192
  have o25 := denote_foldU25 rfl rfl hv182 hv191 hv192
  subst o25
  have hfr4 : Fits u4.mem r (3 * 8 * 64) := by rw [hu4]; exact fits_splice hfr3
  peel_gep 128 with r, hfr4, u4 as rField25
  have g128 : Fits u4.mem rField25 512 :=
    Fits.mono (remainingFits u4.mem r hfr4 128 (by decide)) (by decide)
  refine name_of ({ u4 with mem := u4.mem.splice rField25 (vecBV (foldQuad (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha))))).v25) })
    fun u5 hu5 => ?_
  peel_store (foldQuad (quadMulResult (geQuad (dblR (readQuad ha))) (fhQuad (dblR (readQuad ha))))).v25, rField25, g128, u4 as u5 := hu5
  have hF5' : Frame 12 s (s.mem.writeQuad r (geDbl (readQuad ha))) u5 := by
    rw [hu5, hu4, hu3]; exact hF5
  denote_step_all v 194
  replace hv194 : v194 = .value (BitVec.ofBool (n >ₛ 1#32)) := by
    simp only [hv194, Expr.denoteOp1, Expr.denoteOpPure]; simp_peephole; rfl
  subst hv194
  simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_spine]
  by_cases hb : (n >ₛ 1#32) = true
  · simp only [hb, BitVec.ofBool_true, ite_true, pure_bind]
    refine ⟨?W1, u5, ?env1, hF5', ?run1⟩
    case run1 => rfl
    case env1 => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hb, BitVec.ofBool_false, pure_bind]
    refine ⟨?W2, u5, ?env2, hF5', ?run2⟩
    case run2 => rfl
    case env2 => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PointDbln

end Firedancer.Avx512
