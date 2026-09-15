/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln.Lanes
import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Frame

/-!
# `fd_ed25519_partial_dbl` conforms (AVX-512)

One block: `FD_R43X6_GE_DBL` through six slots, then three stores into `r`. The
lane lemmas and the model, `PointDbln.geDbl`, are `fd_ed25519_point_dbln`'s.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

open PointDbln Ge in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem fd_ed25519_partial_dbl_conforms (r a : Pointer) (s : GlobalState) (hs : s.WF)
    (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a) :
    fd_ed25519_partial_dbl_spec r a s hr ha := by
  simp only [fd_ed25519_partial_dbl_spec, Cfg.denote]
  intro h03 h14 h25
  refine run_runFunction' _ ?_
  have hu : QuadU44 (readQuad ha) := ⟨h03, h14, h25⟩
  denote_step_reduce v 85 [LLVM.const?, LLVM.Ty.poison] fold

  -- `%0 … %85`: the masks and the folds' constants
  replace hv18 : v18 = toBitVecValue 64 dblShift := by simp only [dblShift]; denote_dense hv18
  replace hv31 : v31 = pmaskG 8796093022189#64 8796093022207#64 := by
    simp only [hv31]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskG]
  replace hv40 : v40 = pmaskG 8796093022207#64 8796093022207#64 := by
    simp only [hv40]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskG]
  replace hv49 : v49 = pmaskG 8796093022207#64 1099511627775#64 := by
    simp only [hv49]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskG]
  replace hv58 : v58 = pmaskE 8796093022189#64 8796093022207#64 := by
    simp only [hv58]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv67 : v67 = pmaskE 8796093022207#64 8796093022207#64 := by
    simp only [hv67]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv76 : v76 = pmaskE 8796093022207#64 1099511627775#64 := by
    simp only [hv76]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv85 : v85 = quadMul19 := by
    simp only [hv85]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]
  replace hv8 : v8 = toBitVecValue 64 nbias03 := by simp only [nbias03]; denote_dense hv8
  replace hv7 : v7 = toBitVecValue 64 nbias := by simp only [nbias]; denote_dense hv7
  replace hv6 : v6 = toBitVecValue 64 quadShift43 := by simp only [quadShift43]; denote_dense hv6
  replace hv5 : v5 = toBitVecValue 64 quadShift48 := by simp only [quadShift48]; denote_dense hv5
  replace hv3 : v3 = toBitVecValue 64 quadMask43 := by simp only [quadMask43]; denote_dense hv3
  replace hv2 : v2 = toBitVecValue 64 bias03 := by simp only [bias03]; denote_dense hv2
  replace hv1 : v1 = toBitVecValue 64 bias := by simp only [bias]; denote_dense hv1
  replace hv0 : v0 = toBitVecValue 64 quadMask48 := by simp only [quadMask48]; denote_dense hv0
  subst hv0 hv1 hv2 hv3 hv5 hv6 hv7 hv8 hv18 hv21 hv31 hv40 hv49 hv58 hv67 hv76 hv85
  denote_clear v 4 84

  -- `%86 … %91`: the slots
  refine name_of (s.allocaChain cw 6) fun sA hsA => ?_
  have hF0 : Frame 6 s s.mem sA := hsA ▸ frame_allocaChain hs 6
  peel_alloca_chain s, cw, 6
  simp only [slot_eq]
  rw [← hsA]

  -- `%92 … %105`: `a`'s vectors, `(X+Y, Y, Z, X)`
  have hla : sA.mem.live? a.id = s.mem.live? a.id :=
    hF0.below a.id (lt_nextFreeBlock_of_fits hs ha.1)
  have hra := readVec_quad ha hla
  have hfa : Fits sA.mem a (3 * 8 * 64) := fits_of_live?_eq hla ha.1
  have hpa : IsVecPtr sA.mem a := ⟨Fits.mono hfa (by omega), by have := ha.2; omega⟩
  peel_load_vec (readQuad ha).v03, a, hpa, (hra.1 hpa), sA
  denote_step_all v 93
  have hoff : ∀ o : Nat, o ≤ 128 → (a.withOffset (BitVec.ofNat 64 o)).offset.toNat + 64 ≤ 2 ^ 64 :=
    fun o ho => by
      have := ha.2
      simp only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  peel_gep 64 with a, hfa, sA as aField
  have hpa64 : IsVecPtr sA.mem (a.withOffset 64) :=
    ⟨Fits.mono (remainingFits sA.mem a hfa 64 (by decide)) (by decide), hoff 64 (by omega)⟩
  peel_load_vec (readQuad ha).v14, (a.withOffset 64), hpa64, (hra.2.1 hpa64), sA
  denote_step_all v 96
  peel_gep 128 with a, hfa, sA as aField25
  have hpa128 : IsVecPtr sA.mem (a.withOffset 128) :=
    ⟨Fits.mono (remainingFits sA.mem a hfa 128 (by decide)) (by decide), hoff 128 (by omega)⟩
  peel_load_vec (readQuad ha).v25, (a.withOffset 128), hpa128, (hra.2.2 hpa128), sA
  denote_step_all v 105
  denote_eval v 93 105
  have e03 := denote_addXY hu.1 hv93 hv100 hv101
  have e14 := denote_addXY hu.2.1 hv96 hv102 hv103
  have e25 := denote_addXY hu.2.2 hv99 hv104 hv105
  denote_clear v 93 105
  subst e03 e14 e25
  iterate 3 peel_lifetime

  -- `%106 … %170`: the square into slots 0-2, then `(E, G, F, H)` folded and permuted
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
  denote_step_all v 170
  denote_eval v 109 170
  have p03 := denote_egfh rfl rfl rfl hv109 hv112 hv115 hv118 hv119 hv124 hv125 hv126 hv133
    hv134 hv139 hv140 hv141
  have p14 := denote_egfh rfl rfl rfl hv110 hv113 hv116 hv120 hv121 hv127 hv128 hv129 hv135
    hv136 hv142 hv143 hv144
  have p25 := denote_egfh rfl rfl rfl hv111 hv114 hv117 hv122 hv123 hv130 hv131 hv132 hv137
    hv138 hv145 hv146 hv147
  denote_clear v 109 147
  subst p03 p14 p25
  have r03 := denote_foldSigned03 (P := egfhQuad (quadSqrResult (dblTa (readQuad ha)))) rfl rfl
    rfl rfl rfl rfl hv148 hv150 hv153 hv154 hv155 hv156 hv157 hv158
  have r14 := denote_foldSigned14 (P := egfhQuad (quadSqrResult (dblTa (readQuad ha)))) rfl rfl
    rfl rfl rfl hv148 hv149 hv151 hv159 hv160 hv161
  have r25 := denote_foldSigned25 (P := egfhQuad (quadSqrResult (dblTa (readQuad ha)))) rfl rfl
    rfl rfl hv149 hv150 hv152 hv162 hv163 hv164
  denote_clear v 148 164
  subst r03 r14 r25
  have g03 := denote_permGE hv165
  have g14 := denote_permGE hv166
  have g25 := denote_permGE hv167
  have f03 := denote_permFH hv168
  have f14 := denote_permFH hv169
  have f25 := denote_permFH hv170
  denote_clear v 165 170
  subst g03 g14 g25 f03 f14 f25
  iterate 3 peel_lifetime

  -- `%171 … %173`: the product into slots 3-5
  have hR := u44_dblR hu
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

  -- `%174 … %186`: `FD_R43X6_QUAD_FOLD_UNSIGNED` and the stores into `r`
  have hrlt := lt_nextFreeBlock_of_fits hs hr.1
  have hlr : u2.mem.live? r.id = s.mem.live? r.id := hF2.below r.id hrlt
  denote_step_all v 180
  denote_eval v 174 180
  have o03 : v180 = (geDbl (readQuad ha)).v03.map PoisonOr.value :=
    denote_foldU03 rfl rfl rfl hv176 hv177 hv178 hv179 hv180
  subst o03
  refine name_of ({ u2 with mem := u2.mem.splice r (vecBV (geDbl (readQuad ha)).v03) })
    fun u3 hu3 => ?_
  have g0 : Fits u2.mem r 512 := fits_of_live?_eq hlr (fits_field hr).1
  peel_store (geDbl (readQuad ha)).v03, r, g0, u2 as u3 := hu3
  denote_step_all v 182
  denote_eval v 181 182
  have o14 : v182 = (geDbl (readQuad ha)).v14.map PoisonOr.value :=
    denote_foldU14 rfl rfl hv174 hv181 hv182
  subst o14
  have hfr3 : Fits u3.mem r (3 * 8 * 64) := by
    rw [hu3]; exact fits_splice (fits_of_live?_eq hlr hr.1)
  peel_gep 64 with r, hfr3, u3 as rField
  have g64 : Fits u3.mem rField 512 :=
    Fits.mono (remainingFits u3.mem r hfr3 64 (by decide)) (by decide)
  refine name_of ({ u3 with mem := u3.mem.splice rField (vecBV (geDbl (readQuad ha)).v14) })
    fun u4 hu4 => ?_
  peel_store (geDbl (readQuad ha)).v14, rField, g64, u3 as u4 := hu4
  denote_step_all v 185
  denote_eval v 184 185
  have o25 : v185 = (geDbl (readQuad ha)).v25.map PoisonOr.value :=
    denote_foldU25 rfl rfl hv175 hv184 hv185
  subst o25
  have hfr4 : Fits u4.mem r (3 * 8 * 64) := by rw [hu4]; exact fits_splice hfr3
  peel_gep 128 with r, hfr4, u4 as rField25
  have g128 : Fits u4.mem rField25 512 :=
    Fits.mono (remainingFits u4.mem r hfr4 128 (by decide)) (by decide)
  refine name_of ({ u4 with mem := u4.mem.splice rField25 (vecBV (geDbl (readQuad ha)).v25) })
    fun u5 hu5 => ?_
  peel_store (geDbl (readQuad ha)).v25, rField25, g128, u4 as u5 := hu5

  -- `return %arg0`, in `u5`
  refine ⟨u5, by simp_return, ?_⟩
  have hF5 : Frame 6 s (s.mem.writeQuad r (geDbl (readQuad ha))) u5 := by
    rw [hu5, hu4, hu3]
    exact ((hF2.splice r _).splice (r.withOffset 64) _).splice (r.withOffset 128) _
  have hq := u44_geDbl hu
  exact ⟨geDbl (readQuad ha),
    popFrame_equiv hs hrlt hF5 (fun _ hne => live?_writeQuad_ne (Ne.symm hne)) rfl,
    toPoint_geDbl hu, hq.1, hq.2.1, hq.2.2⟩

end Firedancer.Avx512
