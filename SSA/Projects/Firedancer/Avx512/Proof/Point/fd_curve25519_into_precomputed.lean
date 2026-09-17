/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_curve25519_into_precomputed
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_curve25519_into_precomputed.Model
public import SSA.Projects.Firedancer.Avx512.Proof.Point.Ge.Frame
public import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_neg

/-!
# `fd_curve25519_into_precomputed` conforms (AVX-512)

One block: `r`'s three vectors, the lane sub/add and signed fold, the multiply by
`(1, 1, 1, 2d)` through slots 0-2, the unsigned fold, the three stores into `r`.
The arithmetic is `IntoPre.intoPre` (`fd_curve25519_into_precomputed/Model.lean`).
-/

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

open IntoPre Ge in
theorem fd_curve25519_into_precomputed_conforms (r : Pointer) (s : GlobalState) (hs : s.WF)
    (hr : IsQuadPtr s.mem r) :
    fd_curve25519_into_precomputed_spec r s hr := by
  simp only [fd_curve25519_into_precomputed_spec, Cfg.denote]
  intro h03 h14 h25
  refine ⟨intoPre (readQuad hr), run_runFunction' _ ?_, ?_⟩
  denote_step_reduce v 60 [LLVM.const?, LLVM.Ty.poison] fold

  -- `%0 … %60`: `(1, 1, 1, 2d)`, the masks and the folds' constants
  replace hv2 : v2 = c1112d.v03.map PoisonOr.value := by denote_dense hv2
  replace hv1 : v1 = c1112d.v14.map PoisonOr.value := by denote_dense hv1
  replace hv0 : v0 = c1112d.v25.map PoisonOr.value := by denote_dense hv0
  replace hv33 : v33 = pmaskE 8796093022189#64 8796093022207#64 := by
    simp only [hv33]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv42 : v42 = pmaskE 8796093022207#64 8796093022207#64 := by
    simp only [hv42]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv51 : v51 = pmaskE 8796093022207#64 1099511627775#64 := by
    simp only [hv51]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, pmaskE]
  replace hv60 : v60 = quadMul19 := by
    simp only [hv60]
    apply Vector.ext; intro i hi
    interval_cases i <;> simp [LLVM.Ty.insertelement, quadMul19]
  replace hv11 : v11 = toBitVecValue 64 nbias03 := by simp only [nbias03]; denote_dense hv11
  replace hv10 : v10 = toBitVecValue 64 nbias := by simp only [nbias]; denote_dense hv10
  replace hv9 : v9 = toBitVecValue 64 quadShift43 := by simp only [quadShift43]; denote_dense hv9
  replace hv8 : v8 = toBitVecValue 64 quadShift48 := by simp only [quadShift48]; denote_dense hv8
  replace hv6 : v6 = toBitVecValue 64 quadMask43 := by simp only [quadMask43]; denote_dense hv6
  replace hv5 : v5 = toBitVecValue 64 bias03 := by simp only [bias03]; denote_dense hv5
  replace hv4 : v4 = toBitVecValue 64 bias := by simp only [bias]; denote_dense hv4
  replace hv3 : v3 = toBitVecValue 64 quadMask48 := by simp only [quadMask48]; denote_dense hv3
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv8 hv9 hv10 hv11 hv33 hv42 hv51 hv60
  denote_clear v 7 59
  refine name_of (s.allocaChain cw 3) fun sA hsA => ?_
  have hF0 : Frame 3 s s.mem sA := hsA ▸ frame_allocaChain hs 3
  peel_alloca_chain s, cw, 3
  simp only [slot_eq]
  rw [← hsA]

  -- `%64 … %71`: `r`'s vectors, each permuted
  have hrlt := lt_nextFreeBlock_of_fits hs hr.1
  have hlr : sA.mem.live? r.id = s.mem.live? r.id := hF0.below r.id hrlt
  have rq := readVec_quad hr hlr
  have hfr : Fits sA.mem r (3 * 8 * 64) := fits_of_live?_eq hlr hr.1
  have hoff : ∀ o : Nat, o ≤ 128 → (r.withOffset (BitVec.ofNat 64 o)).offset.toNat + 64 ≤ 2 ^ 64 :=
    fun o ho => by
      have := hr.2
      simp only [Pointer.withOffset, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hp0 : IsVecPtr sA.mem r := ⟨Fits.mono hfr (by omega), by have := hr.2; omega⟩
  peel_load_vec (readQuad hr).v03, r, hp0, (rq.1 hp0), sA
  denote_step_all v 65
  peel_gep 64 with r, hfr, sA as rField
  have hp64 : IsVecPtr sA.mem (r.withOffset 64) :=
    ⟨Fits.mono (remainingFits sA.mem r hfr 64 (by decide)) (by decide), hoff 64 (by omega)⟩
  peel_load_vec (readQuad hr).v14, (r.withOffset 64), hp64, (rq.2.1 hp64), sA
  denote_step_all v 68
  peel_gep 128 with r, hfr, sA as rField25
  have hp128 : IsVecPtr sA.mem (r.withOffset 128) :=
    ⟨Fits.mono (remainingFits sA.mem r hfr 128 (by decide)) (by decide), hoff 128 (by omega)⟩
  peel_load_vec (readQuad hr).v25, (r.withOffset 128), hp128, (rq.2.2 hp128), sA

  -- `%72 … %86`: `(Y-X, Y+X, Z, T)`; `%87 … %103`: the signed fold
  denote_step_all v 103
  denote_eval v 65 103
  have t03 := denote_ip rfl hv65 hv72 hv73 hv74 hv81 hv82
  have t14 := denote_ip rfl hv68 hv75 hv76 hv77 hv83 hv84
  have t25 := denote_ip rfl hv71 hv78 hv79 hv80 hv85 hv86
  clear hv65 hv68 hv71 hv72 hv73 hv74 hv75 hv76 hv77 hv78 hv79 hv80 hv81 hv83 hv85
  subst t03 t14 t25
  have f03 := denote_foldSigned03 (P := ipQuad (readQuad hr)) rfl rfl rfl rfl rfl rfl
    hv87 hv89 hv92 hv93 hv94 hv95 hv96 hv97
  have f14 := denote_foldSigned14 (P := ipQuad (readQuad hr)) rfl rfl rfl rfl rfl
    hv87 hv88 hv90 hv98 hv99 hv100
  have f25 := denote_foldSigned25 (P := ipQuad (readQuad hr)) rfl rfl rfl rfl
    hv88 hv89 hv91 hv101 hv102 hv103
  clear hv87 hv88 hv89 hv90 hv91 hv92 hv93 hv94 hv95 hv96 hv98 hv99 hv101 hv102
  subst f03 f14 f25

  -- the multiply by `(1, 1, 1, 2d)` into slots 0-2
  iterate 3 peel_lifetime
  refine mul_step hF0 (ipF (readQuad hr)) c1112d (u47s (u44_ipF ⟨h03, h14, h25⟩)) (u47s u44_c1112d)
    (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) fun u1 hrun1 hF1 hs0 hs1 hs2 hr0 hr1 hr2 => ?_
  rw [BlockCom.run_bind_denote_call_cfg_of_nil (argTys := [SLLVM.Ty.ptr, SLLVM.Ty.ptr,
      SLLVM.Ty.ptr, V8, V8, V8, V8, V8, V8])
    (argVals := [c1112d.v25.map PoisonOr.value, c1112d.v14.map PoisonOr.value,
      c1112d.v03.map PoisonOr.value, (ipF (readQuad hr)).v25.map PoisonOr.value,
      (ipF (readQuad hr)).v14.map PoisonOr.value, (ipF (readQuad hr)).v03.map PoisonOr.value,
      PoisonOr.value (slot s 2), PoisonOr.value (slot s 1), PoisonOr.value (slot s 0)]ₕ)
    (by simp only [simp_spine]; rfl) hrun1]
  peel_load_vec (quadMulResult (ipF (readQuad hr)) c1112d).v03, (slot s 0), hs0, hr0, u1
  peel_load_vec (quadMulResult (ipF (readQuad hr)) c1112d).v14, (slot s 1), hs1, hr1, u1
  peel_load_vec (quadMulResult (ipF (readQuad hr)) c1112d).v25, (slot s 2), hs2, hr2, u1
  iterate 3 peel_lifetime

  -- `FD_R43X6_QUAD_FOLD_UNSIGNED` and the stores into `r`
  have hI : foldQuad (quadMulResult (ipF (readQuad hr)) c1112d) = intoPre (readQuad hr) := rfl
  have hlr1 : u1.mem.live? r.id = s.mem.live? r.id := hF1.below r.id hrlt
  have g0 : Fits u1.mem r 512 := fits_of_live?_eq hlr1 (fits_field hr).1
  have g64 : Fits u1.mem (r.withOffset 64) 512 :=
    fits_of_live?_eq (p := r.withOffset 64) hlr1 (fits_field hr).2.1
  have g128 : Fits u1.mem (r.withOffset 128) 512 :=
    fits_of_live?_eq (p := r.withOffset 128) hlr1 (fits_field hr).2.2
  denote_step_all v 113
  denote_eval v 107 113
  have o03 := denote_foldU03 rfl rfl rfl hv109 hv110 hv111 hv112 hv113
  clear hv109 hv110 hv111 hv112 hv113
  rw [hI] at o03
  subst o03
  refine name_of ({ u1 with mem := u1.mem.splice r (vecBV (intoPre (readQuad hr)).v03) })
    fun u2 hu2 => ?_
  peel_store (intoPre (readQuad hr)).v03, r, g0, u1 as u2 := hu2
  denote_step_all v 115
  denote_eval v 114 115
  have o14 := denote_foldU14 rfl rfl hv107 hv114 hv115
  clear hv107 hv114 hv115
  rw [hI] at o14
  subst o14
  refine name_of
    ({ u2 with mem := u2.mem.splice rField (vecBV (intoPre (readQuad hr)).v14) }) fun u3 hu3 => ?_
  have g64' : Fits u2.mem rField 512 := by rw [hu2]; exact fits_splice g64
  peel_store (intoPre (readQuad hr)).v14, rField, g64', u2 as u3 := hu3
  denote_step_all v 117
  denote_eval v 116 117
  have o25 := denote_foldU25 rfl rfl hv108 hv116 hv117
  clear hv108 hv116 hv117
  rw [hI] at o25
  subst o25
  refine name_of
    ({ u3 with mem := u3.mem.splice rField25 (vecBV (intoPre (readQuad hr)).v25) })
    fun u4 hu4 => ?_
  have g128' : Fits u3.mem rField25 512 := by rw [hu3, hu2]; exact fits_splice (fits_splice g128)
  peel_store (intoPre (readQuad hr)).v25, rField25, g128', u3 as u4 := hu4

  -- `return`, in `u4`
  refine ⟨u4, by simp_return, ?_⟩
  have hF4 : Frame 3 s (s.mem.writeQuad r (intoPre (readQuad hr))) u4 := by
    rw [hu4, hu3, hu2]
    exact ((hF1.splice r _).splice (r.withOffset 64) _).splice (r.withOffset 128) _
  exact popFrame_equiv hs hrlt hF4 (fun _ hne => live?_writeQuad_ne (Ne.symm hne)) rfl

  /- The region has returned: the point and the bounds. -/
  have hu := u44_intoPre ⟨h03, h14, h25⟩
  exact ⟨ofSlots_intoPre ⟨h03, h14, h25⟩, hu.1, hu.2.1, hu.2.2, PointNeg.foldQuad_negBounds _ 3⟩
