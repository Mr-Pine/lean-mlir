import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryAddback

/-! The actual 23-instruction addback window. Mask and carry bounds discharge
every `nsw`/`nuw` flag, including the two signed top-word additions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Agave.Ed25519.Verifier.Execution.ScalarWide

open LeanMLIR.RIR
open Subtraction
open ScalarMontgomeryMul (zero_sub_byte and_limb_bound addback_shift_bound)

def wrapperAddbackEnv (E : Env program.Γ) (low : Fin 4 → BitVec 64)
    (top : BitVec 64) (byte : BitVec 8) : Env program.Γ :=
  let widened := byte.setWidth 64
  let mask := (0 : BitVec 64) - widened
  let t0 := (mask &&& 671914833335277#64) + low 0
  let m1 := (mask &&& 3916664325105025#64) + low 1
  let t1 := m1 + (t0 >>> 52)
  let m2 := (mask &&& 1367801#64) + low 2
  let t2 := m2 + (t1 >>> 52)
  let t3 := (t2 >>> 52) + low 3
  let m4 := top + (mask &&& 17592186044416#64)
  let t4 := m4 + (t3 >>> 52)
  E[%332 := .value widened, %333 := .value mask,
    %334 := .value (mask &&& 671914833335277#64), %335 := .value t0,
    %336 := .value (t0 &&& 4503599627370495#64),
    %337 := .value (mask &&& 3916664325105025#64), %338 := .value (t0 >>> 52),
    %339 := .value m1, %340 := .value t1,
    %341 := .value (t1 &&& 4503599627370495#64),
    %342 := .value (mask &&& 1367801#64), %343 := .value (t1 >>> 52),
    %344 := .value m2, %345 := .value t2,
    %346 := .value (t2 &&& 4503599627370495#64), %347 := .value (t2 >>> 52),
    %348 := .value t3, %349 := .value (t3 &&& 4503599627370495#64),
    %350 := .value (mask &&& 17592186044416#64), %351 := .value (t3 >>> 52),
    %352 := .value m4, %353 := .value t4, %354 := .value (t4 &&& 4503599627370495#64)]

/-- Run all actual addback instructions with their original poison flags. -/
theorem wrapper_addback_run (p : Primitives) (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (low : Fin 4 → BitVec 64) (top : BitVec 64) (byte : BitVec 8)
    (hbounded : ∀ i, (low i).toNat < 2 ^ 52)
    (htopBound : -(2 ^ 52 : Int) ≤ top.toInt ∧ top.toInt < 2 ^ 52)
    (hl0 : E.read (%314) = .value (low 0))
    (hl1 : E.read (%318) = .value (low 1))
    (hl2 : E.read (%322) = .value (low 2))
    (hl3 : E.read (%325) = .value (low 3))
    (htop : E.read (%328) = .value top)
    (hbyte : E.read (%331) = .value byte)
    (hmask : E.read (%38) = .value 4503599627370495#64)
    (hzero : E.read (%46) = .value 0#64)
    (hk0 : E.read (%47) = .value 671914833335277#64)
    (hk1 : E.read (%48) = .value 3916664325105025#64)
    (hshift : E.read (%32) = .value 52#64)
    (hk2 : E.read (%49) = .value 1367801#64)
    (hk4 : E.read (%50) = .value 17592186044416#64)
    : List.foldlM Instr.run E (((program.entry p g).body.drop 377).take 23) state =
      .value (wrapperAddbackEnv E low top byte, state) := by
  let widened := byte.setWidth 64
  let mask := (0 : BitVec 64) - widened
  let t0 := (mask &&& 671914833335277#64) + low 0
  let m1 := (mask &&& 3916664325105025#64) + low 1
  let t1 := m1 + (t0 >>> 52)
  let m2 := (mask &&& 1367801#64) + low 2
  let t2 := m2 + (t1 >>> 52)
  let t3 := (t2 >>> 52) + low 3
  let m4 := top + (mask &&& 17592186044416#64)
  let t4 := m4 + (t3 >>> 52)
  have hb0 := and_limb_bound mask 671914833335277#64 (by decide)
  have hb1 := and_limb_bound mask 3916664325105025#64 (by decide)
  have hb2 := and_limb_bound mask 1367801#64 (by decide)
  have h0 : (mask &&& 671914833335277#64).toNat + (low 0).toNat < 2 ^ 53 := by
    have hl := hbounded 0
    norm_num at hl hb0 ⊢
    omega
  have f0 := addback_add64 (mask &&& 671914833335277#64) (low 0) h0
  have b0 : t0.toNat < 2 ^ 53 := by rw [f0.2]; exact h0
  have c0 := addback_shift_bound t0 b0
  have h10 : (mask &&& 3916664325105025#64).toNat + (low 1).toNat < 2 ^ 53 := by
    have hl := hbounded 1
    norm_num at hl hb1 ⊢
    omega
  have f10 := addback_add64 (mask &&& 3916664325105025#64) (low 1) h10
  have h1 : m1.toNat + (t0 >>> 52).toNat < 2 ^ 53 := by
    rw [f10.2]
    have hl := hbounded 1
    norm_num at c0 hb1 hl ⊢
    omega
  have f1 := addback_add64 m1 (t0 >>> 52) h1
  have b1 : t1.toNat < 2 ^ 53 := by rw [f1.2]; exact h1
  have c1 := addback_shift_bound t1 b1
  have h20 : (mask &&& 1367801#64).toNat + (low 2).toNat < 2 ^ 53 := by
    have hl := hbounded 2
    norm_num at hl hb2 ⊢
    omega
  have f20 := addback_add64 (mask &&& 1367801#64) (low 2) h20
  have h2 : m2.toNat + (t1 >>> 52).toNat < 2 ^ 53 := by
    rw [f20.2]
    have hl := hbounded 2
    norm_num at hl hb2 c1 ⊢
    omega
  have f2 := addback_add64 m2 (t1 >>> 52) h2
  have b2 : t2.toNat < 2 ^ 53 := by rw [f2.2]; exact h2
  have c2 := addback_shift_bound t2 b2
  have h3 : (t2 >>> 52).toNat + (low 3).toNat < 2 ^ 53 := by
    have hl := hbounded 3
    norm_num at hl c2 ⊢
    omega
  have f3 := addback_add64 (t2 >>> 52) (low 3) h3
  have b3 : t3.toNat < 2 ^ 53 := by rw [f3.2]; exact h3
  have c3 := addback_shift_bound t3 b3
  have hb4 := and_limb_bound mask 17592186044416#64 (by decide)
  have hi4 : (mask &&& 17592186044416#64).toInt =
      ((mask &&& 17592186044416#64).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hb4 ⊢; omega)
  have f4 := signed_add64 top (mask &&& 17592186044416#64)
    (by rw [hi4]; norm_num at htopBound hb4 ⊢; omega)
    (by rw [hi4]; norm_num at htopBound hb4 ⊢; omega)
  have hic : (t3 >>> 52).toInt = ((t3 >>> 52).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at c3 ⊢; omega)
  have f5 := signed_add64 m4 (t3 >>> 52)
    (by rw [f4.2, hi4, hic]; norm_num only [Nat.reducePow, Int.reducePow] at htopBound hb4 c3 ⊢; omega)
    (by rw [f4.2, hi4, hic]; norm_num only [Nat.reducePow, Int.reducePow] at htopBound hb4 c3 ⊢; omega)
  have fs := zero_sub_byte byte
  have hadd (a b : BitVec 64) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [widened, mask, t0, m1, t1, m2, t2, t3, m4] at f0 f10 f1 f20 f2 f3 f4 f5
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    wrapperAddbackEnv, widened, mask, t0, m1, t1, m2, t2, t3, m4, t4,
    hl0, hl1, hl2, hl3, htop, hbyte, hmask, hzero, hk0, hk1, hk2, hk4, hshift,
    f0.1, f10.1, f1.1, f20.1, f2.1, f3.1, f4.1, f5.1, fs,
    Operation.zext, Operation.and, Operation.lshr, hadd,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

/-- The wrapper differs in addition association only; all five output registers
are the shared algebraic conditional-addback words. -/
theorem wrapperAddbackEnv_words (E : Env program.Γ) (d : Subtraction.Limbs) :
    let low : Fin 4 → BitVec 64 := fun i => d ⟨i.val, by omega⟩ &&& 4503599627370495#64
    let result := wrapperAddbackEnv E low (d 4) (borrowByte d)
    result.read (%336) = .value (addback d 0) ∧
    result.read (%341) = .value (addback d 1) ∧
    result.read (%346) = .value (addback d 2) ∧
    result.read (%349) = .value (addback d 3) ∧
    result.read (%354) = .value (addback d 4) := by
  simp [wrapperAddbackEnv, addback, mlir_env,
    BitVec.add_assoc, BitVec.add_comm, add_left_comm]

end Agave.Ed25519.Verifier.Execution.ScalarWide
