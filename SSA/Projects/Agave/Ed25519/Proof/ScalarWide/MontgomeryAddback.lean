import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.SubtractionFlags

/-! The actual 23-instruction addback window. Mask and carry bounds discharge
every `nsw`/`nuw` flag; the final two additions retain intentional wrapping. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open ScalarWide.Subtraction

/-- Negation of a zero-extended byte is always representable as signed i64. -/
theorem zero_sub_byte (byte : BitVec 8) :
    Operation.sub { nsw := true } (.value (0#64)) (.value (byte.setWidth 64)) =
      .value (0 - byte.setWidth 64) := by
  have hb := byte.isLt
  have hi : (byte.setWidth 64).toInt = (byte.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by
      rw [BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
      norm_num at hb ⊢
      omega), BitVec.toNat_setWidth_of_le (by decide : 8 ≤ 64)]
  have hs : (0#64).ssubOverflow (byte.setWidth 64) = false := by
    simp only [BitVec.ssubOverflow, hi]
    norm_num at hb ⊢
    omega
  simp [Operation.sub, hs]

/-- AND cannot increase a literal's unsigned value. -/
theorem and_limb_bound (mask constant : BitVec 64) (h : constant.toNat < 2 ^ 52) :
    (mask &&& constant).toNat < 2 ^ 52 := by
  exact (Nat.and_le_right (n := mask.toNat) (m := constant.toNat)).trans_lt h

/-- A bounded addback word produces only a zero/one radix carry. -/
theorem addback_shift_bound (word : BitVec 64) (h : word.toNat < 2 ^ 53) :
    (word >>> 52).toNat ≤ 1 := by
  change word.toNat >>> 52 ≤ 1
  rw [Nat.shiftRight_eq_div_pow]
  norm_num at h ⊢
  omega

def addbackEnv (E : Env program.Γ) (low : Fin 4 → BitVec 64)
    (top : BitVec 64) (byte : BitVec 8) : Env program.Γ :=
  let widened := byte.setWidth 64
  let mask := (0 : BitVec 64) - widened
  let t0 := low 0 + (mask &&& 671914833335277#64)
  let m1 := (t0 >>> 52) + (mask &&& 3916664325105025#64)
  let t1 := m1 + low 1
  let m2 := low 2 + (mask &&& 1367801#64)
  let t2 := m2 + (t1 >>> 52)
  let t3 := (t2 >>> 52) + low 3
  let m4 := top + (mask &&& 17592186044416#64)
  let t4 := m4 + (t3 >>> 52)
  E[%207 := .value widened, %208 := .value mask,
    %209 := .value (mask &&& 671914833335277#64), %210 := .value t0,
    %211 := .value (t0 &&& 4503599627370495#64),
    %212 := .value (mask &&& 3916664325105025#64), %213 := .value (t0 >>> 52),
    %214 := .value m1, %215 := .value t1,
    %216 := .value (t1 &&& 4503599627370495#64),
    %217 := .value (mask &&& 1367801#64), %218 := .value (t1 >>> 52),
    %219 := .value m2, %220 := .value t2,
    %221 := .value (t2 &&& 4503599627370495#64), %222 := .value (t2 >>> 52),
    %223 := .value t3, %224 := .value (t3 &&& 4503599627370495#64),
    %225 := .value (mask &&& 17592186044416#64), %226 := .value (t3 >>> 52),
    %227 := .value m4, %228 := .value t4, %229 := .value (t4 &&& 4503599627370495#64)]

/-- Run all actual addback instructions with their original poison flags. -/
theorem addback_run (p : Primitives) (E : Env program.Γ) (state : GlobalState)
    (low : Fin 4 → BitVec 64) (top : BitVec 64) (byte : BitVec 8)
    (hbounded : ∀ i, (low i).toNat < 2 ^ 52)
    (hl0 : E.read (%189) = .value (low 0))
    (hl1 : E.read (%193) = .value (low 1))
    (hl2 : E.read (%197) = .value (low 2))
    (hl3 : E.read (%200) = .value (low 3))
    (htop : E.read (%203) = .value top)
    (hbyte : E.read (%206) = .value byte)
    (hmask : E.read (%6) = .value 4503599627370495#64)
    (hzero : E.read (%17) = .value 0#64)
    (hk0 : E.read (%18) = .value 671914833335277#64)
    (hk1 : E.read (%19) = .value 3916664325105025#64)
    (hshift : E.read (%20) = .value 52#64)
    (hk2 : E.read (%21) = .value 1367801#64)
    (hk4 : E.read (%22) = .value 17592186044416#64)
    : List.foldlM Instr.run E (((program.entry p).body.drop 227).take 23) state =
      .value (addbackEnv E low top byte, state) := by
  let widened := byte.setWidth 64
  let mask := (0 : BitVec 64) - widened
  let t0 := low 0 + (mask &&& 671914833335277#64)
  let m1 := (t0 >>> 52) + (mask &&& 3916664325105025#64)
  let t1 := m1 + low 1
  let m2 := low 2 + (mask &&& 1367801#64)
  let t2 := m2 + (t1 >>> 52)
  let t3 := (t2 >>> 52) + low 3
  let m4 := top + (mask &&& 17592186044416#64)
  let t4 := m4 + (t3 >>> 52)
  have hb0 := and_limb_bound mask 671914833335277#64 (by decide)
  have hb1 := and_limb_bound mask 3916664325105025#64 (by decide)
  have hb2 := and_limb_bound mask 1367801#64 (by decide)
  have h0 : (low 0).toNat + (mask &&& 671914833335277#64).toNat < 2 ^ 53 := by
    have hl := hbounded 0
    norm_num at hl hb0 ⊢
    omega
  have f0 := addback_add64 (low 0) (mask &&& 671914833335277#64) h0
  have b0 : t0.toNat < 2 ^ 53 := by rw [f0.2]; exact h0
  have c0 := addback_shift_bound t0 b0
  have h10 : (t0 >>> 52).toNat + (mask &&& 3916664325105025#64).toNat < 2 ^ 53 := by
    norm_num at c0 hb1 ⊢
    omega
  have f10 := addback_add64 (t0 >>> 52) (mask &&& 3916664325105025#64) h10
  have h1 : m1.toNat + (low 1).toNat < 2 ^ 53 := by
    rw [f10.2]
    have hl := hbounded 1
    norm_num at c0 hb1 hl ⊢
    omega
  have f1 := addback_add64 m1 (low 1) h1
  have b1 : t1.toNat < 2 ^ 53 := by rw [f1.2]; exact h1
  have c1 := addback_shift_bound t1 b1
  have h20 : (low 2).toNat + (mask &&& 1367801#64).toNat < 2 ^ 53 := by
    have hl := hbounded 2
    norm_num at hl hb2 ⊢
    omega
  have f20 := addback_add64 (low 2) (mask &&& 1367801#64) h20
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
  have fs := zero_sub_byte byte
  have hadd (a b : BitVec 64) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [widened, mask, t0, m1, t1, m2, t2] at f0 f10 f1 f20 f2 f3
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    addbackEnv, widened, mask, t0, m1, t1, m2, t2, t3, m4, t4,
    hl0, hl1, hl2, hl3, htop, hbyte, hmask, hzero, hk0, hk1, hk2, hk4, hshift,
    f0.1, f10.1, f1.1, f20.1, f2.1, f3.1, fs,
    Operation.zext, Operation.and, Operation.lshr, hadd,
    UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
