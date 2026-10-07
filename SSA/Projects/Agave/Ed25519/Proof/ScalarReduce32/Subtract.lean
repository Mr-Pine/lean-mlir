import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.SubtractBorrow
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.SubtractBlackBox
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.SubtractAddback
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.SubtractStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

/-- Signed range of the actual top difference; no incoming-borrow premise. -/
theorem subtract_top_bounds (x : Fin 5 → BitVec 52) :
    let d := differences (x 0) (x 1) (x 2) (x 3) (x 4);
    -(2 ^ 53 : Int) ≤ (d 4).toInt ∧ (d 4).toInt < (2 ^ 53 : Int) := by
  dsimp only
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  have hx : ((x 4).setWidth 64).toNat < 2 ^ 52 := by
    simpa only [BitVec.toNat_setWidth_of_le (by decide : 52 ≤ 64)] using (x 4).isLt
  have hf := limb_minus_constant ((x 4).setWidth 64) 17592186044416 hx (by decide)
  have hfi : ((x 4).setWidth 64 + (-17592186044416 : BitVec 64)).toInt =
      (((x 4).setWidth 64).toNat : Int) - 17592186044416 := hf.2
  have hb := ((borrowSteps_certificate x).1 3).2
  have hm : ((d 3).sshiftRight 63).toInt = -((borrowSteps x 3).2 : Int) := by
    rw [(differences_refine x 3).2]
    exact borrow_mask_toInt _ hb
  have hs := signed_add64 ((x 4).setWidth 64 + (-17592186044416 : BitVec 64))
    ((d 3).sshiftRight 63)
    (by rw [hfi, hm]; norm_num only at hx ⊢; omega)
    (by rw [hfi, hm]; norm_num only at hx ⊢; omega)
  change -(2 ^ 53 : Int) ≤
      ((x 4).setWidth 64 + (-17592186044416 : BitVec 64) + (d 3).sshiftRight 63).toInt ∧
    ((x 4).setWidth 64 + (-17592186044416 : BitVec 64) + (d 3).sshiftRight 63).toInt < _
  rw [hs.2, hfi, hm]
  norm_num only at hx ⊢
  omega

structure SubtractReady (E : Env program.Γ) (x : Fin 5 → BitVec 52)
    (scratch : Fin 5 → Pointer) : Prop where
  x0 : E.read (%286) = .value ((x 0).setWidth 64)
  x1 : E.read (%294) = .value ((x 1).setWidth 64)
  x2 : E.read (%300) = .value ((x 2).setWidth 64)
  x3 : E.read (%306) = .value ((x 3).setWidth 64)
  x4 : E.read (%308) = .value ((x 4).setWidth 64)
  p0 : E.read (%76) = .value (scratch 0)
  p1 : E.read (%77) = .value (scratch 1)
  p2 : E.read (%78) = .value (scratch 2)
  p3 : E.read (%79) = .value (scratch 3)
  p4 : E.read (%80) = .value (scratch 4)
  c21 : E.read (%21) = .value (0 : BitVec 64)
  c23 : E.read (%23) = .value (4503599627370495 : BitVec 64)
  c35 : E.read (%35) = .value (-671914833335277 : BitVec 64)
  c36 : E.read (%36) = .value (63 : BitVec 64)
  c37 : E.read (%37) = .value (-3916664325105025 : BitVec 64)
  c38 : E.read (%38) = .value (-1367801 : BitVec 64)
  c39 : E.read (%39) = .value (-17592186044416 : BitVec 64)
  c40 : E.read (%40) = .value (671914833335277 : BitVec 64)
  c41 : E.read (%41) = .value (3916664325105025 : BitVec 64)
  c42 : E.read (%42) = .value (52 : BitVec 64)
  c43 : E.read (%43) = .value (1367801 : BitVec 64)
  c44 : E.read (%44) = .value (17592186044416 : BitVec 64)

def subtractLow (x : Fin 5 → BitVec 52) : Fin 4 → BitVec 64 :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  fun i => d ⟨i.val, by omega⟩ &&& 4503599627370495#64

def subtractWords (x : Fin 5 → BitVec 52) : Fin 5 → BitVec 64 :=
  addback (differences (x 0) (x 1) (x 2) (x 3) (x 4))

def subtractEnv (E : Env program.Γ) (x : Fin 5 → BitVec 52) : Env program.Γ :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  subtractAddbackEnv ((subtractBorrowEnv E x)[%327 := .value (borrowByte d)])
    (subtractLow x) (d 4) (borrowByte d)

def subtractState (s : GlobalState) (x : Fin 5 → BitVec 52)
    (scratch : Fin 5 → Pointer) : GlobalState :=
  { alloc := (s.alloca 1).alloc,
    mem := (((((s.mem.storeAt (scratch 0) (subtractWords x 0)).storeAt
      (scratch 1) (subtractWords x 1)).storeAt (scratch 2) (subtractWords x 2)).storeAt
      (scratch 3) (subtractWords x 3)).storeAt (scratch 4) (subtractWords x 4)) }


theorem subtract_body_decomposition : subtract =
    (program.entry.body.drop 358).take 18 ++
    (program.entry.body.drop 376).take 1 ++
    (program.entry.body.drop 377).take 23 ++ subtractStores0Block.body := rfl

/-- All 47 actual subtraction instructions, including the linked black-box
allocation and five private stores, from register/range invariants only. -/
theorem subtract_body (E : Env program.Γ) (s : GlobalState)
    (x : Fin 5 → BitVec 52) (scratch : Fin 5 → Pointer)
    (hr : SubtractReady E x scratch) (hwf : s.WF)
    (hfit : ∀ i, SmallRange s.mem (scratch i) 8) :
    List.foldlM Instr.run E subtract s = .value (subtractEnv E x, subtractState s x scratch) := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  let byte := borrowByte d
  let E1 := subtractBorrowEnv E x
  let E2 := E1[%327 := .value byte]
  let E3 := subtractAddbackEnv E2 (subtractLow x) (d 4) byte
  let s1 : GlobalState := {s with alloc := (s.alloca 1).alloc}
  have hborrow := subtract_borrow E s x hr.x0 hr.x1 hr.x2 hr.x3 hr.x4
    hr.c23 hr.c35 hr.c36 hr.c37 hr.c38 hr.c39
  change List.foldlM Instr.run E ((program.entry.body.drop 358).take 18) s =
    .value (E1, s) at hborrow
  have hbyte : E1.read (%326) = .value byte := by
    simp (disch := decide) only [E1, byte, d, subtractBorrowEnv, mlir_env]
  have hcall := subtract_black_box E1 s byte hwf hbyte
  change List.foldlM Instr.run E1 ((program.entry.body.drop 376).take 1) s =
    .value (E2, s1) at hcall
  have hlow (i : Fin 4) : (subtractLow x i).toNat < 2 ^ 52 := by
    rw [subtractLow, Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul.mask52_toNat]
    exact Nat.mod_lt _ (by decide)
  have htop := subtract_top_bounds x
  have hadd : List.foldlM Instr.run E2 ((program.entry.body.drop 377).take 23) s1 =
      .value (E3, s1) := by
    apply subtract_addback E2 s1 (subtractLow x) (d 4) byte hlow htop.1 htop.2 <;>
      simp (disch := decide) only [E2, E1, subtractBorrowEnv, subtractLow, d, byte,
        hr.c23, hr.c21, hr.c40, hr.c41, hr.c42, hr.c43, hr.c44, mlir_env] <;> rfl
  have hstore := subtractStores0_execute E3 s1
    (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4)
    (subtractWords x 0) (subtractWords x 1) (subtractWords x 2)
    (subtractWords x 3) (subtractWords x 4)
    (hfit 0)
    (by simp (disch := decide) only [E3, E2, E1, subtractAddbackEnv, subtractBorrowEnv, hr.p0, mlir_env])
    (hfit 1)
    (by simp (disch := decide) only [E3, E2, E1, subtractAddbackEnv, subtractBorrowEnv, hr.p1, mlir_env])
    (hfit 2)
    (by simp (disch := decide) only [E3, E2, E1, subtractAddbackEnv, subtractBorrowEnv, hr.p2, mlir_env])
    (hfit 3)
    (by simp (disch := decide) only [E3, E2, E1, subtractAddbackEnv, subtractBorrowEnv, hr.p3, mlir_env])
    (hfit 4)
    (by simp (disch := decide) only [E3, E2, E1, subtractAddbackEnv, subtractBorrowEnv, hr.p4, mlir_env])
    (by simp (disch := decide) only [E3, subtractAddbackEnv, mlir_env]; rfl)
    (by simp (disch := decide) only [E3, subtractAddbackEnv, mlir_env]; rfl)
    (by simp (disch := decide) only [E3, subtractAddbackEnv, mlir_env]; rfl)
    (by simp (disch := decide) only [E3, subtractAddbackEnv, mlir_env]; rfl)
    (by simp (disch := decide) only [E3, subtractAddbackEnv, mlir_env]; rfl)
  change List.foldlM Instr.run E3 subtractStores0Block.body s1 =
    .value (E3, subtractState s x scratch) at hstore
  rw [subtract_body_decomposition]
  simp only [List.foldlM_append, EffectM.bind_eq, hborrow, hcall, hadd, hstore,
    LeanMLIR.RIR.PoisonOr.value_bind]
  rfl

/-- The resulting words perform precisely the one conditional subtraction. -/
theorem subtractWords_value (x : Fin 5 → BitVec 52) :
    Arithmetic.limbs (subtractWords x 0).toNat (subtractWords x 1).toNat
      (subtractWords x 2).toNat (subtractWords x 3).toNat (subtractWords x 4).toNat =
      if rawValue x < Agave.Ed25519.Bridge.subgroupOrder then rawValue x
      else rawValue x - Agave.Ed25519.Bridge.subgroupOrder :=
  conditional_subtract_words x

end Agave.Ed25519.ScalarReduce32.Execution
