import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheFragments
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorReadOnly

namespace Agave.Ed25519.Tables.SerialCacheExecution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialConstructorRegisters
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The first saved source address is still present after the complete cache body. -/
theorem firstBody_source40 (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E F : ⟪SerialConstructor.kernel.Γ⟫) (s t : GlobalState) (input : Pointer)
    (hi : SmallRange s.mem input 160) (harg : E.args 1 = .value input)
    (h40 : E.read (%1) = .value 40#64)
    (hr : List.foldlM Instr.run E (firstBody p g) s = .value (F, t)) :
    F.read (%37) = .value (input.add 40) := by
  let body := firstBody p g
  have he : body = body.take 4 ++ body.drop 4 := (List.take_append_drop 4 body).symm
  change List.foldlM Instr.run E body s = .value (F,t) at hr
  rw [he] at hr
  obtain ⟨M, u, hl, ht⟩ := body_split _ _ _ _ _ _ hr
  have hgep := hi.gep (k := 40) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  have hleft : List.foldlM Instr.run E (body.take 4) s =
      .value (E[%37 := .value (input.add 40)], s) := by
    simp [body, firstBody, SerialConstructor.kernel.bb0, List.foldlM_cons,
      List.foldlM_nil, Instr.run, EffectM.bind_eq, EffectM.pure_eq,
      EffectM.get_eq, PoisonOr.value_bind, GepIndex.inboundsOffset, mlir_env,
      harg, h40, hgep]
  rw [hleft] at hl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (PoisonOr.value_inj.mp hl)
  have hf := body_prefix (body.drop 4) (limit := 38)
    (by simp [body, firstBody, SerialConstructor.kernel.bb0, Instr.above, Dsts.above]) _ _ _ _ ht
  rw [hf.read _ (by intro i ht he; cases he; decide)]
  simp [mlir_env]

/-- The source Z address is also preserved, without repeating the arithmetic. -/
theorem firstBody_source80 (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E F : ⟪SerialConstructor.kernel.Γ⟫) (s t : GlobalState) (input : Pointer)
    (hi : SmallRange s.mem input 160) (harg : E.args 1 = .value input)
    (h80 : E.read (%15) = .value 80#64)
    (hr : List.foldlM Instr.run E (firstBody p g) s = .value (F, t)) :
    F.read (%87) = .value (input.add 80) := by
  let body := firstBody p g
  have he : body = body.take 55 ++ body.drop 55 := (List.take_append_drop 55 body).symm
  change List.foldlM Instr.run E body s = .value (F,t) at hr
  rw [he] at hr
  obtain ⟨M, u, hl, ht⟩ := body_split _ _ _ _ _ _ hr
  have hs := body_readOnly (body.take 55)
    (by simp [body, firstBody, SerialConstructor.kernel.bb0, Instr.readOnly]) E M s u hl
  subst u
  have hf := body_prefix (body.take 55) (limit := 37)
    (by simp [body, firstBody, SerialConstructor.kernel.bb0, Instr.above, Dsts.above]) E M s s hl
  have ha : M.args 1 = .value input := by rw [hf.1]; exact harg
  have hv : M.read (%15) = .value 80#64 := by
    rw [hf.read _ (by intro i ht he; cases he; decide)]
    exact h80
  have hgep := hi.gep (k := 80) (by decide)
  norm_num only [Nat.cast_ofNat] at hgep
  change List.foldlM Instr.run M
    (.gepInbounds (%87) (%arg1) [.constant 80] :: body.drop 56) s = .value (F,t) at ht
  simp only [List.foldlM_cons, Instr.run, EffectM.bind_eq, EffectM.get_eq,
    PoisonOr.value_bind, EffectM.pure_eq, GepIndex.inboundsOffset,
    List.map_cons, List.map_nil, Env.read_arg, ha, hv] at ht
  rw [hgep] at ht
  have hf' := body_prefix (body.drop 56) (limit := 88)
    (by simp [body, firstBody, SerialConstructor.kernel.bb0, Instr.above, Dsts.above]) _ _ _ _ ht
  rw [hf'.read _ (by intro i ht he; cases he; decide)]
  simp [mlir_env]

end Agave.Ed25519.Tables.SerialCacheExecution
