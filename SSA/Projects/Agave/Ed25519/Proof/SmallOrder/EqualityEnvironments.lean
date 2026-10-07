import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.FirstSerializerInitialization
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerFrames

/-! Environment links between the four exact inline serializer copies. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityEnvironments
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

/-- Pointwise preservation of the registers selected by an embedding suffices
for preservation of its pulled environment. -/
theorem pull_congr (ρ : Transport.Embedding Γ Δ) (E F : Env Δ)
    (ha : ∀ i, F.read (ρ.arg i) = E.read (ρ.arg i))
    (hv : ∀ i, F.read (.val (ρ.val i) (ρ.type i)) =
      E.read (.val (ρ.val i) (ρ.type i))) : ρ.pull F = ρ.pull E := by
  apply Transport.env_ext
  · exact funext ha
  · exact funext hv

theorem xr_after_xl (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (h : (SerializerXL.inlineBody p).foldlM Instr.run E s = .value (F, t)) :
    SerializerXR.embedding.pull F = SerializerXR.embedding.pull E := by
  apply pull_congr
  · intro i
    apply SerializerXL.frame p _ _ E F s t h
    fin_cases i <;> exact Or.inl (by decide)
  · intro i
    apply SerializerXL.frame p _ _ E F s t h
    change (if i.val < 45 then i.val + 2 else i.val + 164) < 57 ∨
      208 < (if i.val < 45 then i.val + 2 else i.val + 164)
    split_ifs <;> omega

theorem yl_after_xl (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (h : (SerializerXL.inlineBody p).foldlM Instr.run E s = .value (F, t)) :
    SerializerYL.embedding.pull F = SerializerYL.embedding.pull E := by
  apply pull_congr
  · intro i
    apply SerializerXL.frame p _ _ E F s t h
    fin_cases i <;> exact Or.inl (by decide)
  · intro i
    apply SerializerXL.frame p _ _ E F s t h
    change (if i.val < 45 then i.val + 2 else i.val + 319) < 57 ∨
      208 < (if i.val < 45 then i.val + 2 else i.val + 319)
    split_ifs <;> omega

theorem yl_after_xr (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (h : (SerializerXR.inlineBody p).foldlM Instr.run E s = .value (F, t)) :
    SerializerYL.embedding.pull F = SerializerYL.embedding.pull E := by
  apply pull_congr
  · intro i
    apply SerializerXR.frame p _ _ E F s t h
    fin_cases i <;> exact Or.inl (by decide)
  · intro i
    apply SerializerXR.frame p _ _ E F s t h
    change (if i.val < 45 then i.val + 2 else i.val + 319) < 209 ∨
      360 < (if i.val < 45 then i.val + 2 else i.val + 319)
    split_ifs <;> omega

theorem yr_after_xl (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (h : (SerializerXL.inlineBody p).foldlM Instr.run E s = .value (F, t)) :
    SerializerYR.embedding.pull F = SerializerYR.embedding.pull E := by
  apply pull_congr
  · intro i
    apply SerializerXL.frame p _ _ E F s t h
    fin_cases i <;> exact Or.inl (by decide)
  · intro i
    apply SerializerXL.frame p _ _ E F s t h
    change (if i.val < 45 then i.val + 2 else i.val + 471) < 57 ∨
      208 < (if i.val < 45 then i.val + 2 else i.val + 471)
    split_ifs <;> omega

theorem yr_after_xr (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (h : (SerializerXR.inlineBody p).foldlM Instr.run E s = .value (F, t)) :
    SerializerYR.embedding.pull F = SerializerYR.embedding.pull E := by
  apply pull_congr
  · intro i
    apply SerializerXR.frame p _ _ E F s t h
    fin_cases i <;> exact Or.inl (by decide)
  · intro i
    apply SerializerXR.frame p _ _ E F s t h
    change (if i.val < 45 then i.val + 2 else i.val + 471) < 209 ∨
      360 < (if i.val < 45 then i.val + 2 else i.val + 471)
    split_ifs <;> omega

theorem yr_after_yl (p : Primitives) (E F : Env program.Γ)
    (s t : GlobalState)
    (h : (SerializerYL.inlineBody p).foldlM Instr.run E s = .value (F, t)) :
    SerializerYR.embedding.pull F = SerializerYR.embedding.pull E := by
  apply pull_congr
  · intro i
    apply SerializerYL.frame p _ _ E F s t h
    fin_cases i <;> exact Or.inl (by decide)
  · intro i
    apply SerializerYL.frame p _ _ E F s t h
    change (if i.val < 45 then i.val + 2 else i.val + 471) < 364 ∨
      515 < (if i.val < 45 then i.val + 2 else i.val + 471)
    split_ifs <;> omega

theorem xr_initial (s : GlobalState) (left right : Pointer) :
    SerializerXR.embedding.pull (firstSerializerEnv s left right) =
      SerializerSource.constantEnv
        (Env.init (Encoding.Decompress.Execution.ToBytes.program.args
          (.value (EqualityAllocation.slot2 s))
          (.value (EqualityAllocation.slot6 s))).get) := by
  apply Transport.env_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem yl_initial (s : GlobalState) (left right : Pointer) :
    SerializerYL.embedding.pull (firstSerializerEnv s left right) =
      SerializerSource.constantEnv
        (Env.init (Encoding.Decompress.Execution.ToBytes.program.args
          (.value (EqualityAllocation.slot1 s))
          (.value (EqualityAllocation.slot5 s))).get) := by
  apply Transport.env_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem yr_initial (s : GlobalState) (left right : Pointer) :
    SerializerYR.embedding.pull (firstSerializerEnv s left right) =
      SerializerSource.constantEnv
        (Env.init (Encoding.Decompress.Execution.ToBytes.program.args
          (.value (EqualityAllocation.slot0 s))
          (.value (EqualityAllocation.slot4 s))).get) := by
  apply Transport.env_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

theorem yl_writes (E : Env program.Γ) (x : BitVec 8) (left right : Pointer) :
    SerializerYL.embedding.pull
      (E[%361 := .value x, %362 := .value (left.add 40), %363 := .value (right.add 40)]) =
      SerializerYL.embedding.pull E := by
  apply Transport.env_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    change (E[%361 := .value x, %362 := .value (left.add 40), %363 := .value (right.add 40)]).read
      (.val (SerializerYL.embedding.val i) (SerializerYL.embedding.type i)) = _
    rw [Env.read_write_ne (h := by
      apply ne_of_apply_ne Fin.val
      change (if i.val < 45 then i.val + 2 else i.val + 319) ≠ 363
      split_ifs <;> omega)]
    rw [Env.read_write_ne (h := by
      apply ne_of_apply_ne Fin.val
      change (if i.val < 45 then i.val + 2 else i.val + 319) ≠ 362
      split_ifs <;> omega)]
    rw [Env.read_write_ne (h := by
      apply ne_of_apply_ne Fin.val
      change (if i.val < 45 then i.val + 2 else i.val + 319) ≠ 361
      split_ifs <;> omega)]
    rfl

theorem yr_writes (E : Env program.Γ) (x : BitVec 8) (left right : Pointer) :
    SerializerYR.embedding.pull
      (E[%361 := .value x, %362 := .value (left.add 40), %363 := .value (right.add 40)]) =
      SerializerYR.embedding.pull E := by
  apply Transport.env_ext
  · funext i
    fin_cases i <;> rfl
  · funext i
    change (E[%361 := .value x, %362 := .value (left.add 40), %363 := .value (right.add 40)]).read
      (.val (SerializerYR.embedding.val i) (SerializerYR.embedding.type i)) = _
    rw [Env.read_write_ne (h := by
      apply ne_of_apply_ne Fin.val
      change (if i.val < 45 then i.val + 2 else i.val + 471) ≠ 363
      split_ifs <;> omega)]
    rw [Env.read_write_ne (h := by
      apply ne_of_apply_ne Fin.val
      change (if i.val < 45 then i.val + 2 else i.val + 471) ≠ 362
      split_ifs <;> omega)]
    rw [Env.read_write_ne (h := by
      apply ne_of_apply_ne Fin.val
      change (if i.val < 45 then i.val + 2 else i.val + 471) ≠ 361
      split_ifs <;> omega)]
    rfl

end Agave.Ed25519.SmallOrder.Execution.EqualityEnvironments
