import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerEmbedding

namespace Agave.Ed25519.SmallOrder.Execution.SerializerXL
open LeanMLIR.RIR
open SerializerEmbedding
open Verifier.Execution.PointConstantTimeEq
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000

private def localIndex := index 12 (by decide) (by decide)

private theorem localType (i : Fin Source.n) : Target.ty (localIndex i) = Source.ty i := by
  fin_cases i <;> rfl

/-- Concrete typed register embedding for inline serializer XL. -/
def embedding : Transport.Embedding Source Target where
  val := localIndex
  type := localType
  injective := index_injective 12 (by decide) (by decide)
  arg := fun i => Fin.cases (%50) (fun j => Fin.cases (%54) (fun k => Fin.elim0 k) j) i
  arg_stable := by
    intro E i j v
    fin_cases i
    all_goals apply Env.read_write_ne
    all_goals apply ne_of_apply_ne Fin.val
    all_goals change _ ≠ (localIndex j).val
    all_goals dsimp [localIndex, index]
    all_goals split <;> omega

abbrev body (p : Primitives) := ((program.entry p).body.drop 64).take 184
abbrev inlineBody (p : Primitives) := ((program.entry p).body.drop 61).take 187

/-- Equality of the imported RIR instruction lists, including every arithmetic
flag and memory operation. Source metadata remains in `inlineBody`. -/
theorem body_alpha (p : Primitives) :
    body p = SerializerSource.core.map embedding.renaming.instr := rfl

theorem inlineBody_exact (p : Primitives) : inlineBody p =
    ((program.entry p).body.drop 61).take 3 ++ body p := rfl

private theorem metadata_run (p : Primitives) (E : Env Target) (s : GlobalState) :
    (((program.entry p).body.drop 61).take 3).foldlM Instr.run E s = .value (E, s) := rfl

/-- Reuse the standalone serializer proof under the exact register embedding.
The initial environment equation makes the hoisted constants and fresh locals
explicit; no whole-serializer execution assumption is present. -/
theorem inline_run (p : Primitives) (E : Env Target) (r a : Pointer)
    (s : GlobalState) (hwf : s.WF) (hr : SmallRange s.mem r 32)
    (ha : SmallRange s.mem a 40)
    (hE : embedding.pull E = SerializerSource.constantEnv
      (Env.init (Encoding.Decompress.Execution.ToBytes.program.args (.value r) (.value a)).get)) :
    ∃ F, (inlineBody p).foldlM Instr.run E s =
      .value (F, {s with mem := Encoding.Decompress.Execution.ToBytes.storeBytes s.mem r (Encoding.Decompress.Execution.ToBytes.machine (SerialFieldMul.readLimbs s a))}) := by
  obtain ⟨G, hG⟩ := SerializerSource.core_run r a s hwf hr ha
  have hp : SerializerSource.core.foldlM Instr.run (embedding.renaming.pull E) s =
      .value (G, {s with mem := Encoding.Decompress.Execution.ToBytes.storeBytes s.mem r (Encoding.Decompress.Execution.ToBytes.machine (SerialFieldMul.readLimbs s a))}) := by
    simpa only [Transport.Embedding.renaming, hE] using hG
  obtain ⟨F, hF, _⟩ := embedding.renaming.fold_success SerializerSource.core
    SerializerSource.core_supported E s _ G hp
  refine ⟨F, ?_⟩
  simp only [inlineBody_exact, List.foldlM_append, EffectM.bind_eq,
    metadata_run, PoisonOr.value_bind, body_alpha, hF]

end Agave.Ed25519.SmallOrder.Execution.SerializerXL
