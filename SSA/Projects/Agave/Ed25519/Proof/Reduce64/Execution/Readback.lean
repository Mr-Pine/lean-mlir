import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Kernel
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Output

namespace Agave.Ed25519.Reduce64.Execution
open LeanMLIR.RIR

section

/-- A single execution endpoint: the actual kernel returns normally, its memory
contains the integer reduction in every physical lane, and every field residue
is preserved. The only arithmetic hypothesis is the existing column bound. -/
theorem kernel_correct (dst src : Pointer) (s : GlobalState)
    (hwf : s.WF) (hdst : SmallRange s.mem dst 160) (hsrc : SmallRange s.mem src 320)
    (hz : ∀ lane : Fin 4, ColumnsBound
      (fun j => ((readColumns s.mem src j)[lane]).toNat)) :
    ∃ s' : GlobalState,
      program.call (program.args (.value dst) (.value src)) s = .value (.nil, s') ∧
      (∀ (lane : Fin 4) (limb : Fin 10),
        (outputWord s'.mem dst limb lane).toNat = Reduce64.reduce
          (fun j => ((readColumns s.mem src j)[lane]).toNat) limb) ∧
      (∀ lane : Fin 4, Field.SameField
        (Field.decode10 (fun j => ((readColumns s.mem src j)[lane]).toNat))
        (Field.decode10 (fun j => (outputWord s'.mem dst j lane).toNat))) := by
  refine ⟨{s with mem := storeOutputs s.mem dst (readColumns s.mem src)},
    kernel_call dst src s hwf hdst hsrc, ?_, ?_⟩
  · intro lane limb
    exact outputWord_toNat _ _ _ hdst lane (hz lane) limb
  · intro lane
    simp only [outputWord_toNat _ _ _ hdst lane (hz lane)]
    exact Reduce64.residue _

end
end Agave.Ed25519.Reduce64.Execution
