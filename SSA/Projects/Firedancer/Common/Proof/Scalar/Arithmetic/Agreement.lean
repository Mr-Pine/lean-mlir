import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SourceEvaluator
import SSA.Projects.Firedancer.Common.Proof.fd_ed25519_verify

/-! The arithmetic expression and any deterministic source adapter have the
same result on every 64-byte string. The comparison uses the actual source
call and its four stores, including the case where input and output alias. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Firedancer.Common.ScalarArithmetic
open LeanMLIR SLLVM

private theorem returned_packed_eq {f g : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)}
    (hf : ScalarReduceBy f) (hg : ScalarReduceBy g)
    (out inp : Pointer) (s : GlobalState) (hs : s.WF)
    (hout : IsByteBufPtr s.mem out) (hoff : inp.offset.toNat + 64 ≤ 2 ^ 64)
    (hin : Fits s.mem inp (64 * 8))
    {wf wg : Fin 4 → BitVec 64}
    (hfw : f (readWord hin) = some wf) (hgw : g (readWord hin) = some wg) :
    packWords wf = packWords wg := by
  obtain ⟨sf, hrf, hef⟩ := (hf out inp s hs hout hoff hin).1 wf hfw
  obtain ⟨sg, hrg, heg⟩ := (hg out inp s hs hout hoff hin).1 wg hgw
  have hstates : sf = sg := by
    have heq := hrf.symm.trans hrg
    simp only [PoisonOr.value_inj, Prod.mk.injEq] at heq
    exact heq.2
  subst sg
  have hbf : IsByteBufPtr (scalarOutMem s.mem out wf) out :=
    isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hout)))
  have hbg : IsByteBufPtr (scalarOutMem s.mem out wg) out :=
    isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice (isByteBufPtr_splice hout)))
  rw [← readBuf_scalarOutMem hout hbf, ← readBuf_scalarOutMem hout hbg]
  exact readBuf_of_live?_eq ((hef.live out.id).symm.trans (heg.live out.id))

/-- A source model determines both definedness and the exact packed output. -/
theorem packed_eq_on_readable {f g : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)}
    (hf : ScalarReduceBy f) (hg : ScalarReduceBy g)
    (out inp : Pointer) (s : GlobalState) (hs : s.WF)
    (hout : IsByteBufPtr s.mem out) (hoff : inp.offset.toNat + 64 ≤ 2 ^ 64)
    (hin : Fits s.mem inp (64 * 8)) :
    (f (readWord hin)).map packWords = (g (readWord hin)).map packWords := by
  cases hfw : f (readWord hin) with
  | none =>
    cases hgw : g (readWord hin) with
    | none => rfl
    | some wg =>
      obtain ⟨sg, hrg, _⟩ := (hg out inp s hs hout hoff hin).1 wg hgw
      rw [(hf out inp s hs hout hoff hin).2 hfw] at hrg
      cases hrg
  | some wf =>
    cases hgw : g (readWord hin) with
    | none =>
      obtain ⟨sf, hrf, _⟩ := (hf out inp s hs hout hoff hin).1 wf hfw
      rw [(hg out inp s hs hout hoff hin).2 hgw] at hrf
      cases hrf
    | some wg =>
      exact congrArg some (returned_packed_eq hf hg out inp s hs hout hoff hin hfw hgw)

private def witnessPointer : Pointer := ⟨⟨0⟩, 0⟩
private def witnessState (digest : BitVec 512) : GlobalState :=
  { alloc := ⟨1⟩
    mem := ⟨(∅ : Std.HashMap BlockId Block).insert ⟨0⟩ (.live ⟨64, digest⟩)⟩
    globals := ∅ }

private theorem witness_wf (digest : BitVec 512) : (witnessState digest).WF := by
  intro b hb
  have hne : (⟨0⟩ : BlockId) ≠ b := by intro h; cases h; simp [witnessState] at hb
  simp [witnessState, MemoryState.live?, MemoryState.getElem?_eq, hne]

private theorem witness_fits (digest : BitVec 512) :
    Fits (witnessState digest).mem witnessPointer (64 * 8) := by
  refine ⟨⟨64, digest⟩, ?_, ?_⟩
  · simp [witnessState, witnessPointer, MemoryState.getElem?_eq]
  · simp [witnessPointer, Pointer.offsetInBits, LiveBlock.lengthInBits]

private theorem witness_read (digest : BitVec 512) :
    readWord (witness_fits digest) = digest := by
  apply readWord_eq_of
  simp [readWord?, witnessState, witnessPointer, MemoryState.live?,
    MemoryState.getElem?_eq, Pointer.offsetInBits]

/-- Every 512-bit value is realizable as a readable input buffer, so no memory
premise remains in the equality between two source models. -/
theorem packed_eq {f g : BitVec (64 * 8) → Option (Fin 4 → BitVec 64)}
    (hf : ScalarReduceBy f) (hg : ScalarReduceBy g) (digest : BitVec 512) :
    (f digest).map packWords = (g digest).map packWords := by
  have h := packed_eq_on_readable hf hg witnessPointer witnessPointer (witnessState digest)
    (witness_wf digest) ⟨Fits.mono (witness_fits digest) (by decide), by decide⟩
    (by decide) (witness_fits digest)
  simpa only [witness_read] using h

end Firedancer.Common.ScalarArithmetic
