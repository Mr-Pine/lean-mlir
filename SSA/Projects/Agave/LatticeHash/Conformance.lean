/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Blake3Reference
import SSA.Projects.Agave.LatticeHash.OutputLog

/-!
End-to-end conformance combines the independent portable BLAKE3 reference
with the public output-log refinement. Keeping this composition separate lets
`Blake3Reference` depend only on the concrete one-chunk equivalence layer.
The theorem retains its original namespace for compatibility.
-/
namespace AgaveBlake3Reference

/-- End-to-end source-shaped statement: any chronological event sequence
    accepted by the portable-reference specification has retained-memory
    executions at widths 1, 8 and 16, and all three produce exactly the same
    complete output log `out`. The sole premise is public API legality. -/
theorem every_legal_portable_trace (longHash : Message → AgaveConcrete.Value)
    (events : List AgaveOutputLog.Event) {r : AgaveMixed.Spec}
    {out : List AgaveConcrete.Value}
    (legal : AgaveOutputLog.specEval
      (fun m => referenceHash longHash (AgaveConcrete.toBytes m)) events = some (r, out)) :
    (∃ p s, AgaveOutputLog.Run longHash 1 (by decide) AgaveLattice.labels
      events p s r out) ∧
    (∃ p s, AgaveOutputLog.Run longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) events p s r out) ∧
    (∃ p s, AgaveOutputLog.Run longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) events p s r out) := by
  apply AgaveOutputLog.every_legal_trace longHash events
  rw [publicHash_eq_portableReference longHash]
  exact legal

end AgaveBlake3Reference
