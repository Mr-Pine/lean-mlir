/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.Lifecycle8

namespace AgaveLatticeHash.MLIR.Execution.Avx2
open AgaveStaging AgavePhysicalStaging

/-- Eight empty messages are genuine short BLAKE3 inputs. This explicit trace
fills a batch, runs the actual AVX2 CFG, and drains the stored result, with
serial execution disabled. In particular the serial-free relation is inhabited
by a trace containing a compiled full-width call. -/
theorem eight_empty_compiled_witness :
    ∃ p s value batch before,
      Run (fun _ _ _ => False) .avx2
        (List.replicate 8 (.whole []) ++ [.drain]) p s AgaveMixed.specInit [value] ∧
      batch.count = 8 ∧
      FullWidthRun .avx2 batch before value ∧
      ∀ longHash, AgaveOutputLog.specEval (AgaveConcrete.hash longHash)
        (List.replicate 8 (.whole []) ++ [.drain]) =
          some (AgaveMixed.specInit, [value]) := by
  have h0 : Run (fun _ _ _ => False) .avx2 [] initialStore init AgaveMixed.specInit [] := .initial
  have h1 := Run.whole h0 [] rfl _ (Commit.staged rfl (by decide))
  have h2 := Run.whole h1 [] rfl _ (Commit.staged rfl (by decide))
  have h3 := Run.whole h2 [] rfl _ (Commit.staged rfl (by decide))
  have h4 := Run.whole h3 [] rfl _ (Commit.staged rfl (by decide))
  have h5 := Run.whole h4 [] rfl _ (Commit.staged rfl (by decide))
  have h6 := Run.whole h5 [] rfl _ (Commit.staged rfl (by decide))
  have h7 := Run.whole h6 [] rfl _ (Commit.staged rfl (by decide))
  have hi := source_invariants (fun _ => zero)
    (erase (fun _ => zero) _ (by intros; contradiction) h7)
  have ha := append_represents _ _ [] hi.1 (by have := hi.1.count; have := hi.2.1; change _ < 8 at this; omega)
  rw [← physicalAppend_eq _ _ [] hi.1] at ha
  have hb := append_bounds _ 8 [] hi.2
  rw [← physicalAppend_eq _ _ [] hi.1] at hb
  have hfinish := finish_represents _ _ ha (by decide) hb.2.2
  have hshort := finishLane_pendingOK _ hb.2.1 hb.2.2
  have hcall := BatchConformance8.fullWidth_total _ _ hfinish hshort (by decide)
  have h8 := Run.whole h7 [] rfl _ (Commit.full rfl (by decide) _
    (Flush.compiled (by decide) _ hcall))
  have hd := Run.drain h8 rfl _ _ (Take.empty (by decide))
  have hr : Run (fun _ _ _ => False) .avx2
      (List.replicate 8 (.whole []) ++ [.drain]) _ _ AgaveMixed.specInit [_] := hd
  refine ⟨_, _, _, _, _, hr, ?_, hcall, ?_⟩
  · decide
  · intro longHash
    exact noSerial_run_refines_log longHash hr

end AgaveLatticeHash.MLIR.Execution.Avx2
