/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchConformance8

/-! Refinement of accepted ordinary finish-or-drop AVX2 lifecycle traces.
Full batches execute the actual compiler MLIR. Partial tails and long messages
remain separate serial execution leaves with an explicit reference premise.
Forgotten-builder traces are not constructors of this lifecycle relation. -/
namespace AgaveLatticeHash.MLIR.Execution.Avx2
open AgaveStaging AgavePhysicalStaging
private abbrev arch : Architecture := .avx2

variable (longHash : AgaveConcrete.Message → Value) (serial : SerialExecution)
variable (serial_refines : ∀ ms a result, serial ms a result →
  result = plus a (scalar (AgaveConcrete.hash longHash) ms))
include serial_refines in
theorem flush_refines {p : Store} {s t : Impl}
    (hr : Represents p s) (hs : PendingOK s) (call : Flush serial arch p s t) :
    t = physicalFlush longHash arch.width arch.positive arch.perm p s := by
  cases call with
  | compiled full result run =>
    rw [BatchConformance8.fullWidth_refines p s result hr hs full run]
    simp [physicalFlush, full, arch, Architecture.width, Architecture.perm]
  | serial notfull result run =>
    rw [serial_refines _ _ _ run]
    simp only [physicalFlush, notfull, and_false, ↓reduceIte]

include serial_refines in
theorem commit_refines {p : Store} {s t : Impl}
    (hr : Represents p s) (hb : Bounds arch.width s) (call : Commit serial arch p s t) :
    t = physicalCommit longHash arch.width arch.positive arch.perm p s := by
  cases call with
  | spilled spill result run =>
    rw [serial_refines _ _ _ run]
    simp only [physicalCommit, spill, ↓reduceIte, scalar_singleton]
  | staged spill notfull => simp only [physicalCommit, spill, Bool.false_eq_true, ↓reduceIte, notfull]
  | full spill full t run =>
    have hc : p.count < 16 := by
      have := arch.bounded
      have := hr.count
      have := hb.1
      omega
    have hfinish := finish_represents p s hr hc hb.2.2
    have hshort := finishLane_pendingOK s hb.2.1 hb.2.2
    rw [flush_refines longHash serial serial_refines hfinish hshort run]
    simp only [physicalCommit, spill, Bool.false_eq_true, ↓reduceIte, full]

include serial_refines in
theorem take_refines {p : Store} {s t : Impl} {v : Value}
    (hr : Represents p s) (hs : PendingOK s) (call : Take serial arch p s v t) :
    (v,t) = physicalTake longHash arch.width arch.positive arch.perm p s := by
  cases call with
  | empty empty => simp only [physicalTake, empty, ↓reduceIte]
  | flush nonempty t run =>
    rw [flush_refines longHash serial serial_refines hr hs run]
    simp only [physicalTake, nonempty, ↓reduceIte]

theorem source_invariants
    {events p s r out} (run : AgaveOutputLog.Run longHash arch.width arch.positive arch.perm events p s r out) :
    Represents p s ∧ Bounds arch.width s := by
  have ht := AgavePhysicalMixed.run_simulates longHash arch.width arch.positive arch.bounded
    arch.perm arch.transpose (AgaveOutputLog.erase longHash _ _ _ run)
  exact ⟨ht.2, (AgaveMixed.run_refines _ _ _ arch.positive ht.1).1⟩

include serial_refines in
theorem erase {events p s r out}
    (run : Run serial arch events p s r out) :
    AgaveOutputLog.Run longHash arch.width arch.positive arch.perm events p s r out := by
  induction run with
  | initial => exact .initial
  | start _ idle ih => exact .start ih idle
  | part _ m part active ih => exact .part ih m part active
  | finish _ m active t call ih =>
    have hi := source_invariants longHash ih
    rw [commit_refines longHash serial serial_refines hi.1 hi.2 call]
    exact .finish ih m active
  | drop _ m active ih => exact .drop ih m active
  | @whole events p s r out run m idle t call ih =>
    have hi := source_invariants longHash ih
    have hc : p.count < 16 := by
      have := arch.bounded
      have := hi.1.count
      have := hi.2.1
      omega
    have ha : Represents (appendStore s.spilled p m) (physicalAppend p s m) := by
      rw [physicalAppend_eq p s m hi.1]
      exact append_represents p s m hi.1 hc
    have hb : Bounds arch.width (physicalAppend p s m) := by
      rw [physicalAppend_eq p s m hi.1]
      exact append_bounds s arch.width m hi.2
    rw [commit_refines longHash serial serial_refines ha hb call]
    exact .whole ih m idle
  | mix_in _ x idle ih => exact .mix_in ih x idle
  | mix_out _ x idle ih => exact .mix_out ih x idle
  | drain _ idle value t call ih =>
    have hi := source_invariants longHash ih
    have he := take_refines longHash serial serial_refines hi.1 hi.2.2.1 call
    have hv := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    change value = _ at hv
    change t = _ at ht
    rw [hv, ht]
    exact .drain ih idle

include serial_refines in
theorem run_refines_log {events p s r out}
    (run : Run serial arch events p s r out) :
    AgaveOutputLog.specEval (AgaveConcrete.hash longHash) events = some (r,out) :=
  AgaveOutputLog.run_refines_log longHash arch.width arch.positive arch.bounded arch.perm
    arch.transpose (erase longHash serial serial_refines run)
/- The serial fallback returns the exact reference result. This is stronger
than mere termination of the external serial implementation. -/
variable (serial_total : ∀ ms a, serial ms a (plus a (scalar (AgaveConcrete.hash longHash) ms)))
include serial_total in
theorem flush_lift {p : Store} {s : Impl}
    (hr : Represents p s) (hs : PendingOK s) :
    Flush serial arch p s (physicalFlush longHash arch.width arch.positive arch.perm p s) := by
  by_cases hf : p.count = arch.width
  · simpa [physicalFlush, hf, arch, Architecture.width, Architecture.perm] using
      Flush.compiled (serial := serial) hf _ (BatchConformance8.fullWidth_total p s hr hs hf)
  · simpa only [physicalFlush, hf, and_false, ↓reduceIte] using
      Flush.serial (arch := .avx2) (p := p) (s := s) hf _ (serial_total (readBatch p) s.acc)

include serial_total in
theorem commit_lift {p : Store} {s : Impl}
    (hr : Represents p s) (hb : Bounds arch.width s) :
    Commit serial arch p s (physicalCommit longHash arch.width arch.positive arch.perm p s) := by
  cases hspill : s.spilled with
  | true =>
    simpa only [physicalCommit, hspill, ↓reduceIte, scalar_singleton] using
      Commit.spilled (arch := .avx2) (p := p) (s := s) hspill _ (serial_total [s.serial] s.acc)
  | false =>
    by_cases hf : (finishStore p).count = arch.width
    · have hc : p.count < 16 := by
        have := arch.bounded
        have := hr.count
        have := hb.1
        omega
      have hfinish := finish_represents p s hr hc hb.2.2
      have hshort := finishLane_pendingOK s hb.2.1 hb.2.2
      simpa only [physicalCommit, hspill, Bool.false_eq_true, ↓reduceIte, hf] using
        Commit.full hspill hf _ (flush_lift longHash serial serial_total hfinish hshort)
    · simpa only [physicalCommit, hspill, Bool.false_eq_true, ↓reduceIte, hf] using
        Commit.staged (serial := serial) (arch := .avx2) (p := p) (s := s) hspill hf

include serial_total in
theorem take_lift {p : Store} {s : Impl}
    (hr : Represents p s) (hs : PendingOK s) :
    Take serial arch p s (physicalTake longHash arch.width arch.positive arch.perm p s).1
      (physicalTake longHash arch.width arch.positive arch.perm p s).2 := by
  by_cases he : p.count = 0
  · simpa only [physicalTake, he, ↓reduceIte] using
      Take.empty (serial := serial) (arch := .avx2) (p := p) (s := s) he
  · simpa only [physicalTake, he, ↓reduceIte] using
      Take.flush he _ (flush_lift longHash serial serial_total hr hs)

include serial_total in
theorem lift {events p s r out}
    (run : AgaveOutputLog.Run longHash arch.width arch.positive arch.perm events p s r out) :
    Run serial arch events p s r out := by
  induction run with
  | initial => exact .initial
  | start _ idle ih => exact .start ih idle
  | part _ m part active ih => exact .part ih m part active
  | finish run m active ih =>
    have hi := source_invariants longHash run
    exact .finish ih m active _ (commit_lift longHash serial serial_total hi.1 hi.2)
  | drop _ m active ih => exact .drop ih m active
  | @whole events p s r out run m idle ih =>
    have hi := source_invariants longHash run
    have hc : p.count < 16 := by
      have := arch.bounded
      have := hi.1.count
      have := hi.2.1
      omega
    have ha : Represents (appendStore s.spilled p m) (physicalAppend p s m) := by
      rw [physicalAppend_eq p s m hi.1]
      exact append_represents p s m hi.1 hc
    have hb : Bounds arch.width (physicalAppend p s m) := by
      rw [physicalAppend_eq p s m hi.1]
      exact append_bounds s arch.width m hi.2
    exact .whole ih m idle _ (commit_lift longHash serial serial_total ha hb)
  | mix_in _ x idle ih => exact .mix_in ih x idle
  | mix_out _ x idle ih => exact .mix_out ih x idle
  | drain run idle ih =>
    have hi := source_invariants longHash run
    exact .drain ih idle _ _ (take_lift longHash serial serial_total hi.1 hi.2.2.1)

include serial_total in
theorem every_legal_trace (events : List AgaveOutputLog.Event)
    {r : AgaveMixed.Spec} {out : List Value}
    (legal : AgaveOutputLog.specEval (AgaveConcrete.hash longHash) events = some (r,out)) :
    ∃ p s, Run serial arch events p s r out := by
  obtain ⟨p, s, run⟩ := AgaveOutputLog.specEval_lift longHash arch.width arch.positive arch.bounded
    arch.perm arch.transpose events legal
  exact ⟨p, s, lift longHash serial serial_total run⟩

/-- With serial calls excluded, every accepted execution refines the public
output log without any external hash-execution premise. -/
theorem noSerial_run_refines_log (longHash : AgaveConcrete.Message → Value)
    {events p s r out} (run : Run (fun _ _ _ => False) .avx2 events p s r out) :
    AgaveOutputLog.specEval (AgaveConcrete.hash longHash) events = some (r,out) :=
  run_refines_log longHash _ (by intros; contradiction) run

end AgaveLatticeHash.MLIR.Execution.Avx2
