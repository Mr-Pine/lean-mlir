/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.PhysicalStaging
import SSA.Projects.Agave.LatticeHash.MixedLifecycle

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-!
The combined public lifecycle proof. Full batches execute the concrete kernel
over the retained allocation, scalar tails and spill prefixes read that same
allocation, and arbitrary precomputed LtHash values may be mixed between builder
lifetimes. The logical lists are ghost state. All byte-validity and backend
correctness facts are derived from the public trace, never assumed by clients.
-/
namespace AgavePhysicalMixed

open AgaveStaging AgavePhysicalStaging

/-- Finite legal public traces including arbitrary accumulator effects.
    As in `AgaveMixed`, `mix_out` abbreviates mixing in a negated LtHash.
    `start` acquires the builder borrow; finish or drop releases it. -/
inductive Run (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix) :
    Store → Impl → AgaveMixed.Spec → Prop
  | initial : Run longHash n hn perm initialStore init AgaveMixed.specInit
  | start {p s r} (run : Run longHash n hn perm p s r) (idle : r.active = none) :
      Run longHash n hn perm p s { r with active := some [] }
  | part {p s r} (run : Run longHash n hn perm p s r)
      (m part : Message) (active : r.active = some m) :
      Run longHash n hn perm (appendStore s.spilled p part) (physicalAppend p s part)
        { r with active := some (m ++ part) }
  | finish {p s r} (run : Run longHash n hn perm p s r)
      (m : Message) (active : r.active = some m) :
      Run longHash n hn perm (commitStore n s.spilled p)
        (physicalCommit longHash n hn perm p s) ⟨r.committed ++ [m], none, r.offset⟩
  | drop {p s r} (run : Run longHash n hn perm p s r)
      (m : Message) (active : r.active = some m) :
      Run longHash n hn perm (discardStore p) (discard s) { r with active := none }
  | whole {p s r} (run : Run longHash n hn perm p s r)
      (m : Message) (idle : r.active = none) :
      Run longHash n hn perm
        (commitStore n (physicalAppend p s m).spilled (appendStore s.spilled p m))
        (physicalCommit longHash n hn perm (appendStore s.spilled p m) (physicalAppend p s m))
        ⟨r.committed ++ [m], none, r.offset⟩
  | mix_in {p s r} (run : Run longHash n hn perm p s r)
      (x : Value) (idle : r.active = none) :
      Run longHash n hn perm p (AgaveMixed.mixIn s x)
        { r with offset := plus r.offset x }
  | mix_out {p s r} (run : Run longHash n hn perm p s r)
      (x : Value) (idle : r.active = none) :
      Run longHash n hn perm p (AgaveMixed.mixOut s x)
        { r with offset := plus r.offset (AgaveMixed.neg x) }
  | drain {p s r} (run : Run longHash n hn perm p s r) (idle : r.active = none) :
      Run longHash n hn perm (takeStore p) (physicalTake longHash n hn perm p s).2
        AgaveMixed.specInit

theorem mixIn_represents (p : Store) (s : Impl) (x : Value) (hr : Represents p s) :
    Represents p (AgaveMixed.mixIn s x) :=
  ⟨hr.count, hr.cursor, hr.committed, hr.current⟩

theorem mixOut_represents (p : Store) (s : Impl) (x : Value) (hr : Represents p s) :
    Represents p (AgaveMixed.mixOut s x) :=
  ⟨hr.count, hr.cursor, hr.committed, hr.current⟩

/-- Every physical mixed trace simultaneously follows the verified abstract
    lifecycle and maintains valid metadata, live bytes and final-block padding. -/
theorem run_simulates (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {p : Store} {s : Impl} {r : AgaveMixed.Spec}
    (trace : Run longHash n hn perm p s r) :
    AgaveMixed.Run (AgaveConcrete.hash longHash) n
      (AgaveConcrete.backend longHash n hn perm hp) s r ∧ Represents p s := by
  induction trace with
  | initial => exact ⟨.initial, initial_represents⟩
  | start _ idle ih => exact ⟨.start ih.1 idle, ih.2⟩
  | @part p s r run m part active ih =>
    have hb := (AgaveMixed.run_refines _ _ _ hn ih.1).1
    have hc : p.count < 16 := by have hh := ih.2.count; have hh' := hb.1; omega
    rw [physicalAppend_eq p s part ih.2]
    exact ⟨.part ih.1 m part active, append_represents p s part ih.2 hc⟩
  | @finish p s r run m active ih =>
    have hb := (AgaveMixed.run_refines _ _ _ hn ih.1).1
    rw [physicalCommit_eq longHash n hn hn16 perm hp p s ih.2 hb]
    exact ⟨.finish ih.1 m active, commit_represents _ n _ p s ih.2 hn16 hb⟩
  | drop _ m active ih => exact ⟨.drop ih.1 m active, discard_represents _ _ ih.2⟩
  | @whole p s r run m idle ih =>
    have hb := (AgaveMixed.run_refines _ _ _ hn ih.1).1
    have hc : p.count < 16 := by have hh := ih.2.count; have hh' := hb.1; omega
    have ha := append_represents p s m ih.2 hc
    have hba := append_bounds s n m hb
    rw [physicalAppend_eq p s m ih.2,
      physicalCommit_eq longHash n hn hn16 perm hp _ _ ha hba]
    exact ⟨.whole ih.1 m idle, commit_represents _ n _ _ _ ha hn16 hba⟩
  | mix_in _ x idle ih => exact ⟨.mix_in ih.1 x idle, mixIn_represents _ _ x ih.2⟩
  | mix_out _ x idle ih => exact ⟨.mix_out ih.1 x idle, mixOut_represents _ _ x ih.2⟩
  | @drain p s r run idle ih =>
    have hr := AgaveMixed.run_refines _ _ _ hn ih.1
    have hc := hr.2.1
    rw [idle] at hc
    rw [physicalTake_eq longHash n hn perm hp p s ih.2 hr.1.2.1]
    exact ⟨.drain ih.1 idle, take_represents _ n _ p s ih.2 hc.1⟩

/-- No staging, padding, backend correctness or accumulator premises remain.
    The only semantic condition is a legal trace observed between builders. -/
theorem observational_equivalence (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {p : Store} {s : Impl} {r : AgaveMixed.Spec}
    (trace : Run longHash n hn perm p s r) (idle : r.active = none) :
    (physicalTake longHash n hn perm p s).1 =
      plus (scalar (AgaveConcrete.hash longHash) r.committed) r.offset := by
  have ht := run_simulates longHash n hn hn16 perm hp trace
  have hb := (AgaveMixed.run_refines _ _ _ hn ht.1).1
  rw [physicalTake_eq longHash n hn perm hp p s ht.2 hb.2.1]
  exact AgaveMixed.observational_equivalence _ _ _ hn ht.1 idle

/-- Every legal abstract mixed trace has a physical retained-memory execution.
    Thus the physical trace relation introduces no extra program restriction. -/
theorem run_lift (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {s : Impl} {r : AgaveMixed.Spec}
    (trace : AgaveMixed.Run (AgaveConcrete.hash longHash) n
      (AgaveConcrete.backend longHash n hn perm hp) s r) :
    ∃ p, Run longHash n hn perm p s r := by
  induction trace with
  | initial => exact ⟨_, .initial⟩
  | start _ idle ih => rcases ih with ⟨p, run⟩; exact ⟨p, .start run idle⟩
  | @part s r trace m part active ih =>
    rcases ih with ⟨p, run⟩
    have hr := (run_simulates longHash n hn hn16 perm hp run).2
    refine ⟨appendStore s.spilled p part, ?_⟩
    simpa only [physicalAppend_eq p s part hr] using Run.part run m part active
  | @finish s r trace m active ih =>
    rcases ih with ⟨p, run⟩
    have hr := (run_simulates longHash n hn hn16 perm hp run).2
    have hb := (AgaveMixed.run_refines _ _ _ hn trace).1
    refine ⟨commitStore n s.spilled p, ?_⟩
    simpa only [physicalCommit_eq longHash n hn hn16 perm hp p s hr hb]
      using Run.finish run m active
  | drop _ m active ih => rcases ih with ⟨p, run⟩; exact ⟨_, .drop run m active⟩
  | @whole s r trace m idle ih =>
    rcases ih with ⟨p, run⟩
    have hr := (run_simulates longHash n hn hn16 perm hp run).2
    have hb := (AgaveMixed.run_refines _ _ _ hn trace).1
    have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
    refine ⟨commitStore n (append s m).spilled (appendStore s.spilled p m), ?_⟩
    simpa only [physicalAppend_eq p s m hr,
      physicalCommit_eq longHash n hn hn16 perm hp _ _
        (append_represents p s m hr hc) (append_bounds s n m hb), addMessage]
      using Run.whole run m idle
  | mix_in _ x idle ih => rcases ih with ⟨p, run⟩; exact ⟨p, .mix_in run x idle⟩
  | mix_out _ x idle ih => rcases ih with ⟨p, run⟩; exact ⟨p, .mix_out run x idle⟩
  | @drain s r trace idle ih =>
    rcases ih with ⟨p, run⟩
    have hr := (run_simulates longHash n hn hn16 perm hp run).2
    have hb := (AgaveMixed.run_refines _ _ _ hn trace).1
    refine ⟨takeStore p, ?_⟩
    simpa only [physicalTake_eq longHash n hn perm hp p s hr hb.2.1]
      using Run.drain run idle

/-- A single comparison covering the actual retained-memory kernels and every
    legal public builder/mixing lifecycle. The histories may use different
    fragmentation, flushing and discarded bytes, provided their committed
    messages and net precomputed mix effects agree. -/
theorem physical_reference_eq_avx2_eq_avx512 (longHash : AgaveConcrete.Message → Value)
    {p1 p8 p16 : Store} {s1 s8 s16 : Impl} {r : AgaveMixed.Spec}
    (trace1 : Run longHash 1 (by decide) AgaveLattice.labels p1 s1 r)
    (trace8 : Run longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8 r)
    (trace16 : Run longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16 r)
    (idle : r.active = none) :
    let referenceResult := (physicalTake longHash 1 (by decide) AgaveLattice.labels p1 s1).1
    let avx2Result := (physicalTake longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8).1
    let avx512Result := (physicalTake longHash 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16).1
    referenceResult = avx2Result ∧ avx2Result = avx512Result := by
  dsimp only
  rw [observational_equivalence longHash 1 (by decide) (by decide) _ reference_isTranspose trace1 idle,
    observational_equivalence longHash 8 (by decide) (by decide) _ AgaveLattice.avx2_isTranspose trace8 idle,
    observational_equivalence longHash 16 (by decide) (by decide) _ AgaveLattice.avx512_isTranspose trace16 idle]
  exact ⟨rfl, rfl⟩

/-- Any public observation derived from the returned LtHash also agrees. -/
theorem returned_observable_equivalence {α : Type} (observe : Value → α)
    (longHash : AgaveConcrete.Message → Value)
    {p1 p8 p16 : Store} {s1 s8 s16 : Impl} {r : AgaveMixed.Spec}
    (trace1 : Run longHash 1 (by decide) AgaveLattice.labels p1 s1 r)
    (trace8 : Run longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8 r)
    (trace16 : Run longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16 r)
    (idle : r.active = none) :
    observe (physicalTake longHash 1 (by decide) AgaveLattice.labels p1 s1).1 =
      observe (physicalTake longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8).1 ∧
    observe (physicalTake longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8).1 =
      observe (physicalTake longHash 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16).1 := by
  have h := physical_reference_eq_avx2_eq_avx512 longHash trace1 trace8 trace16 idle
  exact ⟨congrArg observe h.1, congrArg observe h.2⟩

#print axioms run_simulates
#print axioms run_lift
/-- info: 'AgavePhysicalMixed.physical_reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physical_reference_eq_avx2_eq_avx512
/-- info: 'AgavePhysicalMixed.returned_observable_equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms returned_observable_equivalence

end AgavePhysicalMixed

