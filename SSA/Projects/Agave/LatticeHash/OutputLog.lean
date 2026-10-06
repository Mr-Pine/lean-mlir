/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.PhysicalMixed

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-!
The entire observable output stream of a synchronized public event sequence.
The events are chronological. Every drain records the LtHash actually returned
by the retained-memory implementation, then resets the accumulator for reuse.
The reference interpreter checks only public builder-borrow legality. All
staging and backend correctness facts are obtained from `PhysicalMixed`.
-/
namespace AgaveOutputLog

open AgaveStaging AgavePhysicalStaging

/-- The publicly available operations; `mix_out` abbreviates mixing the
    pointwise negation, as in `AgavePhysicalMixed.Run`. -/
inductive Event where
  | start
  | part (bytes : Message)
  | finish
  | drop
  | whole (bytes : Message)
  | mix_in (value : Value)
  | mix_out (value : Value)
  | drain

/-- A simple scalar public specification. Its only failure condition is an
    operation forbidden by an outstanding exclusive builder borrow (or a
    builder operation without such a borrow). -/
def specStep (hash : Message → Value) (event : Event)
    (state : AgaveMixed.Spec × List Value) : Option (AgaveMixed.Spec × List Value) :=
  let (r, out) := state
  match event, r.active with
  | .start, none => some ({ r with active := some [] }, out)
  | .part bytes, some m => some ({ r with active := some (m ++ bytes) }, out)
  | .finish, some m => some (⟨r.committed ++ [m], none, r.offset⟩, out)
  | .drop, some _ => some ({ r with active := none }, out)
  | .whole bytes, none => some (⟨r.committed ++ [bytes], none, r.offset⟩, out)
  | .mix_in x, none => some ({ r with offset := plus r.offset x }, out)
  | .mix_out x, none => some ({ r with offset := plus r.offset (AgaveMixed.neg x) }, out)
  | .drain, none => some (AgaveMixed.specInit, out ++ [AgaveMixed.expected hash r])
  | _, _ => none

def specEval (hash : Message → Value) (events : List Event) :
    Option (AgaveMixed.Spec × List Value) :=
  events.foldl (fun acc event => acc.bind (specStep hash event))
    (some (AgaveMixed.specInit, []))

theorem specEval_append (hash : Message → Value) (events : List Event) (e : Event) :
    specEval hash (events ++ [e]) = (specEval hash events).bind (specStep hash e) := by
  simp [specEval, List.foldl_append]

/-- A retained-memory execution carrying every actual return value of
    `take_lt_hash`. The output log never resets when the accumulator does. -/
inductive Run (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix) :
    List Event → Store → Impl → AgaveMixed.Spec → List Value → Prop
  | initial : Run longHash n hn perm [] initialStore init AgaveMixed.specInit []
  | start {events p s r out} (run : Run longHash n hn perm events p s r out)
      (idle : r.active = none) :
      Run longHash n hn perm (events ++ [.start]) p s { r with active := some [] } out
  | part {events p s r out} (run : Run longHash n hn perm events p s r out)
      (m part : Message) (active : r.active = some m) :
      Run longHash n hn perm (events ++ [.part part])
        (appendStore s.spilled p part) (physicalAppend p s part)
        { r with active := some (m ++ part) } out
  | finish {events p s r out} (run : Run longHash n hn perm events p s r out)
      (m : Message) (active : r.active = some m) :
      Run longHash n hn perm (events ++ [.finish])
        (commitStore n s.spilled p) (physicalCommit longHash n hn perm p s)
        ⟨r.committed ++ [m], none, r.offset⟩ out
  | drop {events p s r out} (run : Run longHash n hn perm events p s r out)
      (m : Message) (active : r.active = some m) :
      Run longHash n hn perm (events ++ [.drop])
        (discardStore p) (discard s) { r with active := none } out
  | whole {events p s r out} (run : Run longHash n hn perm events p s r out)
      (m : Message) (idle : r.active = none) :
      Run longHash n hn perm (events ++ [.whole m])
        (commitStore n (physicalAppend p s m).spilled (appendStore s.spilled p m))
        (physicalCommit longHash n hn perm (appendStore s.spilled p m) (physicalAppend p s m))
        ⟨r.committed ++ [m], none, r.offset⟩ out
  | mix_in {events p s r out} (run : Run longHash n hn perm events p s r out)
      (x : Value) (idle : r.active = none) :
      Run longHash n hn perm (events ++ [.mix_in x]) p (AgaveMixed.mixIn s x)
        { r with offset := plus r.offset x } out
  | mix_out {events p s r out} (run : Run longHash n hn perm events p s r out)
      (x : Value) (idle : r.active = none) :
      Run longHash n hn perm (events ++ [.mix_out x]) p (AgaveMixed.mixOut s x)
        { r with offset := plus r.offset (AgaveMixed.neg x) } out
  | drain {events p s r out} (run : Run longHash n hn perm events p s r out)
      (idle : r.active = none) :
      Run longHash n hn perm (events ++ [.drain]) (takeStore p)
        (physicalTake longHash n hn perm p s).2 AgaveMixed.specInit
        (out ++ [(physicalTake longHash n hn perm p s).1])

/-- Adding event labels and an output log imposes no new state invariant. -/
theorem erase (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix)
    {events : List Event} {p : Store} {s : Impl} {r : AgaveMixed.Spec} {out : List Value}
    (trace : Run longHash n hn perm events p s r out) :
    AgavePhysicalMixed.Run longHash n hn perm p s r := by
  induction trace with
  | initial => exact .initial
  | start _ idle ih => exact .start ih idle
  | part _ m part active ih => exact .part ih m part active
  | finish _ m active ih => exact .finish ih m active
  | drop _ m active ih => exact .drop ih m active
  | whole _ m idle ih => exact .whole ih m idle
  | mix_in _ x idle ih => exact .mix_in ih x idle
  | mix_out _ x idle ih => exact .mix_out ih x idle
  | drain _ idle ih => exact .drain ih idle

/-- Every actual returned value, not just the last observation, agrees with the
    scalar interpreter of the same chronological sequence of public events. -/
theorem run_refines_log (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {events : List Event} {p : Store} {s : Impl} {r : AgaveMixed.Spec} {out : List Value}
    (trace : Run longHash n hn perm events p s r out) :
    specEval (AgaveConcrete.hash longHash) events = some (r, out) := by
  induction trace with
  | initial => rfl
  | start _ idle ih => simp [specEval_append, ih, specStep, idle]
  | part _ m part active ih => simp [specEval_append, ih, specStep, active]
  | finish _ m active ih => simp [specEval_append, ih, specStep, active]
  | drop _ m active ih => simp [specEval_append, ih, specStep, active]
  | whole _ m idle ih => simp [specEval_append, ih, specStep, idle]
  | mix_in _ x idle ih => simp [specEval_append, ih, specStep, idle]
  | mix_out _ x idle ih => simp [specEval_append, ih, specStep, idle]
  | @drain events p s r out run idle ih =>
    have he := AgavePhysicalMixed.observational_equivalence longHash n hn hn16 perm hp
      (erase longHash n hn perm run) idle
    simpa [specEval_append, ih, specStep, idle, AgaveMixed.expected] using
      congrArg (fun v => some (AgaveMixed.specInit, out ++ [v])) he.symm

/-- Any two physical executions of the same public events have the same full
    output log. No end-of-trace idle condition is needed. -/
theorem logs_equal (longHash : AgaveConcrete.Message → Value)
    (n₁ n₂ : Nat) (h₁ : 0 < n₁) (h₂ : 0 < n₂) (h₁16 : n₁ ≤ 16) (h₂16 : n₂ ≤ 16)
    (perm₁ perm₂ : AgaveLattice.Matrix)
    (hp₁ : AgaveLattice.IsTranspose n₁ perm₁) (hp₂ : AgaveLattice.IsTranspose n₂ perm₂)
    {events : List Event} {p₁ p₂ : Store} {s₁ s₂ : Impl}
    {r₁ r₂ : AgaveMixed.Spec} {out₁ out₂ : List Value}
    (trace₁ : Run longHash n₁ h₁ perm₁ events p₁ s₁ r₁ out₁)
    (trace₂ : Run longHash n₂ h₂ perm₂ events p₂ s₂ r₂ out₂) : out₁ = out₂ := by
  have he := (run_refines_log longHash n₁ h₁ h₁16 perm₁ hp₁ trace₁).symm.trans
    (run_refines_log longHash n₂ h₂ h₂16 perm₂ hp₂ trace₂)
  exact congrArg Prod.snd (Option.some.inj he)

/-- The complete observable sequence of the reference, AVX2 and AVX512 paths
    agrees across arbitrary legal fragmentation, cancellation, mixing and reuse. -/
theorem reference_eq_avx2_eq_avx512 (longHash : AgaveConcrete.Message → Value)
    {events : List Event} {p1 p8 p16 : Store} {s1 s8 s16 : Impl}
    {r1 r8 r16 : AgaveMixed.Spec} {out1 out8 out16 : List Value}
    (trace1 : Run longHash 1 (by decide) AgaveLattice.labels events p1 s1 r1 out1)
    (trace8 : Run longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) events p8 s8 r8 out8)
    (trace16 : Run longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) events p16 s16 r16 out16) :
    out1 = out8 ∧ out8 = out16 := by
  exact ⟨logs_equal longHash 1 8 (by decide) (by decide) (by decide) (by decide)
      _ _ reference_isTranspose AgaveLattice.avx2_isTranspose trace1 trace8,
    logs_equal longHash 8 16 (by decide) (by decide) (by decide) (by decide)
      _ _ AgaveLattice.avx2_isTranspose AgaveLattice.avx512_isTranspose trace8 trace16⟩

/-- Every next operation accepted by the public scalar specification can be
    executed by the physical implementation, preserving the actual output log. -/
theorem step_lift (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {events : List Event} {p : Store} {s : Impl} {r : AgaveMixed.Spec} {out : List Value}
    (trace : Run longHash n hn perm events p s r out)
    (event : Event) {r' : AgaveMixed.Spec} {out' : List Value}
    (next : specStep (AgaveConcrete.hash longHash) event (r, out) = some (r', out')) :
    ∃ p' s', Run longHash n hn perm (events ++ [event]) p' s' r' out' := by
  cases event <;> cases ha : r.active <;>
    simp only [specStep, ha, Option.some.injEq, Prod.mk.injEq] at next
  case start.none =>
    rcases next with ⟨rfl, rfl⟩
    exact ⟨p, s, .start trace ha⟩
  case start.some m => contradiction
  case part.none bytes => contradiction
  case part.some bytes m =>
    rcases next with ⟨rfl, rfl⟩
    exact ⟨_, _, .part trace m bytes ha⟩
  case finish.none => contradiction
  case finish.some m =>
    rcases next with ⟨rfl, rfl⟩
    exact ⟨_, _, .finish trace m ha⟩
  case drop.none => contradiction
  case drop.some m =>
    rcases next with ⟨rfl, rfl⟩
    exact ⟨_, _, .drop trace m ha⟩
  case whole.none bytes =>
    rcases next with ⟨rfl, rfl⟩
    exact ⟨_, _, .whole trace bytes ha⟩
  case whole.some bytes m => contradiction
  case mix_in.none x =>
    rcases next with ⟨rfl, rfl⟩
    refine ⟨p, AgaveMixed.mixIn s x, ?_⟩
    simpa only [ha] using Run.mix_in trace x ha
  case mix_in.some x m => contradiction
  case mix_out.none x =>
    rcases next with ⟨rfl, rfl⟩
    refine ⟨p, AgaveMixed.mixOut s x, ?_⟩
    simpa only [ha] using Run.mix_out trace x ha
  case mix_out.some x m => contradiction
  case drain.none =>
    rcases next with ⟨rfl, rfl⟩
    have he := AgavePhysicalMixed.observational_equivalence longHash n hn hn16 perm hp
      (erase longHash n hn perm trace) ha
    refine ⟨takeStore p, (physicalTake longHash n hn perm p s).2, ?_⟩
    simpa only [he, AgaveMixed.expected] using Run.drain trace ha
  case drain.some m => contradiction

/-- Nonvacuity: every legal scalar event sequence has an actual retained-memory
    execution, with exactly the outputs computed by the scalar specification. -/
theorem specEval_lift (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    (events : List Event) {r : AgaveMixed.Spec} {out : List Value}
    (legal : specEval (AgaveConcrete.hash longHash) events = some (r, out)) :
    ∃ p s, Run longHash n hn perm events p s r out := by
  have aux : ∀ (rev : List Event) {r : AgaveMixed.Spec} {out : List Value},
      specEval (AgaveConcrete.hash longHash) rev.reverse = some (r, out) →
        ∃ p s, Run longHash n hn perm rev.reverse p s r out := by
    intro rev
    induction rev with
    | nil =>
      intro r out legal
      simp only [List.reverse_nil, specEval, List.foldl_nil,
        Option.some.injEq, Prod.mk.injEq] at legal
      rcases legal with ⟨rfl, rfl⟩
      exact ⟨_, _, .initial⟩
    | cons event rev ih =>
      intro r out legal
      simp only [List.reverse_cons] at legal ⊢
      rw [specEval_append] at legal
      cases he : specEval (AgaveConcrete.hash longHash) rev.reverse with
      | none => simp [he] at legal
      | some state =>
        rcases state with ⟨r0, out0⟩
        have hl : specStep (AgaveConcrete.hash longHash) event (r0, out0) = some (r, out) := by
          simpa only [he, Option.bind_some] using legal
        rcases ih he with ⟨p, s, trace⟩
        exact step_lift longHash n hn hn16 perm hp trace event hl
  simpa only [List.reverse_reverse] using
    aux events.reverse (by simpa only [List.reverse_reverse] using legal)

/-- A scalar legal trace has executions on all three concrete paths with the
    same complete output log; callers supply no backend or buffer invariant. -/
theorem every_legal_trace (longHash : AgaveConcrete.Message → Value)
    (events : List Event) {r : AgaveMixed.Spec} {out : List Value}
    (legal : specEval (AgaveConcrete.hash longHash) events = some (r, out)) :
    (∃ p s, Run longHash 1 (by decide) AgaveLattice.labels events p s r out) ∧
    (∃ p s, Run longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) events p s r out) ∧
    (∃ p s, Run longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) events p s r out) := by
  exact ⟨specEval_lift longHash 1 (by decide) (by decide)
      _ reference_isTranspose events legal,
    specEval_lift longHash 8 (by decide) (by decide)
      _ AgaveLattice.avx2_isTranspose events legal,
    specEval_lift longHash 16 (by decide) (by decide)
      _ AgaveLattice.avx512_isTranspose events legal⟩

/-- info: 'AgaveOutputLog.reference_eq_avx2_eq_avx512' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_eq_avx2_eq_avx512
/-- info: 'AgaveOutputLog.every_legal_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms every_legal_trace

end AgaveOutputLog
