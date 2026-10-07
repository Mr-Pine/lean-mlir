import SSA.Projects.Agave.Ed25519.Proof.Initializedness.Observations

/-! A byte-mask sufficient condition for independence from allocator contents.
This is an abstract, fixed-address trace theorem. No connection between these
traces and the complete RIR interpreter is asserted in this module. -/
namespace Agave.Ed25519.Initializedness.ShadowTrace

abbrev Bytes := Nat → BitVec 8
abbrev Mask := Nat → Prop

def InRange (base count address : Nat) : Prop :=
  base ≤ address ∧ address < base + count

/-- `clear` starts a fresh lifetime with arbitrary bytes and no defined bytes.
A `write` value must already be defined. `copy` transports the source mask.
Only `read` produces a computational byte observation. -/
inductive Event where
  | clear (base count : Nat)
  | write (base count : Nat) (value : Bytes)
  | copy (destination source count : Nat)
  | read (base count : Nat)

noncomputable def maskStep (event : Event) (defined : Mask) : Mask := by
  classical
  exact match event with
    | .clear base count => fun a => defined a ∧ ¬ InRange base count a
    | .write base count _ => fun a => InRange base count a ∨ defined a
    | .copy dst src count => fun a =>
      if InRange dst count a then defined (src + (a - dst)) else defined a
    | .read _ _ => defined

noncomputable def memoryStep (fresh : Bytes) (event : Event) (memory : Bytes) : Bytes := by
  classical
  exact match event with
    | .clear base count => fun a => if InRange base count a then fresh a else memory a
    | .write base count value => fun a =>
      if InRange base count a then value (a - base) else memory a
    | .copy dst src count => fun a =>
      if InRange dst count a then memory (src + (a - dst)) else memory a
    | .read _ _ => memory

def Agrees (defined : Mask) (left right : Bytes) : Prop :=
  ∀ a, defined a → left a = right a

def ReadDefined (defined : Mask) (event : Event) : Prop :=
  match event with
    | .read base count => ∀ a, InRange base count a → defined a
    | _ => True

def observe (event : Event) (memory : Bytes) : Option (List (BitVec 8)) :=
  match event with
    | .read base count => some (List.ofFn (fun i : Fin count => memory (base + i.val)))
    | _ => none

/-- Copied undefined bytes may remain different; agreement follows exactly the
transported mask, including after fresh allocation or lifetime reset. -/
theorem step_agrees (fresh₁ fresh₂ left right : Bytes) (defined : Mask) (event : Event)
    (h : Agrees defined left right) :
    Agrees (maskStep event defined)
      (memoryStep fresh₁ event left) (memoryStep fresh₂ event right) := by
  classical
  cases event with
  | clear base count =>
    intro a ha
    have ha' : defined a ∧ ¬ InRange base count a := ha
    simpa only [memoryStep, ite_eq_right ha'.2] using h a ha'.1
  | write base count value =>
    intro a ha
    have ha' : InRange base count a ∨ defined a := ha
    by_cases hr : InRange base count a
    · simp only [memoryStep, ite_eq_left hr]
    · simpa only [memoryStep, ite_eq_right hr] using h a (ha'.resolve_left hr)
  | copy dst src count =>
    intro a ha
    by_cases hr : InRange dst count a
    · have hs : defined (src + (a - dst)) := by simpa only [maskStep, ite_eq_left hr] using ha
      simpa only [memoryStep, ite_eq_left hr] using h (src + (a - dst)) hs
    · have hs : defined a := by simpa only [maskStep, ite_eq_right hr] using ha
      simpa only [memoryStep, ite_eq_right hr] using h a hs
  | read base count => exact h

theorem observation_agrees (left right : Bytes) (defined : Mask) (event : Event)
    (h : Agrees defined left right) (hd : ReadDefined defined event) :
    observe event left = observe event right := by
  cases event with
  | clear => rfl
  | write => rfl
  | copy => rfl
  | read base count =>
    apply congrArg some
    apply congrArg List.ofFn
    funext i
    apply h
    apply hd
    exact ⟨by omega, by have := i.isLt; omega⟩

noncomputable def DefinedTrace (defined : Mask) : List Event → Prop
  | [] => True
  | event :: rest => ReadDefined defined event ∧ DefinedTrace (maskStep event defined) rest

noncomputable def observations (fresh memory : Bytes) : List Event → List (Option (List (BitVec 8)))
  | [] => []
  | event :: rest => observe event memory ::
      observations fresh (memoryStep fresh event memory) rest

/-- Exact residual sufficient condition at the byte-trace layer: every
computational read is defined. Initial and freshly allocated undefined bytes
may differ, and memcpy need not read exclusively defined bytes. -/
theorem defined_trace_observations_equal (events : List Event)
    (fresh₁ fresh₂ left right : Bytes) (defined : Mask)
    (ha : Agrees defined left right) (ht : DefinedTrace defined events) :
    observations fresh₁ left events = observations fresh₂ right events := by
  induction events generalizing left right defined with
  | nil => rfl
  | cons event rest ih =>
    exact congrArg₂ List.cons (observation_agrees left right defined event ha ht.1)
      (ih (memoryStep fresh₁ event left) (memoryStep fresh₂ event right)
        (maskStep event defined) (step_agrees fresh₁ fresh₂ left right defined event ha) ht.2)

end Agave.Ed25519.Initializedness.ShadowTrace
