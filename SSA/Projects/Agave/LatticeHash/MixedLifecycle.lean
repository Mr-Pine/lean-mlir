/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Equivalence

/-!
Extension of the hand-written staging model with explicit public mixing events.
`mixIn` is the BatchLtHash accumulator update. `mixOut` models LtHash::mix_out
algebraically; BatchLtHash itself exposes only mix_in, so on BatchLtHash it is
realized by mixing in the pointwise negative of a precomputed hash.
The trace enforces the exclusive builder borrow at public mixing events.
The offset is the net pointwise BitVec16 effect since the most recent take.
-/
namespace AgaveMixed
open AgaveStaging

def neg (x : Value) : Value := fun i => -x i

def mixIn (s : Impl) (x : Value) : Impl := { s with acc := plus s.acc x }
def mixOut (s : Impl) (x : Value) : Impl := { s with acc := fun i => s.acc i - x i }

theorem mixOut_eq_mixIn_neg (s : Impl) (x : Value) :
    mixOut s x = mixIn s (neg x) := by
  have he : (fun i => s.acc i - x i) = plus s.acc (neg x) := by
    funext i
    exact BitVec.sub_eq_add_neg _ _
  simp only [mixOut, mixIn, he]

structure Spec where
  committed : List Message
  active : Option Message
  offset : Value

def specInit : Spec := ⟨[], none, zero⟩
def expected (hash : Message → Value) (r : Spec) : Value :=
  plus (scalar hash r.committed) r.offset

def Refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec) : Prop :=
  Bounds w s ∧ CurrentMatches s r.active ∧ Denote hash s = expected hash r

theorem plus_swap (a b c : Value) : plus (plus a b) c = plus (plus a c) b := by
  rw [plus_assoc, plus_comm b c, ← plus_assoc]

theorem init_refines (hash : Message → Value) (w : Nat) (hw : 0 < w) :
    Refines hash w init specInit := by
  simp [Refines, expected, specInit, Bounds, PendingOK, init, CurrentMatches, Clean, Denote, hw]

theorem begin_refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec)
    (h : Refines hash w s r) (hi : r.active = none) :
    Refines hash w s { r with active := some [] } := by
  rcases h with ⟨hb, hc, hd⟩
  rw [hi] at hc
  change Clean s at hc
  exact ⟨hb, by simp [CurrentMatches, hc.1, hc.2], hd⟩

theorem append_refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec)
    (m p : Message) (h : Refines hash w s r) (hi : r.active = some m) :
    Refines hash w (append s p) { r with active := some (m ++ p) } := by
  rcases h with ⟨hb, hc, hd⟩
  rw [hi] at hc
  exact ⟨append_bounds s w p hb, append_matches s m p hc, (append_denote hash s p).trans hd⟩

theorem commit_refines (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (r : Spec) (m : Message) (hw : 0 < w)
    (h : Refines hash w s r) (hi : r.active = some m) :
    Refines hash w (commit hash w b s) ⟨r.committed ++ [m], none, r.offset⟩ := by
  rcases h with ⟨hb, hc, hd⟩
  rw [hi] at hc
  refine ⟨commit_bounds hash w b s hw hb, commit_clean hash w b s m hc, ?_⟩
  rw [commit_denote hash w b s m hb hc, hd]
  simp only [expected, scalar_append, scalar_singleton]
  exact plus_swap _ _ _

theorem discard_refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec)
    (h : Refines hash w s r) :
    Refines hash w (discard s) { r with active := none } :=
  ⟨discard_bounds s w h.1, discard_clean s, h.2.2⟩

theorem addMessage_refines (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (r : Spec) (m : Message) (hw : 0 < w)
    (h : Refines hash w s r) (hi : r.active = none) :
    Refines hash w (addMessage hash w b s m) ⟨r.committed ++ [m], none, r.offset⟩ := by
  have hb := begin_refines hash w s r h hi
  have ha := append_refines hash w s { r with active := some [] } [] m hb rfl
  simpa [addMessage] using commit_refines hash w b (append s m)
    { r with active := some ([] ++ m) } ([] ++ m) hw ha rfl

theorem mixIn_refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec)
    (x : Value) (h : Refines hash w s r) :
    Refines hash w (mixIn s x) { r with offset := plus r.offset x } := by
  refine ⟨h.1, ?_, ?_⟩
  · cases ha : r.active <;> cases hs : s.spilled <;>
      simpa [CurrentMatches, Clean, mixIn, ha, hs] using h.2.1
  · change plus (plus s.acc x) (scalar hash s.pending) =
      plus (scalar hash r.committed) (plus r.offset x)
    rw [plus_swap s.acc x, ← plus_assoc]
    exact congrArg (fun v => plus v x) h.2.2

theorem mixOut_refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec)
    (x : Value) (h : Refines hash w s r) :
    Refines hash w (mixOut s x) { r with offset := plus r.offset (neg x) } := by
  rw [mixOut_eq_mixIn_neg]
  exact mixIn_refines hash w s r (neg x) h

theorem take_correct (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (r : Spec) (hw : 0 < w) (h : Refines hash w s r)
    (hi : r.active = none) :
    (take hash w b s).1 = expected hash r ∧
    Refines hash w (take hash w b s).2 specInit := by
  rcases h with ⟨hb, hc, hd⟩
  rw [hi] at hc
  change Clean s at hc
  unfold take
  split
  next he =>
    have hp : s.pending = [] := by simpa using he
    constructor
    · simpa [Denote, hp] using hd
    · simpa [Refines, expected, specInit, CurrentMatches, Denote, Bounds, Clean, PendingOK, hp]
        using And.intro hb (And.intro hc (show zero = zero from rfl))
  next he =>
    have hf : Clean (flush hash w b s) := flush_clean _ _ _ _ hc
    have hd' := flush_denote hash w b s hb.2.1
    have hfb := flush_bounds hash w b s hw hb.2.2
    have hp : (flush hash w b s).pending = [] := by unfold flush; split <;> rfl
    constructor
    · simpa [Denote, hp] using hd'.trans hd
    · simpa [Refines, expected, specInit, CurrentMatches, Denote, Bounds, Clean, PendingOK, hp]
        using And.intro hfb (And.intro hf (show zero = zero from rfl))

/-- Legal finite lifecycle traces, allowing arbitrary precomputed hash values.
A take resets both committed messages and the net mix offset for reuse. -/
inductive Run (hash : Message → Value) (w : Nat) (b : Backend hash w) : Impl → Spec → Prop
  | initial : Run hash w b init specInit
  | start {s r} (run : Run hash w b s r) (idle : r.active = none) :
      Run hash w b s { r with active := some [] }
  | part {s r} (run : Run hash w b s r) (m p : Message) (active : r.active = some m) :
      Run hash w b (append s p) { r with active := some (m ++ p) }
  | finish {s r} (run : Run hash w b s r) (m : Message) (active : r.active = some m) :
      Run hash w b (commit hash w b s) ⟨r.committed ++ [m], none, r.offset⟩
  | drop {s r} (run : Run hash w b s r) (m : Message) (active : r.active = some m) :
      Run hash w b (discard s) { r with active := none }
  | whole {s r} (run : Run hash w b s r) (m : Message) (idle : r.active = none) :
      Run hash w b (addMessage hash w b s m) ⟨r.committed ++ [m], none, r.offset⟩
  | mix_in {s r} (run : Run hash w b s r) (x : Value) (idle : r.active = none) :
      Run hash w b (mixIn s x) { r with offset := plus r.offset x }
  | mix_out {s r} (run : Run hash w b s r) (x : Value) (idle : r.active = none) :
      Run hash w b (mixOut s x) { r with offset := plus r.offset (neg x) }
  | drain {s r} (run : Run hash w b s r) (idle : r.active = none) :
      Run hash w b (take hash w b s).2 specInit

theorem run_refines (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (hw : 0 < w) {s : Impl} {r : Spec} (run : Run hash w b s r) : Refines hash w s r := by
  induction run with
  | initial => exact init_refines hash w hw
  | start _ idle ih => exact begin_refines hash w _ _ ih idle
  | part _ m p active ih => exact append_refines hash w _ _ m p ih active
  | finish _ m active ih => exact commit_refines hash w b _ _ m hw ih active
  | drop _ _ _ ih => exact discard_refines hash w _ _ ih
  | whole _ m idle ih => exact addMessage_refines hash w b _ _ m hw ih idle
  | mix_in _ x _ ih => exact mixIn_refines hash w _ _ x ih
  | mix_out _ x _ ih => exact mixOut_refines hash w _ _ x ih
  | drain _ idle ih => exact (take_correct hash w b _ _ hw ih idle).2

/-- Each idle observation is the scalar message sum plus all net mix effects. -/
theorem observational_equivalence (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (hw : 0 < w) {s : Impl} {r : Spec} (run : Run hash w b s r) (idle : r.active = none) :
    (take hash w b s).1 = plus (scalar hash r.committed) r.offset :=
  (take_correct hash w b s r hw (run_refines hash w b hw run) idle).1

/-- Pointwise statement makes the wraparound 16-bit arithmetic explicit. -/
theorem observational_equivalence_coordinate (hash : Message → Value) (w : Nat)
    (b : Backend hash w) (hw : 0 < w) {s : Impl} {r : Spec}
    (run : Run hash w b s r) (idle : r.active = none) (i : Fin 1024) :
    (take hash w b s).1 i = scalar hash r.committed i + r.offset i := by
  rw [observational_equivalence hash w b hw run idle]
  rfl

/-- The concrete reference, AVX2 and AVX512 kernels give identical observations
for the same committed messages and net mix effects, including arbitrary drains,
reuses, fragmentations, discarded builders and precomputed values. -/
theorem reference_eq_avx2_eq_avx512
    (longHash : AgaveConcrete.Message → AgaveConcrete.Value)
    {s1 s8 s16 : Impl} {r : Spec}
    (trace1 : Run (AgaveConcrete.hash longHash) 1 (AgaveConcrete.reference longHash) s1 r)
    (trace8 : Run (AgaveConcrete.hash longHash) 8 (AgaveConcrete.avx2 longHash) s8 r)
    (trace16 : Run (AgaveConcrete.hash longHash) 16 (AgaveConcrete.avx512 longHash) s16 r)
    (idle : r.active = none) :
    (take (AgaveConcrete.hash longHash) 1 (AgaveConcrete.reference longHash) s1).1 =
      (take (AgaveConcrete.hash longHash) 8 (AgaveConcrete.avx2 longHash) s8).1 ∧
    (take (AgaveConcrete.hash longHash) 8 (AgaveConcrete.avx2 longHash) s8).1 =
      (take (AgaveConcrete.hash longHash) 16 (AgaveConcrete.avx512 longHash) s16).1 := by
  rw [observational_equivalence _ _ _ (by decide) trace1 idle,
    observational_equivalence _ _ _ (by decide) trace8 idle,
    observational_equivalence _ _ _ (by decide) trace16 idle]
  exact ⟨rfl, rfl⟩

/-- Equality is preserved by every public observation derived solely from the
    returned LtHash value, including checksum and display formatting. -/
theorem returned_observable_equivalence {α : Type}
    (observe : Value → α)
    (longHash : AgaveConcrete.Message → AgaveConcrete.Value)
    {s1 s8 s16 : Impl} {r : Spec}
    (trace1 : Run (AgaveConcrete.hash longHash) 1 (AgaveConcrete.reference longHash) s1 r)
    (trace8 : Run (AgaveConcrete.hash longHash) 8 (AgaveConcrete.avx2 longHash) s8 r)
    (trace16 : Run (AgaveConcrete.hash longHash) 16 (AgaveConcrete.avx512 longHash) s16 r)
    (idle : r.active = none) :
    observe (take (AgaveConcrete.hash longHash) 1 (AgaveConcrete.reference longHash) s1).1 =
      observe (take (AgaveConcrete.hash longHash) 8 (AgaveConcrete.avx2 longHash) s8).1 ∧
    observe (take (AgaveConcrete.hash longHash) 8 (AgaveConcrete.avx2 longHash) s8).1 =
      observe (take (AgaveConcrete.hash longHash) 16 (AgaveConcrete.avx512 longHash) s16).1 := by
  have h := reference_eq_avx2_eq_avx512 longHash trace1 trace8 trace16 idle
  exact ⟨congrArg observe h.1, congrArg observe h.2⟩

end AgaveMixed
