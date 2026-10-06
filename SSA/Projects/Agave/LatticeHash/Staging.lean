/- Released under Apache 2.0 license as described in the file LICENSE. -/
import Std
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-!
Manual semantic model of lattice-hash/src/batch.rs, at message level.
The implementation relation abstracts correctly padded lane storage to message
bytes; physical stale lanes are modeled separately below for the leaked-guard
counterexample. The batch kernel's functional contract is an explicit argument.
No Rust extraction, compiler, BLAKE3, or target-instruction correctness is assumed
as a Lean axiom or proved by this file.
-/
namespace AgaveStaging

abbrev Message := List UInt8
abbrev Value := Fin 1024 → BitVec 16

def zero : Value := fun _ => 0

def plus (x y : Value) : Value := fun i => x i + y i

theorem plus_assoc (a b c : Value) : plus (plus a b) c = plus a (plus b c) := by
  funext i
  exact BitVec.add_assoc _ _ _

theorem plus_comm (a b : Value) : plus a b = plus b a := by
  funext i
  exact BitVec.add_comm _ _

@[simp] theorem plus_zero (a : Value) : plus a zero = a := by
  funext i
  simp [plus, zero]

@[simp] theorem zero_plus (a : Value) : plus zero a = a := by
  funext i
  simp [plus, zero]

def scalar (hash : Message → Value) : List Message → Value
  | [] => zero
  | m :: ms => plus (hash m) (scalar hash ms)

@[simp] theorem scalar_nil (hash : Message → Value) : scalar hash [] = zero := rfl

@[simp] theorem scalar_singleton (hash : Message → Value) (m : Message) :
    scalar hash [m] = hash m := by simp [scalar]

theorem scalar_append (hash : Message → Value) (xs ys : List Message) :
    scalar hash (xs ++ ys) = plus (scalar hash xs) (scalar hash ys) := by
  induction xs with
  | nil => simp [scalar]
  | cons x xs ih => simp [scalar, ih, plus_assoc]

-- The implementation uses a left fold; it agrees with the scalar list oracle.
theorem scalar_foldl (hash : Message → Value) (ms : List Message) (a : Value) :
    ms.foldl (fun z m => plus z (hash m)) a = plus a (scalar hash ms) := by
  induction ms generalizing a with
  | nil => simp
  | cons m ms ih => simp [List.foldl_cons, ih, scalar, plus_assoc]

structure Impl where
  acc : Value
  pending : List Message
  staged : Message
  serial : Message
  spilled : Bool

structure Spec where
  committed : List Message
  active : Option Message

-- Dirty serial_hasher contents and queued messages are deliberately unrestricted.
def Clean (s : Impl) : Prop := s.staged = [] ∧ s.spilled = false

def PendingOK (s : Impl) : Prop := ∀ m ∈ s.pending, m.length ≤ 1024

def Bounds (w : Nat) (s : Impl) : Prop :=
  s.pending.length < w ∧ PendingOK s ∧ s.staged.length ≤ 1024

def CurrentMatches (s : Impl) : Option Message → Prop
  | none => Clean s
  | some m => if s.spilled then s.staged = [] ∧ s.serial = m else s.staged = m

def Denote (hash : Message → Value) (s : Impl) : Value :=
  plus s.acc (scalar hash s.pending)

def Refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec) : Prop :=
  Bounds w s ∧ CurrentMatches s r.active ∧ Denote hash s = scalar hash r.committed

-- Correctness is required only for full, single-chunk batches. This is the
-- interface to a separately checked SIMD kernel proof, not a hidden axiom.
structure Backend (hash : Message → Value) (w : Nat) where
  run : List Message → Value → Value
  correct : ∀ (ms : List Message) (a : Value), ms.length = w →
    (∀ m ∈ ms, m.length ≤ 1024) → run ms a = plus a (scalar hash ms)

def init : Impl := ⟨zero, [], [], [], false⟩
def specInit : Spec := ⟨[], none⟩

def spill (s : Impl) : Impl :=
  { s with staged := [], serial := s.staged, spilled := true }

def append (s : Impl) (p : Message) : Impl :=
  if s.spilled then { s with serial := s.serial ++ p }
  else if s.staged.length + p.length ≤ 1024 then { s with staged := s.staged ++ p }
  else { spill s with serial := s.staged ++ p }

def discard (s : Impl) : Impl := { s with staged := [], spilled := false }

-- A scalar flush repeatedly resets the shared serial_hasher and leaves its
-- last message behind. A full SIMD flush leaves that hasher unchanged.
def flush (hash : Message → Value) (w : Nat) (b : Backend hash w) (s : Impl) : Impl :=
  if 1 < w ∧ s.pending.length = w then
    { s with acc := b.run s.pending s.acc, pending := [] }
  else
    { s with acc := plus s.acc (scalar hash s.pending), pending := [], serial := s.pending.getLast?.getD s.serial }

def finishLane (s : Impl) : Impl :=
  { s with pending := s.pending ++ [s.staged], staged := [] }

def commit (hash : Message → Value) (w : Nat) (b : Backend hash w) (s : Impl) : Impl :=
  if s.spilled then { s with acc := plus s.acc (hash s.serial), spilled := false }
  else
    let t := finishLane s
    if t.pending.length = w then flush hash w b t else t

-- Like the release build, the operation itself does not clear unfinished state.
-- Its refinement theorem requires Clean, supplied by the legal lifecycle.
def take (hash : Message → Value) (w : Nat) (b : Backend hash w) (s : Impl) : Value × Impl :=
  let t := if s.pending.isEmpty then s else flush hash w b s
  (t.acc, { t with acc := zero })

@[simp] theorem clean_matches (s : Impl) : CurrentMatches s none ↔ Clean s := Iff.rfl

-- In particular, the old serial hasher value is not part of the clean boundary.
theorem clean_ignores_serial (s : Impl) (old : Message) :
    Clean { s with serial := old } ↔ Clean s := Iff.rfl

theorem spill_copies_current (s : Impl) :
    (spill s).serial = s.staged ∧ (spill s).staged = [] ∧ (spill s).spilled = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem append_matches (s : Impl) (m p : Message)
    (hm : CurrentMatches s (some m)) :
    CurrentMatches (append s p) (some (m ++ p)) := by
  unfold CurrentMatches at hm ⊢
  unfold append
  cases hs : s.spilled <;> simp_all [spill]
  split <;> simp_all

theorem append_bounds (s : Impl) (w : Nat) (p : Message) (h : Bounds w s) :
    Bounds w (append s p) := by
  rcases h with ⟨hn, hp, hl⟩
  unfold append
  cases hs : s.spilled <;> simp_all [Bounds, PendingOK, spill]
  split <;> simp_all [Bounds, PendingOK, spill, List.length_append]

theorem append_denote (hash : Message → Value) (s : Impl) (p : Message) :
    Denote hash (append s p) = Denote hash s := by
  unfold append
  cases s.spilled <;> simp [Denote, spill]
  split <;> rfl

theorem discard_clean (s : Impl) : Clean (discard s) := ⟨rfl, rfl⟩

theorem discard_bounds (s : Impl) (w : Nat) (h : Bounds w s) :
    Bounds w (discard s) := by
  exact ⟨h.1, h.2.1, by simp [discard]⟩

theorem discard_denote (hash : Message → Value) (s : Impl) :
    Denote hash (discard s) = Denote hash s := rfl

theorem flush_denote (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (h : PendingOK s) :
    Denote hash (flush hash w b s) = Denote hash s := by
  unfold flush
  split
  next hc => simp [Denote, b.correct _ _ hc.2 h]
  next => simp [Denote]

theorem flush_clean (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (h : Clean s) : Clean (flush hash w b s) := by
  unfold flush
  split <;> exact h

theorem flush_bounds (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (hw : 0 < w) (hl : s.staged.length ≤ 1024) :
    Bounds w (flush hash w b s) := by
  unfold flush
  split <;> simp [Bounds, PendingOK, hw, hl]

theorem finishLane_pendingOK (s : Impl) (hp : PendingOK s)
    (hl : s.staged.length ≤ 1024) : PendingOK (finishLane s) := by
  intro m hm
  simp only [finishLane, List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | rfl
  · exact hp m hm
  · exact hl

theorem commit_clean (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (m : Message) (hm : CurrentMatches s (some m)) :
    Clean (commit hash w b s) := by
  unfold commit
  cases hs : s.spilled
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · apply flush_clean
      exact ⟨rfl, hs⟩
    · exact ⟨rfl, hs⟩
  · simp only [↓reduceIte]
    simp [CurrentMatches, hs] at hm
    exact ⟨hm.1, rfl⟩

theorem commit_bounds (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (hw : 0 < w) (h : Bounds w s) :
    Bounds w (commit hash w b s) := by
  rcases h with ⟨hn, hp, hl⟩
  unfold commit
  cases hs : s.spilled
  · simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · apply flush_bounds _ _ _ _ hw
      simp [finishLane]
    · rename_i hne
      refine ⟨?_, finishLane_pendingOK s hp hl, by simp [finishLane]⟩
      simp only [finishLane, List.length_append, List.length_singleton] at hne ⊢
      omega
  · exact ⟨hn, hp, hl⟩

theorem commit_denote (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (m : Message) (h : Bounds w s) (hm : CurrentMatches s (some m)) :
    Denote hash (commit hash w b s) = plus (Denote hash s) (hash m) := by
  unfold commit
  cases hs : s.spilled
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hm' : s.staged = m := by simpa [CurrentMatches, hs] using hm
    have hf : Denote hash (finishLane s) = plus (Denote hash s) (hash m) := by
      simp [Denote, finishLane, scalar_append, hm', plus_assoc]
    split
    · rw [flush_denote _ _ _ _ (finishLane_pendingOK s h.2.1 h.2.2)]
      exact hf
    · exact hf
  · simp [CurrentMatches, hs] at hm
    simp only [↓reduceIte, Denote, hm.2]
    rw [plus_assoc, plus_comm (hash m), ← plus_assoc]

theorem init_refines (hash : Message → Value) (w : Nat) (hw : 0 < w) :
    Refines hash w init specInit := by
  simp [Refines, Bounds, PendingOK, init, specInit, CurrentMatches, Clean, Denote, hw]

-- Taking observes the scalar result and preserves the exact weak boundary.
theorem take_correct (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (r : Spec) (hw : 0 < w) (h : Refines hash w s r)
    (hi : r.active = none) :
    (take hash w b s).1 = scalar hash r.committed ∧
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
    · simpa [Refines, specInit, CurrentMatches, Denote, Bounds, Clean, PendingOK, hp] using And.intro hb (And.intro hc (show zero = zero from rfl))
  next he =>
    have hf : Clean (flush hash w b s) := flush_clean _ _ _ _ hc
    have hd' := flush_denote hash w b s hb.2.1
    have hfb := flush_bounds hash w b s hw hb.2.2
    have hp : (flush hash w b s).pending = [] := by unfold flush; split <;> rfl
    constructor
    · simpa [Denote, hp] using hd'.trans hd
    · simpa [Refines, specInit, CurrentMatches, Denote, Bounds, Clean, PendingOK, hp] using And.intro hfb (And.intro hf (show zero = zero from rfl))


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
    Refines hash w (commit hash w b s) ⟨r.committed ++ [m], none⟩ := by
  rcases h with ⟨hb, hc, hd⟩
  rw [hi] at hc
  refine ⟨commit_bounds hash w b s hw hb, commit_clean hash w b s m hc, ?_⟩
  rw [commit_denote hash w b s m hb hc, hd, scalar_append, scalar_singleton]

theorem discard_refines (hash : Message → Value) (w : Nat) (s : Impl) (r : Spec)
    (h : Refines hash w s r) :
    Refines hash w (discard s) { r with active := none } := by
  exact ⟨discard_bounds s w h.1, discard_clean s, h.2.2⟩

def addMessage (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (m : Message) : Impl := commit hash w b (append s m)

theorem addMessage_refines (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (s : Impl) (r : Spec) (m : Message) (hw : 0 < w)
    (h : Refines hash w s r) (hi : r.active = none) :
    Refines hash w (addMessage hash w b s m) ⟨r.committed ++ [m], none⟩ := by
  have hb := begin_refines hash w s r h hi
  have ha := append_refines hash w s { r with active := some [] } [] m hb rfl
  simpa [addMessage] using commit_refines hash w b (append s m)
    { r with active := some ([] ++ m) } ([] ++ m) hw ha rfl

/- Legal public traces. The builder's exclusive borrow is represented by the
active message; the finish constructor commits before forgetting its own guard.
There is deliberately no constructor for a client forgetting an unfinished guard.
Drop may discard an empty, staged, or spilled message. Take resets the oracle's
committed list, so an arbitrary number of accumulator reuses is covered. -/
inductive Run (hash : Message → Value) (w : Nat) (b : Backend hash w) : Impl → Spec → Prop
  | initial : Run hash w b init specInit
  | start {s r} (run : Run hash w b s r) (idle : r.active = none) :
      Run hash w b s { r with active := some [] }
  | part {s r} (run : Run hash w b s r) (m p : Message) (active : r.active = some m) :
      Run hash w b (append s p) { r with active := some (m ++ p) }
  | finish {s r} (run : Run hash w b s r) (m : Message) (active : r.active = some m) :
      Run hash w b (commit hash w b s) ⟨r.committed ++ [m], none⟩
  | drop {s r} (run : Run hash w b s r) (m : Message) (active : r.active = some m) :
      Run hash w b (discard s) { r with active := none }
  | whole {s r} (run : Run hash w b s r) (m : Message) (idle : r.active = none) :
      Run hash w b (addMessage hash w b s m) ⟨r.committed ++ [m], none⟩
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
  | drain _ idle ih => exact (take_correct hash w b _ _ hw ih idle).2

-- Main theorem: every idle observation in every legal finite trace agrees
-- coordinate-for-coordinate with scalar list-of-messages accumulation.
theorem observational_equivalence (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (hw : 0 < w) {s : Impl} {r : Spec} (run : Run hash w b s r) (idle : r.active = none) :
    (take hash w b s).1 = scalar hash r.committed :=
  (take_correct hash w b s r hw (run_refines hash w b hw run) idle).1

theorem observational_equivalence_widths_1_8_16 (hash : Message → Value) (w : Nat)
    (b : Backend hash w) (hw : w = 1 ∨ w = 8 ∨ w = 16)
    {s : Impl} {r : Spec} (run : Run hash w b s r) (idle : r.active = none) :
    (take hash w b s).1 = scalar hash r.committed :=
  observational_equivalence hash w b (by omega) run idle

-- Staging's cursor/counter arithmetic stays within the actual allocation.
-- The counter reaches w only transiently: commit immediately flushes it.
theorem staging_access_bounds (w : Nat) (s : Impl) (hw : w = 1 ∨ w = 8 ∨ w = 16)
    (hb : Bounds w s) :
    s.pending.length < 16 ∧ s.pending.length + 1 ≤ w ∧
    s.staged.length ≤ 1024 := by
  rcases hb with ⟨hc, _, hl⟩
  omega

def paddedLength (len : Nat) : Nat := ((max 1 len + 63) / 64) * 64

theorem padding_bounds (len : Nat) (h : len ≤ 1024) :
    len ≤ paddedLength len ∧ 64 ≤ paddedLength len ∧ paddedLength len ≤ 1024 := by
  unfold paddedLength
  omega

theorem empty_has_one_block : paddedLength 0 = 64 := by decide

theorem exact_chunk_stays_in_lane : paddedLength 1024 = 1024 := by decide

-- Rust's saturating_add cannot turn an overflowing append into a fitting one.
-- The usual usize maxima are both strictly larger than CHUNK_LEN.
theorem saturating_append_guard (current incoming usizeMax : Nat)
    (hmax : 1024 < usizeMax) :
    min (current + incoming) usizeMax ≤ 1024 ↔ current + incoming ≤ 1024 := by
  omega

#print axioms observational_equivalence_widths_1_8_16

end AgaveStaging
