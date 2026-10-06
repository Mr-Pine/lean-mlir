/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.Equivalence

/-!
Physical staging refinement for the manual Agave models.  The retained allocation
is genuinely finite: sixteen lanes, each of 1024 bytes.  Only the active width's
lanes are accessed.  `Store` has independent count, cursor and length metadata.
The separate `AgaveStaging.Impl` is a ghost abstraction, not the input from which
physical memory is reconstructed.  Every write below updates the retained bytes
in place; spilling, dropping and clearing preserve those bytes.
-/
namespace AgavePhysicalStaging

open AgaveStaging
abbrev Byte := AgaveConcrete.Byte
abbrev Memory := Fin 16 → Fin 1024 → Byte

structure Store where
  memory : Memory
  lengths : Fin 16 → Nat
  count : Nat
  curLen : Nat

/-- Extensions beyond the finite allocation are only for the kernel interface;
    the control theorem proves that its loads never use them. -/
def memoryAt (p : Store) (lane offset : Nat) : Byte :=
  if hl : lane < 16 then if hi : offset < 1024 then p.memory ⟨lane, hl⟩ ⟨offset, hi⟩ else 0 else 0

def lengthAt (p : Store) (lane : Nat) : Nat :=
  if hl : lane < 16 then p.lengths ⟨lane, hl⟩ else 0

def byte (m : Message) : Nat → Byte := AgaveConcrete.bytes (AgaveConcrete.toBytes m)

def initialStore : Store := ⟨fun _ _ => 0, fun _ => 0, 0, 0⟩

/-- The successful copy_from_slice; only its exact destination slice changes. -/
def copyPart (p : Store) (part : Message) : Store :=
  { p with
    memory := fun l i =>
      if l.val = p.count ∧ p.curLen ≤ i.val ∧ i.val < p.curLen + part.length
      then byte part (i.val - p.curLen) else p.memory l i
    curLen := p.curLen + part.length }

def discardStore (p : Store) : Store := { p with curLen := 0 }

def appendStore (spilled : Bool) (p : Store) (part : Message) : Store :=
  if spilled then p
  else if p.curLen + part.length ≤ 1024 then copyPart p part else discardStore p

/-- Exactly the final compression block is zeroed.  Later stale bytes survive. -/
def finishStore (p : Store) : Store :=
  { p with
    memory := fun l i =>
      if l.val = p.count ∧ p.curLen ≤ i.val ∧ i.val < AgaveStaging.paddedLength p.curLen
      then 0 else p.memory l i
    lengths := fun l => if l.val = p.count then p.curLen else p.lengths l
    count := p.count + 1
    curLen := 0 }

/-- Rust Staging::clear changes only the count, including on reuse. -/
def clearStore (p : Store) : Store := { p with count := 0 }

structure Represents (p : Store) (s : Impl) : Prop where
  count : p.count = s.pending.length
  cursor : p.curLen = s.staged.length
  committed : ∀ (j : Nat) (hj : j < s.pending.length),
    lengthAt p j = (s.pending[j]).length ∧
    AgaveBatchControl.ValidStaging (s.pending[j]).length 1024
      (byte s.pending[j]) (memoryAt p j)
  current : ∀ i, i < p.curLen → memoryAt p p.count i = byte s.staged i

theorem initial_represents : Represents initialStore init := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro j hj; simp [init] at hj
  · intro i hi; simp [initialStore] at hi

/-- The two independently specified padding endpoints coincide, including zero. -/
theorem padding_matches (len : Nat) :
    AgaveStaging.paddedLength len = AgaveBatchControl.paddedBytes len := by
  unfold AgaveStaging.paddedLength AgaveBatchControl.paddedBytes AgaveBatchControl.rootIndex
  omega

theorem byte_append_left (m part : Message) (i : Nat) (hi : i < m.length) :
    byte (m ++ part) i = byte m i := by
  simp [byte, AgaveConcrete.bytes, AgaveConcrete.toBytes, hi,
    Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)]

theorem byte_append_right (m part : Message) (i : Nat)
    (hlo : m.length ≤ i) (hhi : i < m.length + part.length) :
    byte (m ++ part) i = byte part (i - m.length) := by
  have hn : ¬i < m.length := by omega
  have hp : i - m.length < part.length := by omega
  simp [byte, AgaveConcrete.bytes, AgaveConcrete.toBytes, List.getElem_append, hn, hp, hhi]

@[simp] theorem discard_memory (p : Store) (j i : Nat) :
    memoryAt (discardStore p) j i = memoryAt p j i := rfl

@[simp] theorem discard_lengths (p : Store) (j : Nat) :
    lengthAt (discardStore p) j = lengthAt p j := rfl

@[simp] theorem clear_memory (p : Store) (j i : Nat) :
    memoryAt (clearStore p) j i = memoryAt p j i := rfl

@[simp] theorem clear_lengths (p : Store) (j : Nat) :
    lengthAt (clearStore p) j = lengthAt p j := rfl

theorem copyPart_other_lane (p : Store) (part : Message) (j : Nat) (hne : j ≠ p.count) :
    memoryAt (copyPart p part) j = memoryAt p j := by
  funext i
  simp [memoryAt, copyPart, hne]

theorem finishStore_other_lane (p : Store) (j : Nat) (hne : j ≠ p.count) :
    memoryAt (finishStore p) j = memoryAt p j ∧
    lengthAt (finishStore p) j = lengthAt p j := by
  constructor
  · funext i; simp [memoryAt, finishStore, hne]
  · simp [lengthAt, finishStore, hne]

theorem copyPart_current (p : Store) (m part : Message)
    (hc : p.count < 16) (hlen : p.curLen = m.length)
    (hb : p.curLen + part.length ≤ 1024)
    (hlive : ∀ i, i < p.curLen → memoryAt p p.count i = byte m i) :
    ∀ i, i < (copyPart p part).curLen →
      memoryAt (copyPart p part) p.count i = byte (m ++ part) i := by
  intro i hi
  change i < p.curLen + part.length at hi
  have hib : i < 1024 := by omega
  by_cases hlow : i < p.curLen
  · rw [byte_append_left m part i (by omega)]
    have hw : memoryAt (copyPart p part) p.count i = memoryAt p p.count i := by
      simp [memoryAt, copyPart, hc, hib, Nat.not_le.mpr hlow]
    rw [hw]
    exact hlive i hlow
  · have hlo : p.curLen ≤ i := by omega
    rw [byte_append_right m part i (by omega) (by omega)]
    simpa only [hlen] using (show memoryAt (copyPart p part) p.count i = byte part (i - p.curLen) by
      simp [memoryAt, copyPart, hc, hib, hlo, hi])

theorem copyPart_represents (p : Store) (s : Impl) (part : Message)
    (hr : Represents p s) (hc : p.count < 16)
    (hb : p.curLen + part.length ≤ 1024) :
    Represents (copyPart p part) { s with staged := s.staged ++ part } := by
  refine ⟨hr.count, ?_, ?_, ?_⟩
  · simp [copyPart, hr.cursor]
  · intro j hj
    change j < s.pending.length at hj
    have hn : j ≠ p.count := by rw [hr.count]; omega
    have he := copyPart_other_lane p part j hn
    constructor
    · exact (hr.committed j hj).1
    · change AgaveBatchControl.ValidStaging (s.pending[j]).length 1024
        (byte s.pending[j]) (memoryAt (copyPart p part) j)
      rw [he]
      exact (hr.committed j hj).2
  · exact copyPart_current p s.staged part hc hr.cursor hb hr.current

theorem discard_represents (p : Store) (s : Impl) (hr : Represents p s) :
    Represents (discardStore p) (discard s) := by
  refine ⟨hr.count, rfl, ?_, ?_⟩
  · intro j hj; exact hr.committed j hj
  · intro i hi; simp [discardStore] at hi

theorem spill_represents (p : Store) (s : Impl) (part : Message)
    (hr : Represents p s) :
    Represents (discardStore p) { spill s with serial := s.staged ++ part } := by
  refine ⟨hr.count, rfl, ?_, ?_⟩
  · intro j hj; exact hr.committed j hj
  · intro i hi; simp [discardStore] at hi

theorem append_represents (p : Store) (s : Impl) (part : Message)
    (hr : Represents p s) (hc : p.count < 16) :
    Represents (appendStore s.spilled p part) (append s part) := by
  unfold appendStore append
  cases hs : s.spilled
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hfit : p.curLen + part.length ≤ 1024
    · have hfit' : s.staged.length + part.length ≤ 1024 := by simpa [hr.cursor] using hfit
      simp only [hfit, hfit', ↓reduceIte]
      simpa only [hs] using copyPart_represents p s part hr hc hfit
    · have hfit' : ¬s.staged.length + part.length ≤ 1024 := by simpa [hr.cursor] using hfit
      simp only [hfit, hfit', ↓reduceIte]
      exact spill_represents p s part hr
  · simp only [↓reduceIte]
    exact ⟨hr.count, hr.cursor, hr.committed, hr.current⟩

theorem finishStore_current_valid (p : Store) (m : Message)
    (hc : p.count < 16) (hlen : p.curLen = m.length) (hb : m.length ≤ 1024)
    (hlive : ∀ i, i < p.curLen → memoryAt p p.count i = byte m i) :
    lengthAt (finishStore p) p.count = m.length ∧
    AgaveBatchControl.ValidStaging m.length 1024 (byte m)
      (memoryAt (finishStore p) p.count) := by
  constructor
  · simp [lengthAt, finishStore, hc, hlen]
  · refine ⟨?_, ?_, ?_⟩
    · rw [← padding_matches]; exact (AgaveStaging.padding_bounds m.length hb).2.2
    · intro i hi
      have hib : i < 1024 := by omega
      have hlo : ¬p.curLen ≤ i := by omega
      have hw : memoryAt (finishStore p) p.count i = memoryAt p p.count i := by
        simp [memoryAt, finishStore, hc, hib, hlo]
      rw [hw]; exact hlive i (by omega)
    · intro i hlo hhi
      have hp := (AgaveStaging.padding_bounds m.length hb).2.2
      have hib : i < 1024 := by rw [padding_matches] at hp; omega
      have hpadded : i < AgaveStaging.paddedLength p.curLen := by
        rw [hlen, padding_matches]; exact hhi
      simp [memoryAt, finishStore, hc, hib, hpadded, show p.curLen ≤ i by omega]

theorem finish_represents (p : Store) (s : Impl)
    (hr : Represents p s) (hc : p.count < 16) (hb : s.staged.length ≤ 1024) :
    Represents (finishStore p) (finishLane s) := by
  have hcEq := hr.count
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [finishStore, finishLane, hr.count]
  · intro j hj
    change j < (s.pending ++ [s.staged]).length at hj
    by_cases hprev : j < s.pending.length
    · have hn : j ≠ p.count := by rw [hr.count]; omega
      have hh := finishStore_other_lane p j hn
      simpa only [finishLane, List.getElem_append_left hprev, hh.1, hh.2]
        using hr.committed j hprev
    · have he : j = p.count := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      have hind : p.count - s.pending.length = 0 := by omega
      simpa only [finishLane, List.getElem_append_right (by omega : s.pending.length ≤ p.count),
        hind, List.getElem_cons_zero] using finishStore_current_valid p s.staged hc hr.cursor hb hr.current
  · intro i hi; simp [finishStore] at hi

theorem clear_represents (p : Store) (s : Impl) (hr : Represents p s)
    (hclean : s.staged = []) :
    Represents (clearStore p) { s with pending := [] } := by
  refine ⟨rfl, hr.cursor, ?_, ?_⟩
  · intro j hj; simp at hj
  · intro i hi
    have hh : p.curLen = 0 := by simpa [hclean] using hr.cursor
    simp only [clearStore] at hi
    omega

/-- Commit changes no staging bytes on the serial spill branch.  The short
    branch finishes its lane and immediately clears the count if full. -/
def commitStore (w : Nat) (spilled : Bool) (p : Store) : Store :=
  if spilled then p
  else let q := finishStore p
       if q.count = w then clearStore q else q

def takeStore (p : Store) : Store :=
  if p.count = 0 then p else clearStore p

theorem flush_represents (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (p : Store) (s : Impl) (hr : Represents p s) (hclean : s.staged = []) :
    Represents (clearStore p) (flush hash w b s) := by
  have hh := clear_represents p s hr hclean
  unfold flush
  split <;> exact ⟨hh.count, hh.cursor, hh.committed, hh.current⟩

theorem commit_represents (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (p : Store) (s : Impl) (hr : Represents p s)
    (hw : w ≤ 16) (hb : Bounds w s) :
    Represents (commitStore w s.spilled p) (commit hash w b s) := by
  have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
  unfold commitStore commit
  cases hs : s.spilled
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hf := finish_represents p s hr hc hb.2.2
    have hcounts : (finishStore p).count = (finishLane s).pending.length := hf.count
    by_cases hfull : (finishStore p).count = w
    · have hfull' : (finishLane s).pending.length = w := by omega
      simp only [hfull, hfull', ↓reduceIte]
      exact flush_represents hash w b (finishStore p) (finishLane s) hf rfl
    · have hfull' : ¬(finishLane s).pending.length = w := by omega
      simp only [hfull, hfull', ↓reduceIte]
      simpa only [hs] using hf
  · simp only [↓reduceIte]
    exact ⟨hr.count, hr.cursor, hr.committed, hr.current⟩

theorem take_represents (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (p : Store) (s : Impl) (hr : Represents p s) (hclean : s.staged = []) :
    Represents (takeStore p) (take hash w b s).2 := by
  unfold takeStore take
  by_cases he : p.count = 0
  · have hp : s.pending = [] := List.length_eq_zero_iff.mp (hr.count.symm.trans he)
    simp only [he, hp, List.isEmpty_nil, ↓reduceIte]
    exact ⟨by simpa [hp] using hr.count, hr.cursor, by simp, hr.current⟩
  · have hp : s.pending.isEmpty = false := by
      have hn : s.pending ≠ [] := by intro hh; apply he; simpa [hh] using hr.count
      cases hh : s.pending with
      | nil => exact False.elim (hn hh)
      | cons x xs => rfl
    simp only [he, hp, Bool.false_eq_true, ↓reduceIte]
    have hh := flush_represents hash w b p s hr hclean
    exact ⟨hh.count, hh.cursor, hh.committed, hh.current⟩

/-- A physical trace shares the public lifecycle with `AgaveStaging.Run`, while
    also recording every concrete retained-buffer mutation.  No extra memory
    validity premises are imposed on clients. -/
inductive Run (hash : Message → Value) (w : Nat) (b : Backend hash w) :
    Store → Impl → Spec → Prop
  | initial : Run hash w b initialStore init specInit
  | start {p s r} (run : Run hash w b p s r) (idle : r.active = none) :
      Run hash w b p s { r with active := some [] }
  | part {p s r} (run : Run hash w b p s r) (m part : Message) (active : r.active = some m) :
      Run hash w b (appendStore s.spilled p part) (append s part)
        { r with active := some (m ++ part) }
  | finish {p s r} (run : Run hash w b p s r) (m : Message) (active : r.active = some m) :
      Run hash w b (commitStore w s.spilled p) (commit hash w b s)
        ⟨r.committed ++ [m], none⟩
  | drop {p s r} (run : Run hash w b p s r) (m : Message) (active : r.active = some m) :
      Run hash w b (discardStore p) (discard s) { r with active := none }
  | whole {p s r} (run : Run hash w b p s r) (m : Message) (idle : r.active = none) :
      Run hash w b (commitStore w (append s m).spilled (appendStore s.spilled p m))
        (addMessage hash w b s m) ⟨r.committed ++ [m], none⟩
  | drain {p s r} (run : Run hash w b p s r) (idle : r.active = none) :
      Run hash w b (takeStore p) (take hash w b s).2 specInit

theorem run_forget (hash : Message → Value) (w : Nat) (b : Backend hash w)
    {p : Store} {s : Impl} {r : Spec} (trace : Run hash w b p s r) :
    AgaveStaging.Run hash w b s r := by
  induction trace with
  | initial => exact .initial
  | start _ idle ih => exact .start ih idle
  | part _ m part active ih => exact .part ih m part active
  | finish _ m active ih => exact .finish ih m active
  | drop _ m active ih => exact .drop ih m active
  | whole _ m idle ih => exact .whole ih m idle
  | drain _ idle ih => exact .drain ih idle

theorem run_refines (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (hw : 0 < w) {p : Store} {s : Impl} {r : Spec} (trace : Run hash w b p s r) :
    Refines hash w s r :=
  AgaveStaging.run_refines hash w b hw (run_forget hash w b trace)

theorem run_represents (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (hw : 0 < w) (hw16 : w ≤ 16)
    {p : Store} {s : Impl} {r : Spec} (trace : Run hash w b p s r) : Represents p s := by
  induction trace with
  | initial => exact initial_represents
  | start _ _ ih => exact ih
  | part run m part active ih =>
    have hb := (run_refines hash w b hw run).1
    apply append_represents _ _ part ih
    have hc := ih.count; have hn := hb.1; omega
  | finish run m active ih =>
    exact commit_represents hash w b _ _ ih hw16 (run_refines hash w b hw run).1
  | drop _ _ _ ih => exact discard_represents _ _ ih
  | whole run m idle ih =>
    have hb := (run_refines hash w b hw run).1
    have hc := ih.count; have hn := hb.1
    exact commit_represents hash w b _ _
      (append_represents _ _ m ih (by omega)) hw16 (append_bounds _ w m hb)
  | drain run idle ih =>
    have hc := (run_refines hash w b hw run).2.1
    rw [idle] at hc
    exact take_represents hash w b _ _ ih hc.1

/-- Every abstract public trace can be enriched with the retained physical
    buffer trace, so this refinement does not exclude legal programs. -/
theorem run_lift (hash : Message → Value) (w : Nat) (b : Backend hash w)
    {s : Impl} {r : Spec} (trace : AgaveStaging.Run hash w b s r) :
    ∃ p, Run hash w b p s r := by
  induction trace with
  | initial => exact ⟨_, .initial⟩
  | start _ idle ih => rcases ih with ⟨p, run⟩; exact ⟨p, .start run idle⟩
  | part _ m part active ih => rcases ih with ⟨p, run⟩; exact ⟨_, .part run m part active⟩
  | finish _ m active ih => rcases ih with ⟨p, run⟩; exact ⟨_, .finish run m active⟩
  | drop _ m active ih => rcases ih with ⟨p, run⟩; exact ⟨_, .drop run m active⟩
  | whole _ m idle ih => rcases ih with ⟨p, run⟩; exact ⟨_, .whole run m idle⟩
  | drain _ idle ih => rcases ih with ⟨p, run⟩; exact ⟨_, .drain run idle⟩

/-- A full flush's metadata and actual retained allocation meet the kernel's
    premises, including its empty-message block, with no whole-lane zeroing. -/
theorem full_flush_valid (p : Store) (s : Impl) (w : Nat)
    (hr : Represents p s) (hfull : p.count = w) (hp : PendingOK s) :
    ∀ lane : Fin w,
      lengthAt p lane.val = (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hfull) lane).length ∧
      lengthAt p lane.val ≤ 1024 ∧
      AgaveBatchControl.ValidStaging (lengthAt p lane.val) 1024
        (byte (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hfull) lane))
        (memoryAt p lane.val) := by
  intro lane
  have hj : lane.val < s.pending.length := by
    have hh := lane.isLt; have hc := hr.count; omega
  have hh := hr.committed lane.val hj
  have hm : s.pending[lane.val] ∈ s.pending := List.mem_of_getElem rfl
  refine ⟨hh.1, ?_, ?_⟩
  · rw [hh.1]; exact hp _ hm
  · simpa only [hh.1, AgaveConcrete.messagesOf] using hh.2

/-- The transient full store just before a normal commit's flush is valid.
    This applies after any fragments, spills, abandoned builders and drains. -/
theorem reached_full_flush_valid (hash : Message → Value) (w : Nat) (b : Backend hash w)
    (hw : 0 < w) (hw16 : w ≤ 16)
    {p : Store} {s : Impl} {r : Spec} (trace : Run hash w b p s r)
    (hfull : p.count + 1 = w) :
    let q := finishStore p
    let t := finishLane s
    ∃ h : t.pending.length = w,
      ∀ lane : Fin w, lengthAt q lane.val ≤ 1024 ∧
        AgaveBatchControl.ValidStaging (lengthAt q lane.val) 1024
          (byte (AgaveConcrete.messagesOf t.pending h lane)) (memoryAt q lane.val) := by
  have hr := run_represents hash w b hw hw16 trace
  have hb := (run_refines hash w b hw trace).1
  have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
  have hf := finish_represents p s hr hc hb.2.2
  have hfull' : (finishStore p).count = w := hfull
  refine ⟨hf.count.symm.trans hfull', ?_⟩
  intro lane
  exact (full_flush_valid _ _ _ hf hfull'
    (finishLane_pendingOK s hb.2.1 hb.2.2) lane).2

/-- The concrete kernel now reads arbitrary supplied lane memory.  In contrast
    to `AgaveConcrete.rootState`, no canonical zero-filled message is allocated. -/
def retainedRootState {n : Nat} (perm : AgaveLattice.Matrix)
    (lengths : Fin n → Nat) (memory : Fin n → Nat → Byte) : AgaveConcrete.BatchState n :=
  (AgaveConcrete.simdRun perm lengths memory 15
    (fun _ => ⟨0, AgaveConcrete.iv⟩)).getD (fun _ => ⟨0, AgaveConcrete.iv⟩)

theorem retainedRootState_correct {n : Nat} (hn : 0 < n)
    {perm : AgaveLattice.Matrix} (hp : AgaveLattice.IsTranspose n perm)
    (ms : Fin n → AgaveConcrete.Message) (memory : Fin n → Nat → Byte)
    (hm : ∀ l, (ms l).length ≤ 1024)
    (hstage : ∀ l, AgaveBatchControl.ValidStaging (ms l).length 1024
      (AgaveConcrete.bytes (ms l)) (memory l)) :
    retainedRootState perm (fun l => (ms l).length) memory =
      fun l => AgaveBatchControl.scalarRootState AgaveConcrete.compress AgaveConcrete.iv
        (AgaveConcrete.bytes (ms l)) (ms l).length := by
  unfold retainedRootState
  rw [AgaveConcrete.simdRun_eq hn hp,
    AgaveBatchControl.compress_batch_control_equiv AgaveConcrete.compress AgaveConcrete.iv hm hstage]
  rfl

def retainedXofWords {n : Nat} (perm : AgaveLattice.Matrix)
    (lengths : Fin n → Nat) (memory : Fin n → Nat → Byte) : AgaveLattice.XofWords :=
  fun lane out word => if hl : lane < n then if ho : out < 32 then if hw : word < 16 then
    AgaveConcrete.simdXofAt perm lengths memory
      (retainedRootState perm lengths memory) ⟨out, ho⟩ ⟨word, hw⟩ ⟨lane, hl⟩
    else 0 else 0 else 0

theorem retainedXofWords_correct {n : Nat} (hn : 0 < n)
    {perm : AgaveLattice.Matrix} (hp : AgaveLattice.IsTranspose n perm)
    (ms : Fin n → AgaveConcrete.Message) (memory : Fin n → Nat → Byte)
    (hm : ∀ l, (ms l).length ≤ 1024)
    (hstage : ∀ l, AgaveBatchControl.ValidStaging (ms l).length 1024
      (AgaveConcrete.bytes (ms l)) (memory l))
    (lane : Fin n) (out : Fin 32) (word : Fin 16) :
    retainedXofWords perm (fun l => (ms l).length) memory lane out word =
      AgaveConcrete.oneChunkWords (ms lane) out word := by
  simp only [retainedXofWords, lane.isLt, out.isLt, word.isLt, ↓reduceDIte]
  change Blake3Compression.project (AgaveConcrete.simdXofAt _ _ _ _ _) lane word = _
  rw [AgaveConcrete.simdXofAt_project hn hp,
    retainedRootState_correct hn hp ms memory hm hstage,
    AgaveBatchControl.root_xof_equiv AgaveConcrete.compress AgaveConcrete.xof AgaveConcrete.iv hstage]
  rfl

def retainedUpdate {n : Nat} (hn : 0 < n) (perm : AgaveLattice.Matrix)
    (lengths : Fin n → Nat) (memory : Fin n → Nat → Byte) (a : Value) : Value := fun i =>
  AgaveLattice.simdLtHash n hn perm (retainedXofWords perm lengths memory)
    (AgaveConcrete.extendAcc a) i

theorem retainedUpdate_eq_fold {n : Nat} (hn : 0 < n)
    {perm : AgaveLattice.Matrix} (hp : AgaveLattice.IsTranspose n perm)
    (ms : Fin n → AgaveConcrete.Message) (memory : Fin n → Nat → Byte)
    (hm : ∀ l, (ms l).length ≤ 1024)
    (hstage : ∀ l, AgaveBatchControl.ValidStaging (ms l).length 1024
      (AgaveConcrete.bytes (ms l)) (memory l)) (a : Value) :
    retainedUpdate hn perm (fun l => (ms l).length) memory a =
      (List.finRange n).foldl (fun z lane => plus z (AgaveConcrete.oneChunk (ms lane))) a := by
  funext i
  unfold retainedUpdate
  rw [AgaveLattice.simdLtHash_eq_scalarLtHash hn hp,
    AgaveLattice.scalarLtHash_apply, AgaveConcrete.value_foldl_apply]
  have hword (lane : Fin n) :
      AgaveLattice.scalarMessage (retainedXofWords perm (fun l => (ms l).length) memory) lane i =
      AgaveConcrete.oneChunk (ms lane) i := by
    unfold AgaveLattice.scalarMessage AgaveConcrete.oneChunk
    rw [retainedXofWords_correct hn hp ms memory hm hstage lane ⟨i.val / 32, by omega⟩
      ⟨i.val % 32 / 2, by omega⟩]
  simp only [hword, AgaveConcrete.extendAcc, i.isLt, ↓reduceDIte]

/-- Canonical zero extension may be replaced by actual retained storage whenever
    the physical staging relation holds.  Stale data never reaches the oracle. -/
theorem retainedUpdate_eq_canonical {n : Nat} (hn : 0 < n)
    {perm : AgaveLattice.Matrix} (hp : AgaveLattice.IsTranspose n perm)
    (ms : Fin n → AgaveConcrete.Message) (memory : Fin n → Nat → Byte)
    (hm : ∀ l, (ms l).length ≤ 1024)
    (hstage : ∀ l, AgaveBatchControl.ValidStaging (ms l).length 1024
      (AgaveConcrete.bytes (ms l)) (memory l)) (a : Value) :
    retainedUpdate hn perm (fun l => (ms l).length) memory a =
      AgaveConcrete.simdUpdate hn perm ms a := by
  rw [retainedUpdate_eq_fold hn hp ms memory hm hstage,
    AgaveConcrete.simdUpdate_eq_fold hn hp ms hm]

def physicalUpdate (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix)
    (p : Store) (a : Value) : Value :=
  retainedUpdate hn perm (fun l => lengthAt p l.val) (fun l => memoryAt p l.val) a

/-- Pointwise implementation refinement of the backend invocation itself: its
    input is the real retained allocation and independent lengths metadata. -/
theorem physicalUpdate_eq_backend (n : Nat) (hn : 0 < n)
    (perm : AgaveLattice.Matrix) (hp : AgaveLattice.IsTranspose n perm)
    (p : Store) (s : Impl) (hr : Represents p s) (hfull : p.count = n)
    (hshort : PendingOK s) (a : Value) :
    physicalUpdate n hn perm p a = AgaveConcrete.run n hn perm s.pending a := by
  have hlen : s.pending.length = n := hr.count.symm.trans hfull
  let ms : Fin n → AgaveConcrete.Message :=
    fun l => AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending hlen l)
  have hh := full_flush_valid p s n hr hfull hshort
  have he : (fun l : Fin n => lengthAt p l.val) = fun l => (ms l).length := by
    funext l
    simpa only [ms, AgaveConcrete.toBytes_length] using (hh l).1
  have hm : ∀ l, (ms l).length ≤ 1024 := by
    intro l
    rw [← congrFun he l]
    exact (hh l).2.1
  have hstage : ∀ l, AgaveBatchControl.ValidStaging (ms l).length 1024
      (AgaveConcrete.bytes (ms l)) (memoryAt p l.val) := by
    intro l
    rw [← congrFun he l]
    exact (hh l).2.2
  unfold physicalUpdate AgaveConcrete.run
  rw [dite_eq_left hlen, he, retainedUpdate_eq_canonical hn hp ms _ hm hstage]

theorem physicalUpdate_correct (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n)
    (perm : AgaveLattice.Matrix) (hp : AgaveLattice.IsTranspose n perm)
    (p : Store) (s : Impl) (hr : Represents p s) (hfull : p.count = n)
    (hshort : PendingOK s) (a : Value) :
    physicalUpdate n hn perm p a =
      plus a (scalar (AgaveConcrete.hash longHash) s.pending) := by
  rw [physicalUpdate_eq_backend n hn perm hp p s hr hfull hshort]
  exact AgaveConcrete.run_correct longHash n hn perm hp s.pending a
    (hr.count.symm.trans hfull) hshort

/-- Every actual full SIMD flush in every legal physical trace executes the
    concrete retained-memory kernel with the same value as the scalar oracle.
    Its only trace-side conditions select the full, unspilled commit branch. -/
theorem reached_full_kernel_correct (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16)
    (perm : AgaveLattice.Matrix) (hp : AgaveLattice.IsTranspose n perm)
    (b : Backend (AgaveConcrete.hash longHash) n)
    {p : Store} {s : Impl} {r : Spec}
    (trace : Run (AgaveConcrete.hash longHash) n b p s r)
    (_unspilled : s.spilled = false) (hfull : p.count + 1 = n) :
    physicalUpdate n hn perm (finishStore p) s.acc =
      plus s.acc (scalar (AgaveConcrete.hash longHash) (s.pending ++ [s.staged])) := by
  have hr := run_represents _ n b hn hn16 trace
  have hb := (run_refines _ n b hn trace).1
  have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
  exact physicalUpdate_correct longHash n hn perm hp (finishStore p) (finishLane s)
    (finish_represents p s hr hc hb.2.2) hfull
    (finishLane_pendingOK s hb.2.1 hb.2.2) s.acc

/-- This is the byte slice actually fed to the serial hasher, converted back
    from the retained u8 representation.  It reads exactly `len` bytes. -/
def readMessage (p : Store) (lane len : Nat) : Message :=
  List.ofFn (fun i : Fin len => UInt8.ofBitVec (memoryAt p lane i.val))

theorem readMessage_eq (p : Store) (lane len : Nat) (m : Message)
    (hlen : len = m.length)
    (hlive : ∀ i, i < len → memoryAt p lane i = byte m i) :
    readMessage p lane len = m := by
  apply List.ext_getElem (by simp [readMessage, hlen])
  intro i hread hm
  simp only [readMessage, List.getElem_ofFn]
  change UInt8.ofBitVec (memoryAt p lane i) = m[i]
  rw [hlive i (by simpa only [readMessage, List.length_ofFn] using hread)]
  simp [byte, AgaveConcrete.bytes, AgaveConcrete.toBytes, hm]

theorem read_current (p : Store) (s : Impl) (hr : Represents p s) :
    readMessage p p.count p.curLen = s.staged :=
  readMessage_eq p p.count p.curLen s.staged hr.cursor hr.current

theorem read_committed (p : Store) (s : Impl) (hr : Represents p s)
    (j : Nat) (hj : j < s.pending.length) :
    readMessage p j (lengthAt p j) = s.pending[j] := by
  have hh := hr.committed j hj
  apply readMessage_eq p j (lengthAt p j) s.pending[j] hh.1
  intro i hi
  exact hh.2.live i (by omega)

def readBatch (p : Store) : List Message :=
  (List.range p.count).map (fun j => readMessage p j (lengthAt p j))

theorem readBatch_eq (p : Store) (s : Impl) (hr : Represents p s) :
    readBatch p = s.pending := by
  apply List.ext_getElem (by simp [readBatch, hr.count])
  intro i hi hj
  simpa [readBatch] using read_committed p s hr i hj

/-- Appending also transcribes the serial side of a spill: the prefix comes
    from actual staged memory, and the overflowing part is appended afterwards. -/
def physicalAppend (p : Store) (s : Impl) (part : Message) : Impl :=
  if s.spilled then { s with serial := s.serial ++ part }
  else if p.curLen + part.length ≤ 1024 then { s with staged := s.staged ++ part }
  else { s with staged := [], serial := readMessage p p.count p.curLen ++ part, spilled := true }

theorem physicalAppend_eq (p : Store) (s : Impl) (part : Message) (hr : Represents p s) :
    physicalAppend p s part = append s part := by
  unfold physicalAppend append
  rw [read_current p s hr]
  simp only [hr.cursor, spill]

/-- Full SIMD flushes read retained buffers directly.  Scalar tails read their
    exact live byte slices and reset the shared hasher before each message. -/
def physicalFlush (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix) (p : Store) (s : Impl) : Impl :=
  if 1 < n ∧ p.count = n then
    { s with acc := physicalUpdate n hn perm p s.acc, pending := [] }
  else
    { s with acc := plus s.acc (scalar (AgaveConcrete.hash longHash) (readBatch p)), pending := [], serial := (readBatch p).getLast?.getD s.serial }

theorem physicalFlush_eq (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    (p : Store) (s : Impl) (hr : Represents p s) (hshort : PendingOK s) :
    physicalFlush longHash n hn perm p s =
      flush (AgaveConcrete.hash longHash) n (AgaveConcrete.backend longHash n hn perm hp) s := by
  unfold physicalFlush flush
  by_cases hf : 1 < n ∧ p.count = n
  · have hf' : 1 < n ∧ s.pending.length = n := by rw [← hr.count]; exact hf
    rw [ite_eq_left hf, ite_eq_left hf']
    simp only [AgaveConcrete.backend]
    rw [physicalUpdate_eq_backend n hn perm hp p s hr hf.2 hshort]
  · have hf' : ¬(1 < n ∧ s.pending.length = n) := by rw [← hr.count]; exact hf
    simp only [hf, hf', ↓reduceIte, readBatch_eq p s hr]

def physicalCommit (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix) (p : Store) (s : Impl) : Impl :=
  if s.spilled then { s with acc := plus s.acc (AgaveConcrete.hash longHash s.serial), spilled := false }
  else
    let q := finishStore p
    let t := finishLane s
    if q.count = n then physicalFlush longHash n hn perm q t else t

theorem physicalCommit_eq (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    (p : Store) (s : Impl) (hr : Represents p s) (hb : Bounds n s) :
    physicalCommit longHash n hn perm p s =
      commit (AgaveConcrete.hash longHash) n (AgaveConcrete.backend longHash n hn perm hp) s := by
  have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
  have hh := finish_represents p s hr hc hb.2.2
  unfold physicalCommit commit
  split
  · rfl
  · simp only [hh.count]
    split
    · exact physicalFlush_eq longHash n hn perm hp (finishStore p) (finishLane s)
        hh (finishLane_pendingOK s hb.2.1 hb.2.2)
    · rfl

def physicalTake (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix) (p : Store) (s : Impl) : Value × Impl :=
  let t := if p.count = 0 then s else physicalFlush longHash n hn perm p s
  (t.acc, { t with acc := zero })

theorem physicalTake_eq (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    (p : Store) (s : Impl) (hr : Represents p s) (hshort : PendingOK s) :
    physicalTake longHash n hn perm p s =
      take (AgaveConcrete.hash longHash) n (AgaveConcrete.backend longHash n hn perm hp) s := by
  unfold physicalTake take
  rw [physicalFlush_eq longHash n hn perm hp p s hr hshort, hr.count]
  have hh : (s.pending.isEmpty = true) ↔ s.pending.length = 0 := by simp
  simp only [← hh]

/-- The physical program, whose full SIMD branch actually calls the retained
    kernel.  Pending/staged message lists are ghost fields used only to state
    refinement; scalar serial input is read from actual memory above. -/
inductive ConcreteRun (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (perm : AgaveLattice.Matrix) : Store → Impl → Spec → Prop
  | initial : ConcreteRun longHash n hn perm initialStore init specInit
  | start {p s r} (run : ConcreteRun longHash n hn perm p s r) (idle : r.active = none) :
      ConcreteRun longHash n hn perm p s { r with active := some [] }
  | part {p s r} (run : ConcreteRun longHash n hn perm p s r)
      (m part : Message) (active : r.active = some m) :
      ConcreteRun longHash n hn perm (appendStore s.spilled p part) (physicalAppend p s part)
        { r with active := some (m ++ part) }
  | finish {p s r} (run : ConcreteRun longHash n hn perm p s r)
      (m : Message) (active : r.active = some m) :
      ConcreteRun longHash n hn perm (commitStore n s.spilled p)
        (physicalCommit longHash n hn perm p s) ⟨r.committed ++ [m], none⟩
  | drop {p s r} (run : ConcreteRun longHash n hn perm p s r)
      (m : Message) (active : r.active = some m) :
      ConcreteRun longHash n hn perm (discardStore p) (discard s) { r with active := none }
  | whole {p s r} (run : ConcreteRun longHash n hn perm p s r)
      (m : Message) (idle : r.active = none) :
      ConcreteRun longHash n hn perm
        (commitStore n (physicalAppend p s m).spilled (appendStore s.spilled p m))
        (physicalCommit longHash n hn perm (appendStore s.spilled p m) (physicalAppend p s m))
        ⟨r.committed ++ [m], none⟩
  | drain {p s r} (run : ConcreteRun longHash n hn perm p s r) (idle : r.active = none) :
      ConcreteRun longHash n hn perm (takeStore p) (physicalTake longHash n hn perm p s).2 specInit

theorem concrete_run_simulates (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {p : Store} {s : Impl} {r : Spec} (trace : ConcreteRun longHash n hn perm p s r) :
    Run (AgaveConcrete.hash longHash) n (AgaveConcrete.backend longHash n hn perm hp) p s r := by
  induction trace with
  | initial => exact .initial
  | start _ idle ih => exact .start ih idle
  | @part p s r run m part active ih =>
    have hr := run_represents _ _ _ hn hn16 ih
    rw [physicalAppend_eq p s part hr]
    exact .part ih m part active
  | @finish p s r run m active ih =>
    have hr := run_represents _ _ _ hn hn16 ih
    have hb := (run_refines _ _ _ hn ih).1
    rw [physicalCommit_eq longHash n hn hn16 perm hp p s hr hb]
    exact .finish ih m active
  | drop _ m active ih => exact .drop ih m active
  | @whole p s r run m idle ih =>
    have hr := run_represents _ _ _ hn hn16 ih
    have hb := (run_refines _ _ _ hn ih).1
    have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
    rw [physicalAppend_eq p s m hr]
    rw [physicalCommit_eq longHash n hn hn16 perm hp _ _
      (append_represents p s m hr hc) (append_bounds s n m hb)]
    exact .whole ih m idle
  | @drain p s r run idle ih =>
    have hr := run_represents _ _ _ hn hn16 ih
    have hb := (run_refines _ _ _ hn ih).1
    rw [physicalTake_eq longHash n hn perm hp p s hr hb.2.1]
    exact .drain ih idle

/-- End-to-end result for actual retained-memory execution.  The proposition
    has no backend correctness or ValidStaging assumptions: both are proved. -/
theorem concrete_observational_equivalence (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {p : Store} {s : Impl} {r : Spec}
    (trace : ConcreteRun longHash n hn perm p s r) (idle : r.active = none) :
    (physicalTake longHash n hn perm p s).1 =
      scalar (AgaveConcrete.hash longHash) r.committed := by
  have ht := concrete_run_simulates longHash n hn hn16 perm hp trace
  have hr := run_represents _ _ _ hn hn16 ht
  have hb := (run_refines _ _ _ hn ht).1
  rw [physicalTake_eq longHash n hn perm hp p s hr hb.2.1]
  exact AgaveStaging.observational_equivalence _ _ _ hn (run_forget _ _ _ ht) idle

/-- Converse simulation establishes that the concrete trace type is not a
    restriction on valid abstract traces. -/
theorem concrete_run_lift (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {p : Store} {s : Impl} {r : Spec}
    (trace : Run (AgaveConcrete.hash longHash) n (AgaveConcrete.backend longHash n hn perm hp) p s r) :
    ConcreteRun longHash n hn perm p s r := by
  induction trace with
  | initial => exact .initial
  | start _ idle ih => exact .start ih idle
  | @part p s r run m part active ih =>
    have hr := run_represents _ _ _ hn hn16 run
    simpa only [physicalAppend_eq p s part hr] using ConcreteRun.part ih m part active
  | @finish p s r run m active ih =>
    have hr := run_represents _ _ _ hn hn16 run
    have hb := (run_refines _ _ _ hn run).1
    simpa only [physicalCommit_eq longHash n hn hn16 perm hp p s hr hb]
      using ConcreteRun.finish ih m active
  | drop _ m active ih => exact .drop ih m active
  | @whole p s r run m idle ih =>
    have hr := run_represents _ _ _ hn hn16 run
    have hb := (run_refines _ _ _ hn run).1
    have hc : p.count < 16 := by have hh := hr.count; have hh' := hb.1; omega
    simpa only [physicalAppend_eq p s m hr,
      physicalCommit_eq longHash n hn hn16 perm hp _ _
        (append_represents p s m hr hc) (append_bounds s n m hb), addMessage]
      using ConcreteRun.whole ih m idle
  | @drain p s r run idle ih =>
    have hr := run_represents _ _ _ hn hn16 run
    have hb := (run_refines _ _ _ hn run).1
    simpa only [physicalTake_eq longHash n hn perm hp p s hr hb.2.1]
      using ConcreteRun.drain ih idle

theorem avx2_physical_observational_equivalence (longHash : AgaveConcrete.Message → Value)
    {p : Store} {s : Impl} {r : Spec}
    (trace : ConcreteRun longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) p s r)
    (idle : r.active = none) :
    (physicalTake longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p s).1 =
      scalar (AgaveConcrete.hash longHash) r.committed :=
  concrete_observational_equivalence longHash 8 (by decide) (by decide) _
    AgaveLattice.avx2_isTranspose trace idle

theorem avx512_physical_observational_equivalence (longHash : AgaveConcrete.Message → Value)
    {p : Store} {s : Impl} {r : Spec}
    (trace : ConcreteRun longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) p s r)
    (idle : r.active = none) :
    (physicalTake longHash 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p s).1 =
      scalar (AgaveConcrete.hash longHash) r.committed :=
  concrete_observational_equivalence longHash 16 (by decide) (by decide) _
    AgaveLattice.avx512_isTranspose trace idle

/-- Identical committed messages imply identical results across different
    physical retained-buffer histories and SIMD widths. -/
theorem avx2_physical_eq_avx512 (longHash : AgaveConcrete.Message → Value)
    {p8 p16 : Store} {s8 s16 : Impl} {r : Spec}
    (trace8 : ConcreteRun longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8 r)
    (trace16 : ConcreteRun longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16 r)
    (idle : r.active = none) :
    (physicalTake longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8).1 =
      (physicalTake longHash 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16).1 := by
  rw [avx2_physical_observational_equivalence longHash trace8 idle,
    avx512_physical_observational_equivalence longHash trace16 idle]

theorem reference_isTranspose : AgaveLattice.IsTranspose 1 AgaveLattice.labels := by
  intro r c
  simp [AgaveLattice.labels]

theorem reference_physical_observational_equivalence (longHash : AgaveConcrete.Message → Value)
    {p : Store} {s : Impl} {r : Spec}
    (trace : ConcreteRun longHash 1 (by decide) AgaveLattice.labels p s r)
    (idle : r.active = none) :
    (physicalTake longHash 1 (by decide) AgaveLattice.labels p s).1 =
      scalar (AgaveConcrete.hash longHash) r.committed :=
  concrete_observational_equivalence longHash 1 (by decide) (by decide) _
    reference_isTranspose trace idle

/-- Complete 1/8/16 result comparison with retained allocation histories.
    The width-one flush always takes the physical scalar-tail path. -/
theorem physical_reference_eq_avx2_eq_avx512 (longHash : AgaveConcrete.Message → Value)
    {p1 p8 p16 : Store} {s1 s8 s16 : Impl} {r : Spec}
    (trace1 : ConcreteRun longHash 1 (by decide) AgaveLattice.labels p1 s1 r)
    (trace8 : ConcreteRun longHash 8 (by decide)
      (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8 r)
    (trace16 : ConcreteRun longHash 16 (by decide)
      (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16 r)
    (idle : r.active = none) :
    let referenceResult := (physicalTake longHash 1 (by decide) AgaveLattice.labels p1 s1).1
    let avx2Result := (physicalTake longHash 8 (by decide) (AgaveLattice.transpose8 AgaveLattice.labels) p8 s8).1
    let avx512Result := (physicalTake longHash 16 (by decide) (AgaveLattice.transpose16 AgaveLattice.labels) p16 s16).1
    referenceResult = avx2Result ∧ avx2Result = avx512Result := by
  dsimp only
  rw [reference_physical_observational_equivalence longHash trace1 idle,
    avx2_physical_observational_equivalence longHash trace8 idle,
    avx512_physical_observational_equivalence longHash trace16 idle]
  exact ⟨rfl, rfl⟩

/-- The infinite arithmetic notation exactly matches Rust's saturated guard
    on both common usize widths (or any usize maximum above one chunk). -/
theorem append_guard_matches_saturating (p : Store) (part : Message) (usizeMax : Nat)
    (hmax : 1024 < usizeMax) :
    min (p.curLen + part.length) usizeMax ≤ 1024 ↔ p.curLen + part.length ≤ 1024 :=
  AgaveStaging.saturating_append_guard p.curLen part.length usizeMax hmax

/-- No write or scalar-prefix read crosses a selected-width lane boundary.
    The 16-lane physical type simply embeds the 1/8-lane allocations. -/
theorem reached_access_bounds (longHash : AgaveConcrete.Message → Value)
    (n : Nat) (hn : 0 < n) (hn16 : n ≤ 16) (perm : AgaveLattice.Matrix)
    (hp : AgaveLattice.IsTranspose n perm)
    {p : Store} {s : Impl} {r : Spec}
    (trace : ConcreteRun longHash n hn perm p s r) :
    p.count < n ∧ p.count < 16 ∧ p.curLen ≤ 1024 ∧ p.count + 1 ≤ n := by
  have ht := concrete_run_simulates longHash n hn hn16 perm hp trace
  have hr := run_represents _ _ _ hn hn16 ht
  have hb := (run_refines _ _ _ hn ht).1
  have hc := hr.count
  have hcursor := hr.cursor
  have hbcount := hb.1
  have hbcur := hb.2.2
  omega

/-- Explicit frame facts: stale suffixes survive finishing, and scalar spill,
    builder drop, flush and reuse do not clear any lane bytes. -/
theorem finish_preserves_stale_suffix (p : Store) (l : Fin 16) (i : Fin 1024)
    (hstale : AgaveStaging.paddedLength p.curLen ≤ i.val) :
    (finishStore p).memory l i = p.memory l i := by
  simp [finishStore, Nat.not_lt.mpr hstale]

theorem discard_preserves_all_bytes (p : Store) : (discardStore p).memory = p.memory := rfl

theorem clear_preserves_all_bytes (p : Store) : (clearStore p).memory = p.memory := rfl

end AgavePhysicalStaging
