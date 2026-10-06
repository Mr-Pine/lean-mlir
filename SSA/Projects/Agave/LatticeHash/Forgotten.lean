/- Released under Apache 2.0 license as described in the file LICENSE. -/
import Std

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-!
Separate concrete byte-addressed staging model for the known client-mem::forget
counterexample. Raw.flush resets count but deliberately retains curLen and lane
bytes, exactly as Staging::clear does. This is outside Staging.Run's lifecycle.
The observable below records each message passed to hashing; therefore its result
does not assume any property (or implementation) of BLAKE3.
-/
namespace AgaveForgotten

abbrev Message := List UInt8

structure Raw where
  width : Nat
  lanes : Nat → Nat → UInt8
  lengths : Nat → Nat
  count : Nat
  curLen : Nat
  serial : Message
  spilled : Bool
  hashed : List Message

def initial (width : Nat) : Raw :=
  ⟨width, fun _ _ => 0, fun _ => 0, 0, 0, [], false, []⟩

def laneMessage (s : Raw) (lane len : Nat) : Message :=
  List.ofFn (fun i : Fin len => s.lanes lane i)

def pending (s : Raw) : List Message :=
  (List.range s.count).map (fun lane => laneMessage s lane (s.lengths lane))

def flush (s : Raw) : Raw :=
  let msgs := pending s
  { s with
    count := 0
    hashed := s.hashed ++ msgs
    serial := if 1 < s.width ∧ s.count = s.width then s.serial
              else msgs.getLast?.getD s.serial }

def append (s : Raw) (p : Message) : Raw :=
  if s.spilled then { s with serial := s.serial ++ p }
  else if s.curLen + p.length ≤ 1024 then
    { s with
      curLen := s.curLen + p.length
      lanes := fun lane i =>
        if lane = s.count ∧ s.curLen ≤ i ∧ i < s.curLen + p.length
        then p[i - s.curLen]!
        else s.lanes lane i }
  else
    { s with
      curLen := 0
      serial := laneMessage s s.count s.curLen ++ p
      spilled := true }

def finish (s : Raw) : Raw :=
  if s.spilled then
    { s with hashed := s.hashed ++ [s.serial], spilled := false }
  else
    let len := s.curLen
    let padded := ((max 1 len + 63) / 64) * 64
    let t := { s with
      lanes := fun lane i =>
        if lane = s.count ∧ len ≤ i ∧ i < padded then 0 else s.lanes lane i
      lengths := fun lane => if lane = s.count then len else s.lengths lane
      count := s.count + 1
      curLen := 0 }
    if t.count = t.width then flush t else t

def addMessage (s : Raw) (m : Message) : Raw := finish (append s m)

def discard (s : Raw) : Raw := { s with curLen := 0, spilled := false }

def take (s : Raw) : List Message × Raw :=
  let t := if s.count = 0 then s else flush s
  (t.hashed, { t with hashed := [] })

def clean (s : Raw) : Bool := s.curLen == 0 && !s.spilled

def committed : List Message := [[65], [66], [67], [68], [69], [70], [71], [72], [73]]

-- start_message is an unchanged state; dropping would call discard. The user
-- instead forgets the guard after adding Z, so no discard runs before take.
def forgottenState (w : Nat) : Raw :=
  append (committed.foldl addMessage (initial w)) [90]

def forgottenTrace (w : Nat) : List Message × List Message :=
  let (first, s) := take (forgottenState w)
  let (second, _) := take (addMessage s [67])
  (first, second)

theorem width1_counterexample : forgottenTrace 1 = (committed, [[90, 67]]) := by decide

theorem width8_counterexample : forgottenTrace 8 = (committed, [[73, 67]]) := by decide

theorem width16_counterexample : forgottenTrace 16 = (committed, [[65, 67]]) := by decide

-- Debug assertions reject this state; release take leaves the forgotten bytes
-- live while resetting count, which changes the lane selected by curLen.
theorem debug_rejects_all_widths :
    clean (forgottenState 1) = false ∧ clean (forgottenState 8) = false ∧
    clean (forgottenState 16) = false := by decide

theorem actual_inputs_differ_from_new_message :
    (forgottenTrace 1).2 ≠ [[67]] ∧ (forgottenTrace 8).2 ≠ [[67]] ∧
    (forgottenTrace 16).2 ≠ [[67]] := by
  simp [width1_counterexample, width8_counterexample, width16_counterexample]

theorem actual_inputs_differ_between_widths :
    (forgottenTrace 1).2 ≠ (forgottenTrace 8).2 ∧
    (forgottenTrace 8).2 ≠ (forgottenTrace 16).2 ∧
    (forgottenTrace 1).2 ≠ (forgottenTrace 16).2 := by
  simp [width1_counterexample, width8_counterexample, width16_counterexample]

-- The other conjunct of the weak clean condition matters too: an already
-- spilled guard has curLen=0 yet retains all its data in serial_hasher.
def forgottenSpilled (w : Nat) : Raw := append (initial w) (List.replicate 1025 7)

theorem curLen_zero_alone_is_insufficient :
    (forgottenSpilled 8).curLen = 0 ∧ (forgottenSpilled 8).spilled = true ∧
    clean (forgottenSpilled 8) = false := by decide

theorem spilled_release_keeps_forgotten_prefix :
    let (_, s) := take (forgottenSpilled 8)
    (take (addMessage s [67])).1 = [List.replicate 1025 7 ++ [67]] := by decide

#print axioms width1_counterexample
#print axioms width8_counterexample
#print axioms width16_counterexample
#print axioms actual_inputs_differ_between_widths
#print axioms spilled_release_keeps_forgotten_prefix

end AgaveForgotten
