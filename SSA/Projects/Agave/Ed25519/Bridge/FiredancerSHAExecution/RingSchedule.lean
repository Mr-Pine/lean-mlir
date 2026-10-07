import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic

/-! The scalar C core's sixteen-word circular schedule. Its invariant relates
physical ring slots to the append-only FIPS schedule. This layer has no machine
execution premise; the separate memory loop must establish these observations. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge

abbrev Ring := Nat → Word

/-- At the start of round r, the ring contains exactly W[r-16..r-1]. -/
def RingRepresents (q : Ring) (block : Bytes) (r : Nat) : Prop :=
  ∀ j, j < 16 → q ((r + j) % 16) = (schedule block).getD (r - 16 + j) 0

def ringWord (q : Ring) (r : Nat) : Word :=
  scheduleWord (q (r % 16)) (q ((r + 1) % 16))
    (q ((r + 9) % 16)) (q ((r + 14) % 16))

def ringStep (q : Ring) (r : Nat) : Ring :=
  fun i => if i = r % 16 then ringWord q r else q i

theorem ringWord_spec (q : Ring) (block : Bytes) (r : Nat)
    (h : RingRepresents q block r) (hlo : 16 ≤ r) (hhi : r < 80) :
    ringWord q r = (schedule block).getD r 0 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h9 := h 9 (by decide)
  have h14 := h 14 (by decide)
  simp only [Nat.add_zero] at h0
  rw [ringWord, h0, h1, h9, h14]
  simpa only [show r - 16 + 1 = r - 15 by omega,
    show r - 16 + 9 = r - 7 by omega, show r - 16 + 14 = r - 2 by omega] using
    scheduleWord_spec block r hlo hhi

/-- Overwriting exactly the oldest word establishes the next ring invariant. -/
theorem ringStep_represents (q : Ring) (block : Bytes) (r : Nat)
    (h : RingRepresents q block r) (hlo : 16 ≤ r) (hhi : r < 80) :
    RingRepresents (ringStep q r) block (r + 1) := by
  intro j hj
  by_cases hlast : j = 15
  · subst j
    simp only [ringStep, show (r + 1 + 15) % 16 = r % 16 by omega,
      ite_true, ringWord_spec q block r h hlo hhi,
      show r + 1 - 16 + 15 = r by omega]
  · have hslot : (r + 1 + j) % 16 ≠ r % 16 := by omega
    rw [ringStep, ite_eq_right hslot]
    convert h (j + 1) (by omega) using 1 <;> congr 1 <;> omega

def initialRing (block : Bytes) : Ring := fun i => readWordBE block i

theorem initialRing_represents (block : Bytes) :
    RingRepresents (initialRing block) block 16 := by
  intro j hj
  simp only [initialRing, show (16 + j) % 16 = j by omega,
    Nat.sub_self, Nat.zero_add]
  exact (schedule_initial block j hj).symm

/-- Pure state of the C second loop, with the original source round ordering. -/
def laterLoop (q : Ring) (s : State) (r : Nat) : Nat → Ring × State
  | 0 => (q, s)
  | n + 1 =>
    let previous := laterLoop q s r n
    let t := r + n
    (ringStep previous.1 t,
      laterRound previous.2 (ringWord previous.1 t) (constants.toList.getD t 0))

theorem laterLoop_represents (q : Ring) (s : State) (block : Bytes) (r n : Nat)
    (h : RingRepresents q block r) (hlo : 16 ≤ r) (hhi : r + n ≤ 80) :
    RingRepresents (laterLoop q s r n).1 block (r + n) ∧
    (laterLoop q s r n).2 = roundsFrom s (schedule block) r n := by
  induction n with
  | zero => exact ⟨by simpa [laterLoop] using h, rfl⟩
  | succ n ih =>
    obtain ⟨hring, hstate⟩ := ih (by omega)
    constructor
    · simpa only [laterLoop, Nat.add_assoc] using
        ringStep_represents (laterLoop q s r n).1 block (r + n) hring (by omega) (by omega)
    · simp only [laterLoop, laterRound_eq, hstate,
        ringWord_spec (laterLoop q s r n).1 block (r + n) hring (by omega) (by omega),
        roundsFrom]

/-- The source ring loop's sixty-four rounds complete the standard eighty-round
working state when started after the initial sixteen rounds. -/
theorem laterLoop_finishes (initial : State) (block : Bytes) :
    (laterLoop (initialRing block) (roundsFrom initial (schedule block) 0 16) 16 64).2 =
      roundsFrom initial (schedule block) 0 80 := by
  have h := (laterLoop_represents (initialRing block)
    (roundsFrom initial (schedule block) 0 16) block 16 64
    (initialRing_represents block) (by decide) (by decide)).2
  rw [h]
  exact (roundsFrom_add initial (schedule block) 0 16 64).symm

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
