import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarExecutionRound
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Globals
import SSA.Projects.Agave.Ed25519.Proof.SHA512.ScheduleSpec

/-! Shared invariants for exact instruction slices of the scalar compressor.
Only the live message words, working state, and compiler's cached B&C product
are carried between rounds. The original imported bb4 remains unchanged. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def ScheduleReady (w : Nat → Word) : Prop :=
  ∀ r, 16 ≤ r → r < 80 →
    w r = smallSigma1 (w (r - 2)) + w (r - 7) +
      smallSigma0 (w (r - 15)) + w (r - 16)

theorem schedule_ready (block : Agave.Ed25519.Bridge.Challenge.Bytes) :
    ScheduleReady (fun r => (Spec.schedule block).getD r 0) := by
  intro r hlo hhi
  have h := schedule_recurrence block (r - 16) (by omega)
  simpa only [show 16 + (r - 16) = r by omega,
    show r - 16 + 14 = r - 2 by omega,
    show r - 16 + 9 = r - 7 by omega,
    show r - 16 + 1 = r - 15 by omega] using h

/-- Instructions from the round slices only write registers numbered at
least 250. Caller arguments, original state, addresses and constants remain. -/
def Frame (before after : Env program.Γ) : Prop :=
  after.args = before.args ∧ ∀ i : Fin program.Γ.n, i.val < 250 →
    after.vals i = before.vals i

theorem Frame.refl (E : Env program.Γ) : Frame E E := ⟨rfl, fun _ _ => rfl⟩
theorem Frame.trans (h₀ : Frame E₀ E₁) (h₁ : Frame E₁ E₂) : Frame E₀ E₂ :=
  ⟨h₁.1.trans h₀.1, fun i hi => (h₁.2 i hi).trans (h₀.2 i hi)⟩
theorem Frame.write (h : Frame E₀ E₁) (dst : Dst program.Γ t) (v : t.denote)
    (hlo : 250 ≤ dst.i.val) : Frame E₀ (E₁.write dst v) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  have hne : i ≠ dst.i := by intro heq; have := congrArg Fin.val heq; omega
  simpa only [Env.write, Env.set, dite_eq_right hne] using h.2 i hi

theorem Frame.read_val (h : Frame E₀ E₁) (i : Fin program.Γ.n)
    (hi : i.val < 250) (ht : program.Γ.ty i = t) :
    E₁.read (.val i ht) = E₀.read (.val i ht) := by
  simp only [Env.read, h.2 i hi]

structure Constants (E : Env program.Γ) (kp : Pointer) : Prop where
  v1 : E.read (%1) = .value 7#64
  v9 : E.read (%9) = .value 56#64
  v19 : E.read (%19) = .value 50#64
  v20 : E.read (%20) = .value 46#64
  v21 : E.read (%21) = .value 23#64
  v22 : E.read (%22) = .value (-1 : Word)
  v24 : E.read (%24) = .value 36#64
  v25 : E.read (%25) = .value 30#64
  v26 : E.read (%26) = .value 25#64
  v42 : E.read (%42) = .value 63#64
  v43 : E.read (%43) = .value 45#64
  v44 : E.read (%44) = .value 3#64
  v45 : E.read (%45) = .value 6#64
  k00 : E.read (%23) = .value (kp.add 0#64)
  k01 : E.read (%27) = .value (kp.add 8#64)
  k02 : E.read (%28) = .value (kp.add 16#64)
  k03 : E.read (%29) = .value (kp.add 24#64)
  k04 : E.read (%30) = .value (kp.add 32#64)
  k05 : E.read (%31) = .value (kp.add 40#64)
  k06 : E.read (%32) = .value (kp.add 48#64)
  k07 : E.read (%33) = .value (kp.add 56#64)
  k08 : E.read (%34) = .value (kp.add 64#64)
  k09 : E.read (%35) = .value (kp.add 72#64)
  k10 : E.read (%36) = .value (kp.add 80#64)
  k11 : E.read (%37) = .value (kp.add 88#64)
  k12 : E.read (%38) = .value (kp.add 96#64)
  k13 : E.read (%39) = .value (kp.add 104#64)
  k14 : E.read (%40) = .value (kp.add 112#64)
  k15 : E.read (%41) = .value (kp.add 120#64)
  k16 : E.read (%46) = .value (kp.add 128#64)
  k17 : E.read (%48) = .value (kp.add 136#64)
  k18 : E.read (%50) = .value (kp.add 144#64)
  k19 : E.read (%52) = .value (kp.add 152#64)
  k20 : E.read (%54) = .value (kp.add 160#64)
  k21 : E.read (%56) = .value (kp.add 168#64)
  k22 : E.read (%58) = .value (kp.add 176#64)
  k23 : E.read (%60) = .value (kp.add 184#64)
  k24 : E.read (%62) = .value (kp.add 192#64)
  k25 : E.read (%64) = .value (kp.add 200#64)
  k26 : E.read (%66) = .value (kp.add 208#64)
  k27 : E.read (%68) = .value (kp.add 216#64)
  k28 : E.read (%70) = .value (kp.add 224#64)
  k29 : E.read (%72) = .value (kp.add 232#64)
  k30 : E.read (%74) = .value (kp.add 240#64)
  k31 : E.read (%76) = .value (kp.add 248#64)
  k32 : E.read (%78) = .value (kp.add 256#64)
  k33 : E.read (%80) = .value (kp.add 264#64)
  k34 : E.read (%82) = .value (kp.add 272#64)
  k35 : E.read (%84) = .value (kp.add 280#64)
  k36 : E.read (%86) = .value (kp.add 288#64)
  k37 : E.read (%88) = .value (kp.add 296#64)
  k38 : E.read (%90) = .value (kp.add 304#64)
  k39 : E.read (%92) = .value (kp.add 312#64)
  k40 : E.read (%94) = .value (kp.add 320#64)
  k41 : E.read (%96) = .value (kp.add 328#64)
  k42 : E.read (%98) = .value (kp.add 336#64)
  k43 : E.read (%100) = .value (kp.add 344#64)
  k44 : E.read (%102) = .value (kp.add 352#64)
  k45 : E.read (%104) = .value (kp.add 360#64)
  k46 : E.read (%106) = .value (kp.add 368#64)
  k47 : E.read (%108) = .value (kp.add 376#64)
  k48 : E.read (%110) = .value (kp.add 384#64)
  k49 : E.read (%112) = .value (kp.add 392#64)
  k50 : E.read (%114) = .value (kp.add 400#64)
  k51 : E.read (%116) = .value (kp.add 408#64)
  k52 : E.read (%118) = .value (kp.add 416#64)
  k53 : E.read (%120) = .value (kp.add 424#64)
  k54 : E.read (%122) = .value (kp.add 432#64)
  k55 : E.read (%124) = .value (kp.add 440#64)
  k56 : E.read (%126) = .value (kp.add 448#64)
  k57 : E.read (%128) = .value (kp.add 456#64)
  k58 : E.read (%130) = .value (kp.add 464#64)
  k59 : E.read (%132) = .value (kp.add 472#64)
  k60 : E.read (%134) = .value (kp.add 480#64)
  k61 : E.read (%136) = .value (kp.add 488#64)
  k62 : E.read (%138) = .value (kp.add 496#64)
  k63 : E.read (%140) = .value (kp.add 504#64)
  k64 : E.read (%142) = .value (kp.add 512#64)
  k65 : E.read (%144) = .value (kp.add 520#64)
  k66 : E.read (%146) = .value (kp.add 528#64)
  k67 : E.read (%148) = .value (kp.add 536#64)
  k68 : E.read (%150) = .value (kp.add 544#64)
  k69 : E.read (%152) = .value (kp.add 552#64)
  k70 : E.read (%154) = .value (kp.add 560#64)
  k71 : E.read (%156) = .value (kp.add 568#64)
  k72 : E.read (%158) = .value (kp.add 576#64)
  k73 : E.read (%160) = .value (kp.add 584#64)
  k74 : E.read (%162) = .value (kp.add 592#64)
  k75 : E.read (%164) = .value (kp.add 600#64)
  k76 : E.read (%166) = .value (kp.add 608#64)
  k77 : E.read (%168) = .value (kp.add 616#64)
  k78 : E.read (%170) = .value (kp.add 624#64)
  k79 : E.read (%172) = .value (kp.add 632#64)

theorem Constants.of_frame (h : Constants E₀ kp) (hf : Frame E₀ E₁) :
    Constants E₁ kp := by
  constructor
  · rw [hf.read_val 1 (by decide) (by rfl)]; exact h.v1
  · rw [hf.read_val 9 (by decide) (by rfl)]; exact h.v9
  · rw [hf.read_val 19 (by decide) (by rfl)]; exact h.v19
  · rw [hf.read_val 20 (by decide) (by rfl)]; exact h.v20
  · rw [hf.read_val 21 (by decide) (by rfl)]; exact h.v21
  · rw [hf.read_val 22 (by decide) (by rfl)]; exact h.v22
  · rw [hf.read_val 24 (by decide) (by rfl)]; exact h.v24
  · rw [hf.read_val 25 (by decide) (by rfl)]; exact h.v25
  · rw [hf.read_val 26 (by decide) (by rfl)]; exact h.v26
  · rw [hf.read_val 42 (by decide) (by rfl)]; exact h.v42
  · rw [hf.read_val 43 (by decide) (by rfl)]; exact h.v43
  · rw [hf.read_val 44 (by decide) (by rfl)]; exact h.v44
  · rw [hf.read_val 45 (by decide) (by rfl)]; exact h.v45
  · rw [hf.read_val 23 (by decide) (by rfl)]; exact h.k00
  · rw [hf.read_val 27 (by decide) (by rfl)]; exact h.k01
  · rw [hf.read_val 28 (by decide) (by rfl)]; exact h.k02
  · rw [hf.read_val 29 (by decide) (by rfl)]; exact h.k03
  · rw [hf.read_val 30 (by decide) (by rfl)]; exact h.k04
  · rw [hf.read_val 31 (by decide) (by rfl)]; exact h.k05
  · rw [hf.read_val 32 (by decide) (by rfl)]; exact h.k06
  · rw [hf.read_val 33 (by decide) (by rfl)]; exact h.k07
  · rw [hf.read_val 34 (by decide) (by rfl)]; exact h.k08
  · rw [hf.read_val 35 (by decide) (by rfl)]; exact h.k09
  · rw [hf.read_val 36 (by decide) (by rfl)]; exact h.k10
  · rw [hf.read_val 37 (by decide) (by rfl)]; exact h.k11
  · rw [hf.read_val 38 (by decide) (by rfl)]; exact h.k12
  · rw [hf.read_val 39 (by decide) (by rfl)]; exact h.k13
  · rw [hf.read_val 40 (by decide) (by rfl)]; exact h.k14
  · rw [hf.read_val 41 (by decide) (by rfl)]; exact h.k15
  · rw [hf.read_val 46 (by decide) (by rfl)]; exact h.k16
  · rw [hf.read_val 48 (by decide) (by rfl)]; exact h.k17
  · rw [hf.read_val 50 (by decide) (by rfl)]; exact h.k18
  · rw [hf.read_val 52 (by decide) (by rfl)]; exact h.k19
  · rw [hf.read_val 54 (by decide) (by rfl)]; exact h.k20
  · rw [hf.read_val 56 (by decide) (by rfl)]; exact h.k21
  · rw [hf.read_val 58 (by decide) (by rfl)]; exact h.k22
  · rw [hf.read_val 60 (by decide) (by rfl)]; exact h.k23
  · rw [hf.read_val 62 (by decide) (by rfl)]; exact h.k24
  · rw [hf.read_val 64 (by decide) (by rfl)]; exact h.k25
  · rw [hf.read_val 66 (by decide) (by rfl)]; exact h.k26
  · rw [hf.read_val 68 (by decide) (by rfl)]; exact h.k27
  · rw [hf.read_val 70 (by decide) (by rfl)]; exact h.k28
  · rw [hf.read_val 72 (by decide) (by rfl)]; exact h.k29
  · rw [hf.read_val 74 (by decide) (by rfl)]; exact h.k30
  · rw [hf.read_val 76 (by decide) (by rfl)]; exact h.k31
  · rw [hf.read_val 78 (by decide) (by rfl)]; exact h.k32
  · rw [hf.read_val 80 (by decide) (by rfl)]; exact h.k33
  · rw [hf.read_val 82 (by decide) (by rfl)]; exact h.k34
  · rw [hf.read_val 84 (by decide) (by rfl)]; exact h.k35
  · rw [hf.read_val 86 (by decide) (by rfl)]; exact h.k36
  · rw [hf.read_val 88 (by decide) (by rfl)]; exact h.k37
  · rw [hf.read_val 90 (by decide) (by rfl)]; exact h.k38
  · rw [hf.read_val 92 (by decide) (by rfl)]; exact h.k39
  · rw [hf.read_val 94 (by decide) (by rfl)]; exact h.k40
  · rw [hf.read_val 96 (by decide) (by rfl)]; exact h.k41
  · rw [hf.read_val 98 (by decide) (by rfl)]; exact h.k42
  · rw [hf.read_val 100 (by decide) (by rfl)]; exact h.k43
  · rw [hf.read_val 102 (by decide) (by rfl)]; exact h.k44
  · rw [hf.read_val 104 (by decide) (by rfl)]; exact h.k45
  · rw [hf.read_val 106 (by decide) (by rfl)]; exact h.k46
  · rw [hf.read_val 108 (by decide) (by rfl)]; exact h.k47
  · rw [hf.read_val 110 (by decide) (by rfl)]; exact h.k48
  · rw [hf.read_val 112 (by decide) (by rfl)]; exact h.k49
  · rw [hf.read_val 114 (by decide) (by rfl)]; exact h.k50
  · rw [hf.read_val 116 (by decide) (by rfl)]; exact h.k51
  · rw [hf.read_val 118 (by decide) (by rfl)]; exact h.k52
  · rw [hf.read_val 120 (by decide) (by rfl)]; exact h.k53
  · rw [hf.read_val 122 (by decide) (by rfl)]; exact h.k54
  · rw [hf.read_val 124 (by decide) (by rfl)]; exact h.k55
  · rw [hf.read_val 126 (by decide) (by rfl)]; exact h.k56
  · rw [hf.read_val 128 (by decide) (by rfl)]; exact h.k57
  · rw [hf.read_val 130 (by decide) (by rfl)]; exact h.k58
  · rw [hf.read_val 132 (by decide) (by rfl)]; exact h.k59
  · rw [hf.read_val 134 (by decide) (by rfl)]; exact h.k60
  · rw [hf.read_val 136 (by decide) (by rfl)]; exact h.k61
  · rw [hf.read_val 138 (by decide) (by rfl)]; exact h.k62
  · rw [hf.read_val 140 (by decide) (by rfl)]; exact h.k63
  · rw [hf.read_val 142 (by decide) (by rfl)]; exact h.k64
  · rw [hf.read_val 144 (by decide) (by rfl)]; exact h.k65
  · rw [hf.read_val 146 (by decide) (by rfl)]; exact h.k66
  · rw [hf.read_val 148 (by decide) (by rfl)]; exact h.k67
  · rw [hf.read_val 150 (by decide) (by rfl)]; exact h.k68
  · rw [hf.read_val 152 (by decide) (by rfl)]; exact h.k69
  · rw [hf.read_val 154 (by decide) (by rfl)]; exact h.k70
  · rw [hf.read_val 156 (by decide) (by rfl)]; exact h.k71
  · rw [hf.read_val 158 (by decide) (by rfl)]; exact h.k72
  · rw [hf.read_val 160 (by decide) (by rfl)]; exact h.k73
  · rw [hf.read_val 162 (by decide) (by rfl)]; exact h.k74
  · rw [hf.read_val 164 (by decide) (by rfl)]; exact h.k75
  · rw [hf.read_val 166 (by decide) (by rfl)]; exact h.k76
  · rw [hf.read_val 168 (by decide) (by rfl)]; exact h.k77
  · rw [hf.read_val 170 (by decide) (by rfl)]; exact h.k78
  · rw [hf.read_val 172 (by decide) (by rfl)]; exact h.k79

def KRead (mem : MemoryState) (kp : Pointer) : Prop :=
  ∀ r : Fin 80, Fits mem (kp.add (BitVec.ofNat 64 (8 * r.val))) 64 ∧
    mem.readAt (kp.add (BitVec.ofNat 64 (8 * r.val))) 64 = constants.toList.getD r.val 0

theorem scalar_choice_or (e f g : Word) :
    (e &&& f) ||| (g &&& (e ^^^ (-1 : Word))) =
      (e &&& f) + (g &&& (e ^^^ (-1 : Word))) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (-1 : Word).getLsbD i = true := by
    change (BitVec.allOnes 64).getLsbD i = true
    simp only [BitVec.getLsbD_allOnes, hi, decide_true]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, hm]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;>
    simp [BitVec.getLsbD]

theorem scalar_majority (a b c : Word) :
    (a &&& (b ^^^ c)) ^^^ (b &&& c) = majority a b c := by
  simpa only [BitVec.and_comm, BitVec.xor_comm] using majority_source a b c

theorem fshl63_rotateRight (x : Word) :
    Operation.fshl (.value x) (.value x) (.value 63#64) =
      .value (x.rotateRight 1) := by
  simpa only [Operation.fshl, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg LeanMLIR.RIR.PoisonOr.value (Spec.rotateRight1_fshl x)

theorem fshl56_rotateRight (x : Word) :
    Operation.fshl (.value x) (.value x) (.value 56#64) =
      .value (x.rotateRight 8) := by
  simpa only [Operation.fshl, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg LeanMLIR.RIR.PoisonOr.value (Spec.rotateRight8_fshl x)

theorem fshl45_rotateRight (x : Word) :
    Operation.fshl (.value x) (.value x) (.value 45#64) =
      .value (x.rotateRight 19) := by
  simpa only [Operation.fshl, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg LeanMLIR.RIR.PoisonOr.value (Spec.rotateRight19_fshl x)

theorem fshl3_rotateRight (x : Word) :
    Operation.fshl (.value x) (.value x) (.value 3#64) =
      .value (x.rotateRight 61) := by
  simpa only [Operation.fshl, LeanMLIR.RIR.PoisonOr.value_bind, LeanMLIR.RIR.PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg LeanMLIR.RIR.PoisonOr.value (Spec.rotateRight61_fshl x)

/-- Sequential composition of exact original-body instruction slices. -/
theorem runBodyFrom_slice (E E' : Env program.Γ) (start count : Nat)
    (state : GlobalState)
    (h : List.foldlM Instr.run E (program.bb4.body.drop start |>.take count) state =
      .value (E', state)) :
    program.bb4.runBodyFrom E start state =
      program.bb4.runBodyFrom E' (start + count) state := by
  unfold BasicBlock.runBodyFrom
  have hs := List.take_append_drop count (program.bb4.body.drop start)
  rw [← hs, List.foldlM_append]
  change (List.foldlM Instr.run E (program.bb4.body.drop start |>.take count) state >>= _) = _
  rw [h]
  dsimp
  simp only [List.drop_drop, Nat.add_comm]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
