import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarExecutionPrefix
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullInput
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullTerminal

/-! Register framing across successive original scalar bb4 iterations. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR
open ScalarFull
open Spec

theorem before_trans (h : Before bound E₀ E₁) (h' : Before bound E₁ E₂) : Before bound E₀ E₂ :=
  ⟨h'.1.trans h.1, fun i hi => (h'.2 i hi).trans (h.2 i hi)⟩
theorem before_weaken (h : Before bound E₀ E₁) (hb : small ≤ bound) : Before small E₀ E₁ :=
  ⟨h.1, fun i hi => h.2 i (lt_of_lt_of_le hi hb)⟩
theorem frame_before (h : Frame E₀ E₁) : Before 250 E₀ E₁ := h

theorem constants_before (h : Constants E₀ kp) (hb : Before 173 E₀ E₁) : Constants E₁ kp := by
  constructor
  · rw [hb.read_val 1 (by decide) (by rfl)]; exact h.v1
  · rw [hb.read_val 9 (by decide) (by rfl)]; exact h.v9
  · rw [hb.read_val 19 (by decide) (by rfl)]; exact h.v19
  · rw [hb.read_val 20 (by decide) (by rfl)]; exact h.v20
  · rw [hb.read_val 21 (by decide) (by rfl)]; exact h.v21
  · rw [hb.read_val 22 (by decide) (by rfl)]; exact h.v22
  · rw [hb.read_val 24 (by decide) (by rfl)]; exact h.v24
  · rw [hb.read_val 25 (by decide) (by rfl)]; exact h.v25
  · rw [hb.read_val 26 (by decide) (by rfl)]; exact h.v26
  · rw [hb.read_val 42 (by decide) (by rfl)]; exact h.v42
  · rw [hb.read_val 43 (by decide) (by rfl)]; exact h.v43
  · rw [hb.read_val 44 (by decide) (by rfl)]; exact h.v44
  · rw [hb.read_val 45 (by decide) (by rfl)]; exact h.v45
  · rw [hb.read_val 23 (by decide) (by rfl)]; exact h.k00
  · rw [hb.read_val 27 (by decide) (by rfl)]; exact h.k01
  · rw [hb.read_val 28 (by decide) (by rfl)]; exact h.k02
  · rw [hb.read_val 29 (by decide) (by rfl)]; exact h.k03
  · rw [hb.read_val 30 (by decide) (by rfl)]; exact h.k04
  · rw [hb.read_val 31 (by decide) (by rfl)]; exact h.k05
  · rw [hb.read_val 32 (by decide) (by rfl)]; exact h.k06
  · rw [hb.read_val 33 (by decide) (by rfl)]; exact h.k07
  · rw [hb.read_val 34 (by decide) (by rfl)]; exact h.k08
  · rw [hb.read_val 35 (by decide) (by rfl)]; exact h.k09
  · rw [hb.read_val 36 (by decide) (by rfl)]; exact h.k10
  · rw [hb.read_val 37 (by decide) (by rfl)]; exact h.k11
  · rw [hb.read_val 38 (by decide) (by rfl)]; exact h.k12
  · rw [hb.read_val 39 (by decide) (by rfl)]; exact h.k13
  · rw [hb.read_val 40 (by decide) (by rfl)]; exact h.k14
  · rw [hb.read_val 41 (by decide) (by rfl)]; exact h.k15
  · rw [hb.read_val 46 (by decide) (by rfl)]; exact h.k16
  · rw [hb.read_val 48 (by decide) (by rfl)]; exact h.k17
  · rw [hb.read_val 50 (by decide) (by rfl)]; exact h.k18
  · rw [hb.read_val 52 (by decide) (by rfl)]; exact h.k19
  · rw [hb.read_val 54 (by decide) (by rfl)]; exact h.k20
  · rw [hb.read_val 56 (by decide) (by rfl)]; exact h.k21
  · rw [hb.read_val 58 (by decide) (by rfl)]; exact h.k22
  · rw [hb.read_val 60 (by decide) (by rfl)]; exact h.k23
  · rw [hb.read_val 62 (by decide) (by rfl)]; exact h.k24
  · rw [hb.read_val 64 (by decide) (by rfl)]; exact h.k25
  · rw [hb.read_val 66 (by decide) (by rfl)]; exact h.k26
  · rw [hb.read_val 68 (by decide) (by rfl)]; exact h.k27
  · rw [hb.read_val 70 (by decide) (by rfl)]; exact h.k28
  · rw [hb.read_val 72 (by decide) (by rfl)]; exact h.k29
  · rw [hb.read_val 74 (by decide) (by rfl)]; exact h.k30
  · rw [hb.read_val 76 (by decide) (by rfl)]; exact h.k31
  · rw [hb.read_val 78 (by decide) (by rfl)]; exact h.k32
  · rw [hb.read_val 80 (by decide) (by rfl)]; exact h.k33
  · rw [hb.read_val 82 (by decide) (by rfl)]; exact h.k34
  · rw [hb.read_val 84 (by decide) (by rfl)]; exact h.k35
  · rw [hb.read_val 86 (by decide) (by rfl)]; exact h.k36
  · rw [hb.read_val 88 (by decide) (by rfl)]; exact h.k37
  · rw [hb.read_val 90 (by decide) (by rfl)]; exact h.k38
  · rw [hb.read_val 92 (by decide) (by rfl)]; exact h.k39
  · rw [hb.read_val 94 (by decide) (by rfl)]; exact h.k40
  · rw [hb.read_val 96 (by decide) (by rfl)]; exact h.k41
  · rw [hb.read_val 98 (by decide) (by rfl)]; exact h.k42
  · rw [hb.read_val 100 (by decide) (by rfl)]; exact h.k43
  · rw [hb.read_val 102 (by decide) (by rfl)]; exact h.k44
  · rw [hb.read_val 104 (by decide) (by rfl)]; exact h.k45
  · rw [hb.read_val 106 (by decide) (by rfl)]; exact h.k46
  · rw [hb.read_val 108 (by decide) (by rfl)]; exact h.k47
  · rw [hb.read_val 110 (by decide) (by rfl)]; exact h.k48
  · rw [hb.read_val 112 (by decide) (by rfl)]; exact h.k49
  · rw [hb.read_val 114 (by decide) (by rfl)]; exact h.k50
  · rw [hb.read_val 116 (by decide) (by rfl)]; exact h.k51
  · rw [hb.read_val 118 (by decide) (by rfl)]; exact h.k52
  · rw [hb.read_val 120 (by decide) (by rfl)]; exact h.k53
  · rw [hb.read_val 122 (by decide) (by rfl)]; exact h.k54
  · rw [hb.read_val 124 (by decide) (by rfl)]; exact h.k55
  · rw [hb.read_val 126 (by decide) (by rfl)]; exact h.k56
  · rw [hb.read_val 128 (by decide) (by rfl)]; exact h.k57
  · rw [hb.read_val 130 (by decide) (by rfl)]; exact h.k58
  · rw [hb.read_val 132 (by decide) (by rfl)]; exact h.k59
  · rw [hb.read_val 134 (by decide) (by rfl)]; exact h.k60
  · rw [hb.read_val 136 (by decide) (by rfl)]; exact h.k61
  · rw [hb.read_val 138 (by decide) (by rfl)]; exact h.k62
  · rw [hb.read_val 140 (by decide) (by rfl)]; exact h.k63
  · rw [hb.read_val 142 (by decide) (by rfl)]; exact h.k64
  · rw [hb.read_val 144 (by decide) (by rfl)]; exact h.k65
  · rw [hb.read_val 146 (by decide) (by rfl)]; exact h.k66
  · rw [hb.read_val 148 (by decide) (by rfl)]; exact h.k67
  · rw [hb.read_val 150 (by decide) (by rfl)]; exact h.k68
  · rw [hb.read_val 152 (by decide) (by rfl)]; exact h.k69
  · rw [hb.read_val 154 (by decide) (by rfl)]; exact h.k70
  · rw [hb.read_val 156 (by decide) (by rfl)]; exact h.k71
  · rw [hb.read_val 158 (by decide) (by rfl)]; exact h.k72
  · rw [hb.read_val 160 (by decide) (by rfl)]; exact h.k73
  · rw [hb.read_val 162 (by decide) (by rfl)]; exact h.k74
  · rw [hb.read_val 164 (by decide) (by rfl)]; exact h.k75
  · rw [hb.read_val 166 (by decide) (by rfl)]; exact h.k76
  · rw [hb.read_val 168 (by decide) (by rfl)]; exact h.k77
  · rw [hb.read_val 170 (by decide) (by rfl)]; exact h.k78
  · rw [hb.read_val 172 (by decide) (by rfl)]; exact h.k79

theorem store_before (h : StoreReady E₀ chain) (hb : Before 193 E₀ E₁) : StoreReady E₁ chain := by
  constructor
  · change E₁.args 0 = .value chain
    rw [hb.1]
    exact h.chainPtr
  · rw [hb.read_val 179 (by decide) (by rfl)]; exact h.p1
  · rw [hb.read_val 180 (by decide) (by rfl)]; exact h.p2
  · rw [hb.read_val 181 (by decide) (by rfl)]; exact h.p3
  · rw [hb.read_val 182 (by decide) (by rfl)]; exact h.p4
  · rw [hb.read_val 183 (by decide) (by rfl)]; exact h.p5
  · rw [hb.read_val 184 (by decide) (by rfl)]; exact h.p6
  · rw [hb.read_val 185 (by decide) (by rfl)]; exact h.p7

theorem loop_before (E : Env program.Γ) (next : Pointer) (initial : Spec.State) :
    Before 193 E (scalarLoopEnv E next initial) := by
  unfold scalarLoopEnv
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem loop_initial (E : Env program.Γ) (next : Pointer) (initial : Spec.State) :
    InitialReady (scalarLoopEnv E next initial) initial := by
  constructor <;> simp [scalarLoopEnv, mlir_env]

theorem loop_cursor (E : Env program.Γ) (next : Pointer) (initial : Spec.State) :
    (scalarLoopEnv E next initial).read (%200) = .value next := by
  simp [scalarLoopEnv, mlir_env]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
