import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters

/-! Final scalar round and compiler-fused feed-forward, exact bb4 slice 2924..2969. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

structure InitialReady (E : Env program.Γ) (initial : Spec.State) : Prop where
  a : E.read (%201) = .value initial.a
  b : E.read (%199) = .value initial.b
  c : E.read (%198) = .value initial.c
  d : E.read (%197) = .value initial.d
  e : E.read (%196) = .value initial.e
  f : E.read (%195) = .value initial.f
  g : E.read (%194) = .value initial.g
  h : E.read (%193) = .value initial.h

theorem InitialReady.of_frame {initial : Spec.State} (h : InitialReady E₀ initial) (hf : Frame E₀ E₁) : InitialReady E₁ initial := by
  constructor
  · rw [hf.read_val 201 (by decide) (by rfl)]; exact h.a
  · rw [hf.read_val 199 (by decide) (by rfl)]; exact h.b
  · rw [hf.read_val 198 (by decide) (by rfl)]; exact h.c
  · rw [hf.read_val 197 (by decide) (by rfl)]; exact h.d
  · rw [hf.read_val 196 (by decide) (by rfl)]; exact h.e
  · rw [hf.read_val 195 (by decide) (by rfl)]; exact h.f
  · rw [hf.read_val 194 (by decide) (by rfl)]; exact h.g
  · rw [hf.read_val 193 (by decide) (by rfl)]; exact h.h

structure ResultReady (E : Env program.Γ) (result : Spec.State) : Prop where
  a : E.read (%3161) = .value result.a
  b : E.read (%3162) = .value result.b
  c : E.read (%3163) = .value result.c
  d : E.read (%3164) = .value result.d
  e : E.read (%3166) = .value result.e
  f : E.read (%3167) = .value result.f
  g : E.read (%3168) = .value result.g
  h : E.read (%3169) = .value result.h

def fullEnv79 (E : Env program.Γ) (initial s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v3124 := (w 64).rotateRight 1
  let v3125 := (w 64).rotateRight 8
  let v3126 := v3124 ^^^ v3125
  let v3127 := (w 64) >>> 7
  let v3128 := v3126 ^^^ v3127
  let v3129 := (w 77).rotateRight 19
  let v3130 := (w 77).rotateRight 61
  let v3131 := v3129 ^^^ v3130
  let v3132 := (w 77) >>> 6
  let v3133 := v3131 ^^^ v3132
  let v3134 := s.e.rotateRight 14
  let v3135 := s.e.rotateRight 18
  let v3136 := v3134 ^^^ v3135
  let v3137 := s.e.rotateRight 41
  let v3138 := v3136 ^^^ v3137
  let v3139 := s.e &&& s.f
  let v3140 := s.e ^^^ (-1 : Word)
  let v3141 := s.g &&& v3140
  let v3142 := v3139 ||| v3141
  let v3143 := k
  let v3144 := (w 63) + v3143
  let v3145 := v3144 + v3128
  let v3146 := v3145 + (w 72)
  let v3147 := v3146 + v3133
  let v3148 := v3147 + s.h
  let v3149 := v3148 + v3142
  let v3150 := v3149 + v3138
  let v3151 := s.a.rotateRight 28
  let v3152 := s.a.rotateRight 34
  let v3153 := v3151 ^^^ v3152
  let v3154 := s.a.rotateRight 39
  let v3155 := v3153 ^^^ v3154
  let v3156 := s.b ^^^ s.c
  let v3157 := s.a &&& v3156
  let v3158 := v3157 ^^^ (s.b &&& s.c)
  let v3159 := v3158 + initial.a
  let v3160 := v3159 + v3155
  let v3161 := v3160 + v3150
  let v3162 := s.a + initial.b
  let v3163 := s.b + initial.c
  let v3164 := s.c + initial.d
  let v3165 := s.d + initial.e
  let v3166 := v3165 + v3150
  let v3167 := s.e + initial.f
  let v3168 := s.f + initial.g
  let v3169 := s.g + initial.h
  E[%3124 := .value v3124,
    %3125 := .value v3125,
    %3126 := .value v3126,
    %3127 := .value v3127,
    %3128 := .value v3128,
    %3129 := .value v3129,
    %3130 := .value v3130,
    %3131 := .value v3131,
    %3132 := .value v3132,
    %3133 := .value v3133,
    %3134 := .value v3134,
    %3135 := .value v3135,
    %3136 := .value v3136,
    %3137 := .value v3137,
    %3138 := .value v3138,
    %3139 := .value v3139,
    %3140 := .value v3140,
    %3141 := .value v3141,
    %3142 := .value v3142,
    %3143 := .value v3143,
    %3144 := .value v3144,
    %3145 := .value v3145,
    %3146 := .value v3146,
    %3147 := .value v3147,
    %3148 := .value v3148,
    %3149 := .value v3149,
    %3150 := .value v3150,
    %3151 := .value v3151,
    %3152 := .value v3152,
    %3153 := .value v3153,
    %3154 := .value v3154,
    %3155 := .value v3155,
    %3156 := .value v3156,
    %3157 := .value v3157,
    %3158 := .value v3158,
    %3159 := .value v3159,
    %3160 := .value v3160,
    %3161 := .value v3161,
    %3162 := .value v3162,
    %3163 := .value v3163,
    %3164 := .value v3164,
    %3165 := .value v3165,
    %3166 := .value v3166,
    %3167 := .value v3167,
    %3168 := .value v3168,
    %3169 := .value v3169]

def fullOut79 (initial s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v3124 := (w 64).rotateRight 1
  let v3125 := (w 64).rotateRight 8
  let v3126 := v3124 ^^^ v3125
  let v3127 := (w 64) >>> 7
  let v3128 := v3126 ^^^ v3127
  let v3129 := (w 77).rotateRight 19
  let v3130 := (w 77).rotateRight 61
  let v3131 := v3129 ^^^ v3130
  let v3132 := (w 77) >>> 6
  let v3133 := v3131 ^^^ v3132
  let v3134 := s.e.rotateRight 14
  let v3135 := s.e.rotateRight 18
  let v3136 := v3134 ^^^ v3135
  let v3137 := s.e.rotateRight 41
  let v3138 := v3136 ^^^ v3137
  let v3139 := s.e &&& s.f
  let v3140 := s.e ^^^ (-1 : Word)
  let v3141 := s.g &&& v3140
  let v3142 := v3139 ||| v3141
  let v3143 := k
  let v3144 := (w 63) + v3143
  let v3145 := v3144 + v3128
  let v3146 := v3145 + (w 72)
  let v3147 := v3146 + v3133
  let v3148 := v3147 + s.h
  let v3149 := v3148 + v3142
  let v3150 := v3149 + v3138
  let v3151 := s.a.rotateRight 28
  let v3152 := s.a.rotateRight 34
  let v3153 := v3151 ^^^ v3152
  let v3154 := s.a.rotateRight 39
  let v3155 := v3153 ^^^ v3154
  let v3156 := s.b ^^^ s.c
  let v3157 := s.a &&& v3156
  let v3158 := v3157 ^^^ (s.b &&& s.c)
  let v3159 := v3158 + initial.a
  let v3160 := v3159 + v3155
  let v3161 := v3160 + v3150
  let v3162 := s.a + initial.b
  let v3163 := s.b + initial.c
  let v3164 := s.c + initial.d
  let v3165 := s.d + initial.e
  let v3166 := v3165 + v3150
  let v3167 := s.e + initial.f
  let v3168 := s.f + initial.g
  let v3169 := s.g + initial.h
  ⟨v3161, v3162, v3163, v3164, v3166, v3167, v3168, v3169⟩

theorem fullOut79_eq (initial s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) :
    fullOut79 initial s w k = feedForward initial (Spec.round s (w 79) k) := by
  have hw79 := hw 79 (by decide) (by decide)
  dsimp only [fullOut79, Spec.round, feedForward]
  rw [hw79]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv79_frame (E : Env program.Γ) (initial s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv79 E initial s w k) := by
  unfold fullEnv79
  repeat' (apply Frame.write <;> try decide)
  exact Frame.refl E

theorem full_body79 (E : Env program.Γ) (state : GlobalState)
    (initial s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (hi : InitialReady E initial) (h : Ready79 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 632#64) 64)
    (hk : state.mem.readAt (kp.add 632#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2924 |>.take 46) state =
      .value (fullEnv79 E initial s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv79, hi.a, hi.b, hi.c, hi.d, hi.e, hi.f, hi.g, hi.h, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w63, h.w64, h.w72, h.w77, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k79, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready79 (E : Env program.Γ) (initial s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) :
    ResultReady (fullEnv79 E initial s w k) (feedForward initial (Spec.round s (w 79) k)) := by
  have hout := fullOut79_eq initial s w k hw
  constructor
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.a hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.b hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.c hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.d hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.e hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.f hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.g hout)
  · simpa [fullEnv79, fullOut79, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value (congrArg Spec.State.h hout)

theorem full_step79 (E : Env program.Γ) (state : GlobalState)
    (initial s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (hi : InitialReady E initial) (h : Ready79 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2924 |>.take 46) state =
      .value (E', state) ∧
      ResultReady E' (feedForward initial (Spec.round s (w 79) (constants.toList.getD 79 0))) ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 79 0
  have hf := fullEnv79_frame E initial s w k
  exact ⟨fullEnv79 E initial s w k,
    full_body79 E state initial s w kp k hi h hc (hk 79).1 (hk 79).2,
    full_ready79 E initial s w k hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
