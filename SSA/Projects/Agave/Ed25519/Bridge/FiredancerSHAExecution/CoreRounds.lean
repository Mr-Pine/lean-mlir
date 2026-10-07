import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Program
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Memory

/-! Exact arithmetic slices of both imported scalar core loops, including their
inbounds K-table address and load. Their output registers implement Spec.round.
Schedule loads/stores and loop composition are separate obligations. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The C array GEP has a zero array index followed by an element offset. -/
theorem gep_zero_index {m : MemoryState} {p : Pointer} {bytes k : Nat} (h : SmallRange m p bytes) (hk : k ≤ bytes) :
    Operation.gepInboundsLive m (.value p) [.value 0, .value (k : Int)] =
      .value (p.add (BitVec.ofNat 64 k)) := by
  obtain ⟨b, hb, hsmall, hsz⟩ := h
  have hwithin : Operation.GepInboundsOffsets b.length p.offset.toNat [0, (k : Int)] := by
    simp [Operation.GepInboundsOffsets, Operation.GepSignedRange,
      List.scanl_cons, List.scanl_nil]
    omega
  simpa using Operation.gepInboundsLive_eq (offsets := [0, (k : Int)]) hb hsmall hwithin

theorem constant_index (r : Nat) (hr : r < 80) :
    Operation.gepInboundsIndex 8 (.value (BitVec.ofNat 64 r)) =
      .value (Int.ofNat (8 * r)) := by
  interval_cases r <;> decide

structure Constants (E : Env program.Γ) (kp : Pointer) : Prop where
  zero : E.read (%8) = .value 0#64
  rot14 : E.read (%10) = .value 50#64
  rot18 : E.read (%11) = .value 46#64
  rot41 : E.read (%12) = .value 23#64
  notMask : E.read (%13) = .value (-1 : Word)
  kp : E.read (%14) = .value kp
  rot28 : E.read (%15) = .value 36#64
  rot34 : E.read (%16) = .value 30#64
  rot39 : E.read (%17) = .value 25#64

structure FirstReady (E : Env program.Γ) (s : State) (word : Word) (r : Nat) : Prop where
  a : E.read (%54) = .value s.a
  b : E.read (%55) = .value s.b
  c : E.read (%56) = .value s.c
  d : E.read (%57) = .value s.d
  e : E.read (%58) = .value s.e
  f : E.read (%59) = .value s.f
  g : E.read (%62) = .value s.g
  h : E.read (%61) = .value s.h
  word : E.read (%66) = .value word
  index : E.read (%60) = .value (BitVec.ofNat 64 r)

def firstEnv (E : Env program.Γ) (s : State) (word constant : Word)
    (kp : Pointer) (r : Nat) : Env program.Γ :=
  let v0 := s.e.rotateRight 14
  let v1 := s.e.rotateRight 18
  let v2 := v0 ^^^ v1
  let v3 := s.e.rotateRight 41
  let v4 := v2 ^^^ v3
  let v5 := s.e &&& s.f
  let v6 := s.e ^^^ (-1 : Word)
  let v7 := s.g &&& v6
  let v8 := v5 ||| v7
  let v9 := kp.add (BitVec.ofNat 64 (8 * r))
  let v10 := constant
  let v11 := v8 + s.h
  let v12 := v11 + v4
  let v13 := v12 + word
  let v14 := v13 + v10
  let v15 := s.a.rotateRight 28
  let v16 := s.a.rotateRight 34
  let v17 := v15 ^^^ v16
  let v18 := s.a.rotateRight 39
  let v19 := v17 ^^^ v18
  let v20 := s.b ^^^ s.c
  let v21 := s.a &&& v20
  let v22 := s.b &&& s.c
  let v23 := v21 ^^^ v22
  let v24 := v19 + v23
  let v25 := v14 + s.d
  let v26 := v24 + v14
  E[%68 := .value v0,
    %69 := .value v1,
    %70 := .value v2,
    %71 := .value v3,
    %72 := .value v4,
    %73 := .value v5,
    %74 := .value v6,
    %75 := .value v7,
    %76 := .value v8,
    %77 := .value v9,
    %78 := .value v10,
    %79 := .value v11,
    %80 := .value v12,
    %81 := .value v13,
    %82 := .value v14,
    %83 := .value v15,
    %84 := .value v16,
    %85 := .value v17,
    %86 := .value v18,
    %87 := .value v19,
    %88 := .value v20,
    %89 := .value v21,
    %90 := .value v22,
    %91 := .value v23,
    %92 := .value v24,
    %93 := .value v25,
    %94 := .value v26]

theorem first_body (E : Env program.Γ) (state : GlobalState)
    (s : State) (word constant : Word) (kp : Pointer) (r : Nat)
    (h : FirstReady E s word r) (hc : Constants E kp)
    (hr : r < 80) (hk : SmallRange state.mem kp 640)
    (hread : state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant) :
    List.foldlM Instr.run E (program.bb2.body.drop 6 |>.take 27) state =
      .value (firstEnv E s word constant kp r, state) := by
  have hidx := constant_index r hr
  have hzero : Operation.gepInboundsIndex 640 (.value 0#64) = .value 0 := by decide
  have hgep := gep_zero_index hk (k := 8 * r) (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hfit := hk.fits_add (k := 8 * r) (count := 8) (by omega)
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    firstEnv, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.word, h.index,
    hc.zero, hc.rot14, hc.rot18, hc.rot41, hc.notMask, hc.kp,
    hc.rot28, hc.rot34, hc.rot39, hidx, hzero, hgep, hfit, hread,
    Operation.load, Operation.and, Operation.xor, Operation.or, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    GepIndex.inboundsOffset, BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem first_result (E : Env program.Γ) (s : State) (word constant : Word)
    (kp : Pointer) (r : Nat) :
    (firstEnv E s word constant kp r).read (%94) =
      .value (Spec.round s word constant).a ∧
    (firstEnv E s word constant kp r).read (%93) =
      .value (Spec.round s word constant).e := by
  rw [← firstRound_eq]
  simp [firstEnv, firstRound, bigSigma0, bigSigma1, mlir_env]

structure LaterReady (E : Env program.Γ) (s : State) (word : Word) (r : Nat) : Prop where
  a : E.read (%97) = .value s.a
  b : E.read (%98) = .value s.b
  c : E.read (%99) = .value s.c
  d : E.read (%100) = .value s.d
  e : E.read (%101) = .value s.e
  f : E.read (%102) = .value s.f
  g : E.read (%105) = .value s.g
  h : E.read (%104) = .value s.h
  word : E.read (%133) = .value word
  index : E.read (%103) = .value (BitVec.ofNat 64 r)

def laterEnv (E : Env program.Γ) (s : State) (word constant : Word)
    (kp : Pointer) (r : Nat) : Env program.Γ :=
  let v0 := s.e.rotateRight 14
  let v1 := s.e.rotateRight 18
  let v2 := v0 ^^^ v1
  let v3 := s.e.rotateRight 41
  let v4 := v2 ^^^ v3
  let v5 := s.e &&& s.f
  let v6 := s.e ^^^ (-1 : Word)
  let v7 := s.g &&& v6
  let v8 := v5 ||| v7
  let v9 := kp.add (BitVec.ofNat 64 (8 * r))
  let v10 := constant
  let v11 := v8 + s.h
  let v12 := v11 + v4
  let v13 := v12 + v10
  let v14 := v13 + word
  let v15 := s.a.rotateRight 28
  let v16 := s.a.rotateRight 34
  let v17 := v15 ^^^ v16
  let v18 := s.a.rotateRight 39
  let v19 := v17 ^^^ v18
  let v20 := s.b ^^^ s.c
  let v21 := s.a &&& v20
  let v22 := s.b &&& s.c
  let v23 := v21 ^^^ v22
  let v24 := v19 + v23
  let v25 := v14 + s.d
  let v26 := v24 + v14
  E[%134 := .value v0,
    %135 := .value v1,
    %136 := .value v2,
    %137 := .value v3,
    %138 := .value v4,
    %139 := .value v5,
    %140 := .value v6,
    %141 := .value v7,
    %142 := .value v8,
    %143 := .value v9,
    %144 := .value v10,
    %145 := .value v11,
    %146 := .value v12,
    %147 := .value v13,
    %148 := .value v14,
    %149 := .value v15,
    %150 := .value v16,
    %151 := .value v17,
    %152 := .value v18,
    %153 := .value v19,
    %154 := .value v20,
    %155 := .value v21,
    %156 := .value v22,
    %157 := .value v23,
    %158 := .value v24,
    %159 := .value v25,
    %160 := .value v26]

theorem later_body (E : Env program.Γ) (state : GlobalState)
    (s : State) (word constant : Word) (kp : Pointer) (r : Nat)
    (h : LaterReady E s word r) (hc : Constants E kp)
    (hr : r < 80) (hk : SmallRange state.mem kp 640)
    (hread : state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant) :
    List.foldlM Instr.run E (program.bb3.body.drop 29 |>.take 27) state =
      .value (laterEnv E s word constant kp r, state) := by
  have hidx := constant_index r hr
  have hzero : Operation.gepInboundsIndex 640 (.value 0#64) = .value 0 := by decide
  have hgep := gep_zero_index hk (k := 8 * r) (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hgep
  have hfit := hk.fits_add (k := 8 * r) (count := 8) (by omega)
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run,
    laterEnv, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.word, h.index,
    hc.zero, hc.rot14, hc.rot18, hc.rot41, hc.notMask, hc.kp,
    hc.rot28, hc.rot34, hc.rot39, hidx, hzero, hgep, hfit, hread,
    Operation.load, Operation.and, Operation.xor, Operation.or, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    GepIndex.inboundsOffset, BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem later_result (E : Env program.Γ) (s : State) (word constant : Word)
    (kp : Pointer) (r : Nat) :
    (laterEnv E s word constant kp r).read (%160) =
      .value (Spec.round s word constant).a ∧
    (laterEnv E s word constant kp r).read (%159) =
      .value (Spec.round s word constant).e := by
  rw [← laterRound_eq]
  simp [laterEnv, laterRound, bigSigma0, bigSigma1, mlir_env]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
