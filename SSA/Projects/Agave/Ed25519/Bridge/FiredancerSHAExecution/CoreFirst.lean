import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreSchedule
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail

/-! Complete first-loop body, including native input load, bswap, private
schedule store, K load, round arithmetic, and loop-index comparison. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.SHA512Finalization (swapBytes)
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem first_shift (r : Nat) (hr : r < 16) :
    Operation.shl {nsw := true, nuw := true} (.value (BitVec.ofNat 64 r)) (.value 3#64) =
      .value (BitVec.ofNat 64 (8 * r)) := by
  interval_cases r <;> decide

theorem first_data_index (r : Nat) (hr : r < 16) :
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 (8 * r))) =
      .value (Int.ofNat (8 * r)) := by
  interval_cases r <;> decide

structure InputReady (E : Env program.Γ) (stack data : Pointer) (r : Nat) : Prop where
  stack : E.read (%28) = .value stack
  data : E.read (%52) = .value data
  index : E.read (%60) = .value (BitVec.ofNat 64 r)
  zero : E.read (%8) = .value 0#64
  shift : E.read (%9) = .value 3#64

def inputMemory (m : MemoryState) (stack : Pointer) (r : Nat) (native : Word) : MemoryState :=
  m.storeAt (stack.add (BitVec.ofNat 64 (8 * r))) (swapBytes native)

def inputEnv (E : Env program.Γ) (stack data : Pointer) (r : Nat) (native : Word) : Env program.Γ :=
  E[%63 := .value (BitVec.ofNat 64 (8 * r)),
    %64 := .value (data.add (BitVec.ofNat 64 (8 * r))), %65 := .value native,
    %66 := .value (swapBytes native), %67 := .value (stack.add (BitVec.ofNat 64 (8 * r)))]

theorem input_body (E : Env program.Γ) (state : GlobalState) (stack data : Pointer)
    (r : Nat) (native : Word) (h : InputReady E stack data r) (hr : r < 16)
    (hs : SmallRange state.mem stack 128) (hd : SmallRange state.mem data 128)
    (hread : state.mem.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64 = native) :
    List.foldlM Instr.run E (program.bb2.body.take 6) state =
      .value (inputEnv E stack data r native,
        {state with mem := inputMemory state.mem stack r native}) := by
  have hshift := first_shift r hr
  have hdi := first_data_index r hr
  have hsi := constant_index r (by omega)
  have hzero : Operation.gepInboundsIndex 128 (.value 0#64) = .value 0 := by decide
  have hsg := gep_zero_index hs (k := 8 * r) (by omega)
  have hdg := hd.gep (k := 8 * r) (by omega)
  have hsf := hs.fits_add (k := 8 * r) (count := 8) (by omega)
  have hdf := hd.fits_add (k := 8 * r) (count := 8) (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hsg hdg
  have hswap : Operation.bswap (.value native) = .value (swapBytes native) := rfl
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run,
    inputEnv, inputMemory, h.stack, h.data, h.index, h.zero, h.shift,
    hshift, hdi, hsi, hzero, hsg, hdg, hsf, hdf, hread, hswap,
    Operation.load, Operation.store, GepIndex.inboundsOffset, UnOp.compute,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

structure FirstStateReady (E : Env program.Γ) (s : State) : Prop where
  a : E.read (%54) = .value s.a
  b : E.read (%55) = .value s.b
  c : E.read (%56) = .value s.c
  d : E.read (%57) = .value s.d
  e : E.read (%58) = .value s.e
  f : E.read (%59) = .value s.f
  g : E.read (%62) = .value s.g
  h : E.read (%61) = .value s.h

theorem input_ready_round (E : Env program.Γ) (stack data : Pointer) (r : Nat)
    (native : Word) (s : State) (h : FirstStateReady E s)
    (hr : E.read (%60) = .value (BitVec.ofNat 64 r)) :
    FirstReady (inputEnv E stack data r native) s (swapBytes native) r := by
  constructor
  · simpa [inputEnv, mlir_env] using h.a
  · simpa [inputEnv, mlir_env] using h.b
  · simpa [inputEnv, mlir_env] using h.c
  · simpa [inputEnv, mlir_env] using h.d
  · simpa [inputEnv, mlir_env] using h.e
  · simpa [inputEnv, mlir_env] using h.f
  · simpa [inputEnv, mlir_env] using h.g
  · simpa [inputEnv, mlir_env] using h.h
  · simp [inputEnv, mlir_env]
  · simpa [inputEnv, mlir_env] using hr

theorem input_constants (E : Env program.Γ) (stack data kp : Pointer) (r : Nat)
    (native : Word) (h : Constants E kp) : Constants (inputEnv E stack data r native) kp := by
  constructor
  · simpa [inputEnv, mlir_env] using h.zero
  · simpa [inputEnv, mlir_env] using h.rot14
  · simpa [inputEnv, mlir_env] using h.rot18
  · simpa [inputEnv, mlir_env] using h.rot41
  · simpa [inputEnv, mlir_env] using h.notMask
  · simpa [inputEnv, mlir_env] using h.kp
  · simpa [inputEnv, mlir_env] using h.rot28
  · simpa [inputEnv, mlir_env] using h.rot34
  · simpa [inputEnv, mlir_env] using h.rot39

def firstBodyEnv (E : Env program.Γ) (stack data kp : Pointer) (r : Nat)
    (s : State) (native constant : Word) : Env program.Γ :=
  (firstEnv (inputEnv E stack data r native) s (swapBytes native) constant kp r)[
    %95 := .value (BitVec.ofNat 64 (r + 1)),
    %96 := .value (BitVec.ofBool (BitVec.ofNat 64 (r + 1) == 16#64))]

theorem first_body_full (E : Env program.Γ) (state : GlobalState) (stack data kp : Pointer)
    (r : Nat) (s : State) (native constant : Word)
    (hstate : FirstStateReady E s) (hin : InputReady E stack data r) (hc : Constants E kp)
    (h16 : E.read (%2) = .value 16#64) (h1 : E.read (%18) = .value 1#64) (hr : r < 16)
    (hs : SmallRange state.mem stack 128) (hd : SmallRange state.mem data 128)
    (hk : SmallRange state.mem kp 640) (hne : stack.id ≠ kp.id)
    (hread : state.mem.readAt (data.add (BitVec.ofNat 64 (8 * r))) 64 = native)
    (hkread : state.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant) :
    List.foldlM Instr.run E program.bb2.body state =
      .value (firstBodyEnv E stack data kp r s native constant,
        {state with mem := inputMemory state.mem stack r native}) := by
  let EI := inputEnv E stack data r native
  let SI : GlobalState := {state with mem := inputMemory state.mem stack r native}
  have hfirst := input_body E state stack data r native hin hr hs hd hread
  have hready : FirstReady EI s (swapBytes native) r :=
    input_ready_round E stack data r native s hstate hin.index
  have hconst : Constants EI kp := input_constants E stack data kp r native hc
  have hks : SmallRange SI.mem kp 640 := hk.storeAt _ _
  have hkread' : SI.mem.readAt (kp.add (BitVec.ofNat 64 (8 * r))) 64 = constant := by
    dsimp only [SI, inputMemory]
    have hdis : (Range.of (stack.add (BitVec.ofNat 64 (8 * r))) 64).Disjoint
        (Range.of (kp.add (BitVec.ofNat 64 (8 * r))) 64) := Or.inl hne
    rw [MemoryState.readAt_storeAt_disjoint hdis]
    exact hkread
  have hround := first_body EI SI s (swapBytes native) constant kp r hready hconst (by omega) hks hkread'
  have hnext := ring_index_add r 1 (by omega) (by decide)
  have hsplit : program.bb2.body = program.bb2.body.take 6 ++
      ((program.bb2.body.drop 6).take 27 ++ program.bb2.body.drop 33) := by rfl
  rw [hsplit, List.foldlM_append]
  change (List.foldlM Instr.run E (program.bb2.body.take 6) state >>= _) = _
  rw [hfirst]
  change List.foldlM Instr.run EI
    ((program.bb2.body.drop 6).take 27 ++ program.bb2.body.drop 33) SI = _
  rw [List.foldlM_append]
  change (List.foldlM Instr.run EI ((program.bb2.body.drop 6).take 27) SI >>= _) = _
  rw [hround]
  simp [program.bb2, List.foldlM_cons, List.foldlM_nil, Instr.run, firstBodyEnv,
    firstEnv, inputEnv, EI, SI, hin.index, h1, h16, hnext, Operation.icmp, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem first_exit_test (r : Nat) (hr : r < 16) :
    (BitVec.ofNat 64 (r + 1) == 16#64) = decide (r + 1 = 16) := by
  interval_cases r <;> decide

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
