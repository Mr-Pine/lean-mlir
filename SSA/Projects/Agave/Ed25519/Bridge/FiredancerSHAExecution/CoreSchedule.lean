import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreRounds
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.RingSchedule
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

/-! Exact schedule-load/update instructions in the second scalar loop. All
circular array indices and flagged additions are checked at their legal rounds. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem ring_index_add (r k : Nat) (hr : r < 80) (hk : k ≤ 14) :
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 r))
      (.value (BitVec.ofNat 64 k)) = .value (BitVec.ofNat 64 (r + k)) := by
  have hnat (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hir : (BitVec.ofNat 64 r).toInt = (r : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hnat r (by omega)]; omega), hnat r (by omega)]
  have hik : (BitVec.ofNat 64 k).toInt = (k : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hnat k (by omega)]; omega), hnat k (by omega)]
  have hs : (BitVec.ofNat 64 r).saddOverflow (BitVec.ofNat 64 k) = false := by
    simp only [BitVec.saddOverflow, hir, hik]
    norm_num
    omega
  have hu : (BitVec.ofNat 64 r).uaddOverflow (BitVec.ofNat 64 k) = false := by
    simp only [BitVec.uaddOverflow, hnat r (by omega), hnat k (by omega)]
    norm_num
    omega
  simp [Operation.add, hs, hu, ← BitVec.ofNat_add]

theorem ring_index_mask (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& 15#64 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  change n &&& (2 ^ 4 - 1) = (n % 16) % 2 ^ 64
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : n % 16 < 2 ^ 64)]

theorem ring_index_gep (n : Nat) :
    Operation.gepInboundsIndex 8 (.value (BitVec.ofNat 64 (n % 16))) =
      .value (Int.ofNat (8 * (n % 16))) := constant_index _ (by omega)

theorem fshl63_rotate (x : Word) : Operation.fshl (.value x) (.value x) (.value 63#64) =
    .value (x.rotateRight 1) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (rotateRight1_fshl x)
theorem fshl56_rotate (x : Word) : Operation.fshl (.value x) (.value x) (.value 56#64) =
    .value (x.rotateRight 8) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (rotateRight8_fshl x)
theorem fshl45_rotate (x : Word) : Operation.fshl (.value x) (.value x) (.value 45#64) =
    .value (x.rotateRight 19) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (rotateRight19_fshl x)
theorem fshl3_rotate (x : Word) : Operation.fshl (.value x) (.value x) (.value 3#64) =
    .value (x.rotateRight 61) := by
  simpa only [Operation.fshl, PoisonOr.value_bind, PoisonOr.pure_def,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using
    congrArg PoisonOr.value (rotateRight61_fshl x)

structure ScheduleReady (E : Env program.Γ) (stack : Pointer) (r : Nat) : Prop where
  index : E.read (%103) = .value (BitVec.ofNat 64 r)
  stack : E.read (%28) = .value stack
  c7 : E.read (%7) = .value 56#64
  c8 : E.read (%8) = .value 0#64
  c9 : E.read (%9) = .value 3#64
  c18 : E.read (%18) = .value 1#64
  c19 : E.read (%19) = .value 15#64
  c20 : E.read (%20) = .value 14#64
  c21 : E.read (%21) = .value 63#64
  c22 : E.read (%22) = .value 7#64
  c23 : E.read (%23) = .value 45#64
  c24 : E.read (%24) = .value 6#64
  c25 : E.read (%25) = .value 9#64

def scheduleMemory (m : MemoryState) (stack : Pointer) (q : Ring) (r : Nat) : MemoryState :=
  m.storeAt (stack.add (BitVec.ofNat 64 (8 * (r % 16)))) (ringWord q r)

def scheduleEnv (E : Env program.Γ) (stack : Pointer) (q : Ring) (r : Nat) : Env program.Γ :=
  let v106 := BitVec.ofNat 64 (r + 1)
  let v107 := BitVec.ofNat 64 ((r + 1) % 16)
  let v108 := stack.add (BitVec.ofNat 64 (8 * ((r + 1) % 16)))
  let v109 := q ((r + 1) % 16)
  let v110 := BitVec.ofNat 64 (r + 14)
  let v111 := BitVec.ofNat 64 ((r + 14) % 16)
  let v112 := stack.add (BitVec.ofNat 64 (8 * ((r + 14) % 16)))
  let v113 := q ((r + 14) % 16)
  let v114 := v109.rotateRight 1
  let v115 := v109.rotateRight 8
  let v116 := v114 ^^^ v115
  let v117 := v109 >>> 7
  let v118 := v116 ^^^ v117
  let v119 := v113.rotateRight 19
  let v120 := v113.rotateRight 61
  let v121 := v119 ^^^ v120
  let v122 := v113 >>> 6
  let v123 := v121 ^^^ v122
  let v124 := BitVec.ofNat 64 (r + 9)
  let v125 := BitVec.ofNat 64 ((r + 9) % 16)
  let v126 := stack.add (BitVec.ofNat 64 (8 * ((r + 9) % 16)))
  let v127 := q ((r + 9) % 16)
  let v128 := BitVec.ofNat 64 (r % 16)
  let v129 := stack.add (BitVec.ofNat 64 (8 * (r % 16)))
  let v130 := q (r % 16)
  let v131 := v118 + v127
  let v132 := v131 + v130
  let v133 := v132 + v123
  E[%106 := .value v106,
    %107 := .value v107,
    %108 := .value v108,
    %109 := .value v109,
    %110 := .value v110,
    %111 := .value v111,
    %112 := .value v112,
    %113 := .value v113,
    %114 := .value v114,
    %115 := .value v115,
    %116 := .value v116,
    %117 := .value v117,
    %118 := .value v118,
    %119 := .value v119,
    %120 := .value v120,
    %121 := .value v121,
    %122 := .value v122,
    %123 := .value v123,
    %124 := .value v124,
    %125 := .value v125,
    %126 := .value v126,
    %127 := .value v127,
    %128 := .value v128,
    %129 := .value v129,
    %130 := .value v130,
    %131 := .value v131,
    %132 := .value v132,
    %133 := .value v133]

theorem schedule_body (E : Env program.Γ) (state : GlobalState) (stack : Pointer)
    (q : Ring) (r : Nat) (h : ScheduleReady E stack r) (hr : r < 80)
    (hs : SmallRange state.mem stack 128)
    (hread : ∀ j, j < 16 → state.mem.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = q j) :
    List.foldlM Instr.run E (program.bb3.body.take 29) state =
      .value (scheduleEnv E stack q r, {state with mem := scheduleMemory state.mem stack q r}) := by
  have hadd1 := ring_index_add r 1 hr (by decide)
  have hadd9 := ring_index_add r 9 hr (by decide)
  have hadd14 := ring_index_add r 14 hr (by decide)
  have hzero : Operation.gepInboundsIndex 128 (.value 0#64) = .value 0 := by decide
  have hm0 := ring_index_mask r (by omega)
  have hi0 := ring_index_gep r
  have hg0 := gep_zero_index hs (k := 8 * (r % 16)) (by omega)
  have hf0 := hs.fits_add (k := 8 * (r % 16)) (count := 8) (by omega)
  have hv0 := hread (r % 16) (by omega)
  have hm1 := ring_index_mask (r + 1) (by omega)
  have hi1 := ring_index_gep (r + 1)
  have hg1 := gep_zero_index hs (k := 8 * ((r + 1) % 16)) (by omega)
  have hf1 := hs.fits_add (k := 8 * ((r + 1) % 16)) (count := 8) (by omega)
  have hv1 := hread ((r + 1) % 16) (by omega)
  have hm9 := ring_index_mask (r + 9) (by omega)
  have hi9 := ring_index_gep (r + 9)
  have hg9 := gep_zero_index hs (k := 8 * ((r + 9) % 16)) (by omega)
  have hf9 := hs.fits_add (k := 8 * ((r + 9) % 16)) (count := 8) (by omega)
  have hv9 := hread ((r + 9) % 16) (by omega)
  have hm14 := ring_index_mask (r + 14) (by omega)
  have hi14 := ring_index_gep (r + 14)
  have hg14 := gep_zero_index hs (k := 8 * ((r + 14) % 16)) (by omega)
  have hf14 := hs.fits_add (k := 8 * ((r + 14) % 16)) (count := 8) (by omega)
  have hv14 := hread ((r + 14) % 16) (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Int.natCast_emod] at hg0 hg1 hg9 hg14
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run,
    scheduleEnv, scheduleMemory, ringWord, scheduleWord, smallSigma0, smallSigma1,
    h.index, h.stack, h.c7, h.c8, h.c9, h.c18, h.c19, h.c20, h.c21, h.c22, h.c23, h.c24, h.c25,
    hadd1, hadd9, hadd14, hzero,
    hm0, hi0, hg0, hf0, hv0, hm1, hi1, hg1, hf1, hv1, hm9, hi9, hg9, hf9, hv9, hm14, hi14, hg14, hf14, hv14,
    Operation.and, Operation.xor, Operation.lshr, Operation.load, Operation.store, hadd,
    fshl63_rotate, fshl56_rotate, fshl45_rotate, fshl3_rotate, GepIndex.inboundsOffset,
    BinOp.compute, TernOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    mlir_env, mlir_effect, throwUBIf]

/-- The one store updates precisely the ring slot selected by the C mask. -/
theorem scheduleMemory_read (m : MemoryState) (stack : Pointer) (q : Ring) (r j : Nat)
    (hs : SmallRange m stack 128) (hj : j < 16)
    (hread : m.readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 = q j) :
    (scheduleMemory m stack q r).readAt (stack.add (BitVec.ofNat 64 (8 * j))) 64 =
      ringStep q r j := by
  by_cases heq : j = r % 16
  · subst j
    simpa only [scheduleMemory, ringStep, ite_true] using
      MemoryState.readAt_storeAt_self
        (hs.fits_add (k := 8 * (r % 16)) (count := 8) (by omega)) (ringWord q r)
  · have hdis := smallRange_disjoint_offsets hs (i := 8 * (r % 16)) (countI := 8)
      (j := 8 * j) (countJ := 8) (by omega) (by omega) (by omega)
    simp only [scheduleMemory, ringStep, ite_eq_right heq,
      MemoryState.readAt_storeAt_disjoint hdis, hread]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Core
