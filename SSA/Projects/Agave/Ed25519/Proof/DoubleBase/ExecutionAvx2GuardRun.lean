import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Dispatch
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Guards

/-! Exact continuations through all four digit guards. B's load, signed
dispatch and bounds check are composed below. No panic-callee property is
assumed: the source NAF magnitude excludes those edges. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

theorem negative5_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) (s : GlobalState) :
    (avx2Kernel p g).runFrom (negative5Input E m) 20 s =
      (avx2Kernel p g).runFrom (negative5Result E m) 22 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 20 = avx2Kernel.bb20 from rfl,
    negative5_block]
  rfl

theorem positive5_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) (s : GlobalState) :
    (avx2Kernel p g).runFrom (positive5Input E m) 23 s =
      (avx2Kernel p g).runFrom (positive5Result E m) 25 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 23 = avx2Kernel.bb23 from rfl,
    positive5_block]
  rfl

theorem negative8_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) (s : GlobalState) :
    (avx2Kernel p g).runFrom (negative8Input E m) 27 s =
      (avx2Kernel p g).runFrom (negative8Result E m) 29 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 27 = avx2Kernel.bb27 from rfl,
    negative8_block]
  rfl

theorem positive8_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) (s : GlobalState) :
    (avx2Kernel p g).runFrom (positive8Input E m) 31 s =
      (avx2Kernel p g).runFrom (positive8Result E m) 33 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 31 = avx2Kernel.bb31 from rfl,
    positive8_block]
  rfl

theorem dispatchB_negative_ready (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer)
    (pos : Fin 256) (n : Nat)
    (hone : E.read (%10) = .value 1#64)
    (hminus : E.read (%222) = .value (-1 : BitVec 8))
    (hnegative : nafDigits 8 n pos.val < 0) :
    negative8Input (dispatchBResult E digits pos (Execution.nafByte 8 n pos.val))
      (nafMagnitude8 n pos.val) =
        dispatchBResult E digits pos (Execution.nafByte 8 n pos.val) := by
  unfold negative8Input
  repeat' (first | rfl | apply Env.write_eq_of)
  all_goals simp [dispatchBResult, dispatchBInput, mlir_env, hone, hminus,
    (naf8_magnitude_cases n pos.val).2 (le_of_lt hnegative)]

theorem dispatchB_positive_ready (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer)
    (pos : Fin 256) (n : Nat)
    (hone : E.read (%10) = .value 1#64)
    (hminus : E.read (%222) = .value (-1 : BitVec 8))
    (hpositive : 0 ≤ nafDigits 8 n pos.val) :
    positive8Input (dispatchBResult E digits pos (Execution.nafByte 8 n pos.val))
      (nafMagnitude8 n pos.val) =
        dispatchBResult E digits pos (Execution.nafByte 8 n pos.val) := by
  unfold positive8Input
  repeat' (first | rfl | apply Env.write_eq_of)
  all_goals simp [dispatchBResult, dispatchBInput, mlir_env, hone, hminus,
    (naf8_magnitude_cases n pos.val).1 hpositive]

/-- The exact B-digit read and both signed index guards, finishing at the
appropriate add/sub arithmetic block or at the original zero backedge. -/
theorem dispatchB_naf_guard_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256) (n : Nat)
    (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 =
      Execution.nafByte 8 n pos.val)
    (hone : E.read (%10) = .value 1#64)
    (hminus : E.read (%222) = .value (-1 : BitVec 8)) :
    (avx2Kernel p g).runFrom (dispatchBInput E digits pos) 26 s =
      if nafDigits 8 n pos.val < 0 then
        (avx2Kernel p g).runFrom
          (negative8Result (dispatchBResult E digits pos (Execution.nafByte 8 n pos.val))
            (nafMagnitude8 n pos.val)) 29 s
      else if Execution.nafByte 8 n pos.val = 0#8 then
        (avx2Kernel p g).runFrom
          (dispatchBZero E digits pos (Execution.nafByte 8 n pos.val)) 30 s
      else
        (avx2Kernel p g).runFrom
          (positive8Result (dispatchBResult E digits pos (Execution.nafByte 8 n pos.val))
            (nafMagnitude8 n pos.val)) 33 s := by
  rw [dispatchB_run p g E digits pos _ s hbuffer hread,
    Execution.nafByte_toInt 8 (Or.inr rfl)]
  by_cases hneg : nafDigits 8 n pos.val < 0
  · rw [if_pos hneg, if_pos hneg]
    conv_lhs => rw [← dispatchB_negative_ready E digits pos n hone hminus hneg]
    exact negative8_run p g _ _ s
  · rw [if_neg hneg, if_neg hneg]
    by_cases hzero : Execution.nafByte 8 n pos.val = 0#8
    · rw [if_pos hzero, if_pos hzero]
    · rw [if_neg hzero, if_neg hzero]
      conv_lhs => rw [← dispatchB_positive_ready E digits pos n hone hminus (by omega)]
      exact positive8_run p g _ _ s

end Agave.Ed25519.DoubleBase.ExecutionAvx2
