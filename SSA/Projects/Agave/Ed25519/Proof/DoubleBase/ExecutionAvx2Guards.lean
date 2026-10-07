import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Control
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Execution

/-! The four signed-digit index/guard blocks of the actual imported kernel.
The bounds here concern magnitudes; the NAF construction supplies them. The
conclusions identify a safe arithmetic successor and exclude the panic block,
without requiring any behavior from the panic primitive. -/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR RIR

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The NAF construction, rather than a caller-supplied index premise,
provides the exact magnitude range used by the width-five guard. -/
def nafMagnitude5 (n i : Nat) : Fin 16 :=
  ⟨(nafDigits 5 n i).natAbs, by
    have h := NAF.digits_bounds 5 (Or.inl rfl) 256 0 ⟨n, 0⟩ (by norm_num) i
    change -(2 ^ (5 - 1) : Int) < nafDigits 5 n i ∧
      nafDigits 5 n i < (2 ^ (5 - 1) : Int) ∧ _ at h
    norm_num at h
    rcases le_total 0 (nafDigits 5 n i) with hp | hn
    · have hab := Int.natAbs_of_nonneg hp
      omega
    · have hab := Int.ofNat_natAbs_of_nonpos hn
      omega⟩

def nafMagnitude8 (n i : Nat) : Fin 128 :=
  ⟨(nafDigits 8 n i).natAbs, by
    have h := NAF.digits_bounds 8 (Or.inr rfl) 256 0 ⟨n, 0⟩ (by norm_num) i
    change -(2 ^ (8 - 1) : Int) < nafDigits 8 n i ∧
      nafDigits 8 n i < (2 ^ (8 - 1) : Int) ∧ _ at h
    norm_num at h
    rcases le_total 0 (nafDigits 8 n i) with hp | hn
    · have hab := Int.natAbs_of_nonneg hp
      omega
    · have hab := Int.ofNat_natAbs_of_nonpos hn
      omega⟩

theorem byte_magnitude_cases : ∀ digit : BitVec 8,
    (0 ≤ digit.toInt → digit = BitVec.ofNat 8 digit.toInt.natAbs) ∧
    (digit.toInt ≤ 0 → digit = -BitVec.ofNat 8 digit.toInt.natAbs) := by
  decide +kernel

theorem naf5_magnitude_cases (n i : Nat) :
    (0 ≤ nafDigits 5 n i →
      Execution.nafByte 5 n i = BitVec.ofNat 8 (nafMagnitude5 n i).val) ∧
    (nafDigits 5 n i ≤ 0 →
      Execution.nafByte 5 n i = -BitVec.ofNat 8 (nafMagnitude5 n i).val) := by
  simpa only [Execution.nafByte_toInt 5 (Or.inl rfl), nafMagnitude5] using
    byte_magnitude_cases (Execution.nafByte 5 n i)

theorem naf8_magnitude_cases (n i : Nat) :
    (0 ≤ nafDigits 8 n i →
      Execution.nafByte 8 n i = BitVec.ofNat 8 (nafMagnitude8 n i).val) ∧
    (nafDigits 8 n i ≤ 0 →
      Execution.nafByte 8 n i = -BitVec.ofNat 8 (nafMagnitude8 n i).val) := by
  simpa only [Execution.nafByte_toInt 8 (Or.inr rfl), nafMagnitude8] using
    byte_magnitude_cases (Execution.nafByte 8 n i)

theorem index5_arithmetic : ∀ m : Fin 16,
    Operation.sub {} (.value 0#8) (.value (-BitVec.ofNat 8 m.val)) =
      .value (BitVec.ofNat 8 m.val) ∧
    Operation.sext (.value (BitVec.ofNat 8 m.val)) = .value (BitVec.ofNat 64 m.val) ∧
    Operation.lshr false (.value (BitVec.ofNat 64 m.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (m.val / 2)) ∧
    Operation.icmp .ult (.value (BitVec.ofNat 8 m.val)) (.value 16#8) = .value 1#1 := by
  decide +kernel

theorem index8_arithmetic : ∀ m : Fin 128,
    Operation.sub {} (.value 0#8) (.value (-BitVec.ofNat 8 m.val)) =
      .value (BitVec.ofNat 8 m.val) ∧
    Operation.sext (.value (BitVec.ofNat 8 m.val)) = .value (BitVec.ofNat 64 m.val) ∧
    Operation.lshr false (.value (BitVec.ofNat 64 m.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (m.val / 2)) ∧
    Operation.icmp .sgt (.value (BitVec.ofNat 8 m.val)) (.value 255#8) = .value 1#1 := by
  decide +kernel

def negative5Input (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) : ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %10 := .value 1#64, %117 := .value 16#8,
    %523 := .value (-BitVec.ofNat 8 m.val)]

def negative5Result (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) : ⟪avx2Kernel.Γ⟫ :=
  (negative5Input E m)[%525 := .value (BitVec.ofNat 8 m.val),
    %526 := .value (BitVec.ofNat 64 m.val),
    %527 := .value (BitVec.ofNat 64 (m.val / 2)), %528 := .value 1#1]

theorem negative5_block (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) (s : GlobalState) :
    avx2Kernel.bb20.run avx2Kernel.blockParams (negative5Input E m) s =
      .value ((negative5Result E m, .inr 22), s) := by
  obtain ⟨hneg, hsext, hshr, hguard⟩ := index5_arithmetic m
  simp [BasicBlock.run, avx2Kernel.bb20,
    negative5Input, negative5Result, List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hneg, hsext, hshr, hguard,
    Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def positive5Input (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) : ⟪avx2Kernel.Γ⟫ :=
  E[%10 := .value 1#64, %117 := .value 16#8, %523 := .value (BitVec.ofNat 8 m.val)]

def positive5Result (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) : ⟪avx2Kernel.Γ⟫ :=
  (positive5Input E m)[%624 := .value (BitVec.ofNat 64 m.val),
    %625 := .value (BitVec.ofNat 64 (m.val / 2)), %626 := .value 1#1]

theorem positive5_block (E : ⟪avx2Kernel.Γ⟫) (m : Fin 16) (s : GlobalState) :
    avx2Kernel.bb23.run avx2Kernel.blockParams (positive5Input E m) s =
      .value ((positive5Result E m, .inr 25), s) := by
  obtain ⟨_, hsext, hshr, hguard⟩ := index5_arithmetic m
  simp [BasicBlock.run, avx2Kernel.bb23,
    positive5Input, positive5Result, List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hsext, hshr, hguard,
    Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def negative8Input (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) : ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %10 := .value 1#64, %222 := .value (-1 : BitVec 8),
    %704 := .value (-BitVec.ofNat 8 m.val)]

def negative8Result (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) : ⟪avx2Kernel.Γ⟫ :=
  (negative8Input E m)[%706 := .value (BitVec.ofNat 8 m.val),
    %707 := .value (BitVec.ofNat 64 m.val),
    %708 := .value (BitVec.ofNat 64 (m.val / 2)), %709 := .value 1#1]

theorem negative8_block (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) (s : GlobalState) :
    avx2Kernel.bb27.run avx2Kernel.blockParams (negative8Input E m) s =
      .value ((negative8Result E m, .inr 29), s) := by
  obtain ⟨hneg, hsext, hshr, hguard⟩ := index8_arithmetic m
  simp [BasicBlock.run, avx2Kernel.bb27,
    negative8Input, negative8Result, List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hneg, hsext, hshr, hguard,
    Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def positive8Input (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) : ⟪avx2Kernel.Γ⟫ :=
  E[%10 := .value 1#64, %222 := .value (-1 : BitVec 8),
    %704 := .value (BitVec.ofNat 8 m.val)]

def positive8Result (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) : ⟪avx2Kernel.Γ⟫ :=
  (positive8Input E m)[%812 := .value (BitVec.ofNat 64 m.val),
    %813 := .value (BitVec.ofNat 64 (m.val / 2)), %814 := .value 1#1]

theorem positive8_block (E : ⟪avx2Kernel.Γ⟫) (m : Fin 128) (s : GlobalState) :
    avx2Kernel.bb31.run avx2Kernel.blockParams (positive8Input E m) s =
      .value ((positive8Result E m, .inr 33), s) := by
  obtain ⟨_, hsext, hshr, hguard⟩ := index8_arithmetic m
  simp [BasicBlock.run, avx2Kernel.bb31,
    positive8Input, positive8Result, List.foldlM_cons, List.foldlM_nil, Instr.run,
    BinOp.compute, UnOp.compute, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hsext, hshr, hguard,
    Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

/-- Applying the negative width-five block to an actual NAF byte needs only
its sign; both magnitude and index bounds are derived from construction. -/
theorem negative5_naf_block (E : ⟪avx2Kernel.Γ⟫) (n i : Nat) (s : GlobalState)
    (hnegative : nafDigits 5 n i ≤ 0) :
    avx2Kernel.bb20.run avx2Kernel.blockParams
      E[%1 := .value 0#8, %10 := .value 1#64, %117 := .value 16#8,
        %523 := .value (Execution.nafByte 5 n i)] s =
      .value ((negative5Result E (nafMagnitude5 n i), .inr 22), s) := by
  rw [(naf5_magnitude_cases n i).2 hnegative]
  exact negative5_block E (nafMagnitude5 n i) s

theorem positive5_naf_block (E : ⟪avx2Kernel.Γ⟫) (n i : Nat) (s : GlobalState)
    (hpositive : 0 ≤ nafDigits 5 n i) :
    avx2Kernel.bb23.run avx2Kernel.blockParams
      E[%10 := .value 1#64, %117 := .value 16#8,
        %523 := .value (Execution.nafByte 5 n i)] s =
      .value ((positive5Result E (nafMagnitude5 n i), .inr 25), s) := by
  rw [(naf5_magnitude_cases n i).1 hpositive]
  exact positive5_block E (nafMagnitude5 n i) s

theorem negative8_naf_block (E : ⟪avx2Kernel.Γ⟫) (n i : Nat) (s : GlobalState)
    (hnegative : nafDigits 8 n i ≤ 0) :
    avx2Kernel.bb27.run avx2Kernel.blockParams
      E[%1 := .value 0#8, %10 := .value 1#64, %222 := .value (-1 : BitVec 8),
        %704 := .value (Execution.nafByte 8 n i)] s =
      .value ((negative8Result E (nafMagnitude8 n i), .inr 29), s) := by
  rw [(naf8_magnitude_cases n i).2 hnegative]
  exact negative8_block E (nafMagnitude8 n i) s

theorem positive8_naf_block (E : ⟪avx2Kernel.Γ⟫) (n i : Nat) (s : GlobalState)
    (hpositive : 0 ≤ nafDigits 8 n i) :
    avx2Kernel.bb31.run avx2Kernel.blockParams
      E[%10 := .value 1#64, %222 := .value (-1 : BitVec 8),
        %704 := .value (Execution.nafByte 8 n i)] s =
      .value ((positive8Result E (nafMagnitude8 n i), .inr 33), s) := by
  rw [(naf8_magnitude_cases n i).1 hpositive]
  exact positive8_block E (nafMagnitude8 n i) s

end Agave.Ed25519.DoubleBase.ExecutionAvx2
