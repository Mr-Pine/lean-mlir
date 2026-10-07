import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2AdditionDefs
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ScanLoop
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGExecution

/-! Discharge the ladder's bb18 interface using the proved imported doubling
block. The remaining context premise is preservation under its concrete five
scratch stores; it contains no execution or point-arithmetic correctness. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
open Reduce64.Execution (SmallRange)
open Avx2PointAdd.Phases (packPoint)
set_option maxRecDepth 10000

variable {p : Avx2CFG.Primitives}

theorem double_successor_naf (a pos : Nat) :
    Avx2PointDouble.CFG.successor (Execution.nafByte 5 a pos) =
      digitBlockA (nafDigits 5 a pos) := by
  have hz : Execution.nafByte 5 a pos = 0#8 ↔ nafDigits 5 a pos = 0 := by
    rw [← byte_toInt_zero, Execution.nafByte_toInt 5 (Or.inl rfl)]
  unfold Avx2PointDouble.CFG.successor digitBlockA
  rw [Execution.nafByte_toInt 5 (Or.inl rfl)]
  split_ifs <;> simp_all [hz]

theorem double_exit_point (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point)
    (digits : Pointer) (pos : Fin 256) (a : Nat)
    (hP : Avx2PointAdd.pointReduced P) (hQ : Avx2PointAdd.pointValue P = Q) :
    PointAt (doubleStage (nafDigits 5 a pos.val))
      (Avx2PointDouble.CFG.exitEnv E P digits pos (Execution.nafByte 5 a pos.val))
      (avx2Double Q) := by
  have hv : Avx2PointAdd.pointValue (Avx2PointDouble.doublePoint P) = avx2Double Q :=
    (Avx2PointDouble.doublePoint_value hP).trans (congrArg avx2Double hQ)
  refine ⟨Avx2PointDouble.doublePoint P, Avx2PointDouble.doublePoint_reduced hP, hv, ?_⟩
  by_cases hz : nafDigits 5 a pos.val = 0
  · have hbyte : Execution.nafByte 5 a pos.val = 0#8 := by simp [Execution.nafByte, hz]
    rw [hbyte]
    obtain ⟨h3, h2, h1, h0, h4⟩ := Avx2PointDouble.CFG.exitEnv_zero_reads E P digits pos
    intro k
    fin_cases k
    · simpa [pointReg, doubleStage, hz] using h0
    · simpa [pointReg, doubleStage, hz] using h1
    · simpa [pointReg, doubleStage, hz] using h2
    · simpa [pointReg, doubleStage, hz] using h3
    · simpa [pointReg, doubleStage, hz] using h4
  · obtain ⟨h0, h1, h2, h3, h4⟩ :=
      Avx2PointDouble.CFG.exitEnv_reads E P digits pos (Execution.nafByte 5 a pos.val)
    intro k
    fin_cases k
    · simpa [pointReg, doubleStage, hz] using h0
    · simpa [pointReg, doubleStage, hz] using h1
    · simpa [pointReg, doubleStage, hz] using h2
    · simpa [pointReg, doubleStage, hz] using h3
    · simpa [pointReg, doubleStage, hz] using h4

theorem double_exit_digit (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point)
    (digits : Pointer) (pos : Fin 256) (digit : BitVec 8) :
    (Avx2PointDouble.CFG.exitEnv E P digits pos digit).read (%523) = .value digit := by
  unfold Avx2PointDouble.CFG.exitEnv
  split_ifs <;> simp [Avx2PointDouble.CFG.zeroEnv, Avx2PointDouble.CFG.dispatchEnv, mlir_env]

/-- The local double postcondition is derived from square/multiply contracts
and explicit live-in constants/pointers. Every digit load, branch, reduced
point witness and register frame is supplied by the actual bb18 proof. -/
theorem double_block_post (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hsquare : SquareContract p.call1) (hmul : MulContract p.call2)
    (hs : ContextStable ctx) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (pos : Fin 256) (Q : Extended F) (u v r : Pointer)
    (hready : LadderReady ctx a b da db E s pos) (hpoint : PointAt .loop E Q)
    (hwf : s.WF) (hu : SmallRange s.mem u 160) (hv : SmallRange s.mem v 160)
    (hr : SmallRange s.mem r 160) (huv : u.id ≠ v.id)
    (huA : u.id ≠ da.id) (hvA : v.id ≠ da.id) (hrA : r.id ≠ da.id)
    (huB : u.id ≠ db.id) (hvB : v.id ≠ db.id) (hrB : r.id ≠ db.id)
    (hconstants : Avx2PointDouble.CFG.Constants E)
    (hpointers : Avx2PointDouble.CFG.Pointers E u v r)
    (hcontext : ∀ P : Avx2PointAdd.Point, Avx2PointAdd.pointReduced P →
      ctx E (Avx2PointDouble.CFG.resultState s u v r P)) :
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 18
      (digitBlockA (nafDigits 5 a pos.val)) (doubleStage (nafDigits 5 a pos.val))
      (avx2Double Q) E s pos E' s' ∧
      E'.read (%523) = .value (Execution.nafByte 5 a pos.val) := by
  obtain ⟨P, hP, hQ, hreads⟩ := hpoint
  have hinput : Avx2PointDouble.CFG.inputReads E (packPoint P) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [pointReg] using hreads 0
    · simpa [pointReg] using hreads 1
    · simpa [pointReg] using hreads 2
    · simpa [pointReg] using hreads 3
    · simpa [pointReg] using hreads 4
  let E' := Avx2PointDouble.CFG.exitEnv E P da pos (Execution.nafByte 5 a pos.val)
  let s' := Avx2PointDouble.CFG.resultState s u v r P
  have hf : RegisterFrame 427 avx2Kernel.Γ.n E E' :=
    Avx2PointDouble.CFG.exitEnv_frame E P da pos _
  have hdigits : DigitMemory s' da db a b := by
    refine ⟨Avx2PointDouble.CFG.resultState_buffer s u v r P hready.digits.bufferA,
      Avx2PointDouble.CFG.resultState_buffer s u v r P hready.digits.bufferB, ?_, ?_⟩
    · intro i
      exact (Avx2PointDouble.CFG.resultState_read s u v r _ P 8
        (by simpa using huA) (by simpa using hvA) (by simpa using hrA)).trans
          (hready.digits.readA i)
    · intro i
      exact (Avx2PointDouble.CFG.resultState_read s u v r _ P 8
        (by simpa using huB) (by simpa using hvB) (by simpa using hrB)).trans
          (hready.digits.readB i)
  refine ⟨E', s', ⟨?_, ?_, double_exit_point E P da pos a hP hQ, hf⟩,
    double_exit_digit E P da pos _⟩
  · change BasicBlock.run avx2Kernel.blockParams E (avx2Kernel.bb18 p) s =
      .value ((E', .inr (digitBlockA (nafDigits 5 a pos.val))), s')
    simpa only [E', s', double_successor_naf] using
      Avx2PointDouble.CFG.block_correct p E s u v r da P pos
        (Execution.nafByte 5 a pos.val) hsquare hmul hwf hu hv hr huv
        hready.digits.bufferA huA hvA hrA (hready.digits.readA pos)
        hP hconstants hpointers hinput hready.control.zeroByte
        hready.control.digitsA hready.cursor
  · exact ⟨hready.control.of_frame hf, cursor_of_frame pos hf hready.cursor, hdigits,
      hs E E' s' (hf.weaken (by decide) (Nat.le_refl _)) (hcontext P hP)⟩

/-- Explicit live-in and scratch-store obligations for bb18. All functional
point doubling and branch correctness are absent from these premises. -/
structure DoubleInputs (ctx : LocalContext) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (da db u v r : Pointer) : Prop where
  wellFormed : s.WF
  prepared : SmallRange s.mem u 160
  square : SmallRange s.mem v 160
  result : SmallRange s.mem r 160
  separate : u.id ≠ v.id
  preparedA : u.id ≠ da.id
  squareA : v.id ≠ da.id
  resultA : r.id ≠ da.id
  preparedB : u.id ≠ db.id
  squareB : v.id ≠ db.id
  resultB : r.id ≠ db.id
  constants : Avx2PointDouble.CFG.Constants E
  pointers : Avx2PointDouble.CFG.Pointers E u v r
  contextStores : ∀ P : Avx2PointAdd.Point, Avx2PointAdd.pointReduced P →
    ctx E (Avx2PointDouble.CFG.resultState s u v r P)

theorem arithmeticBlocks_of_imported_double
    (hsquare : SquareContract p.call1) (hmul : MulContract p.call2)
    (hs : ContextStable ctx) (hadds : AdditionBlocks p g ctx a b da db table)
    (hinputs : ∀ E s pos, LadderReady ctx a b da db E s pos →
      ∃ u v r, DoubleInputs ctx E s da db u v r) :
    ArithmeticBlocks p g ctx a b da db table := by
  refine ⟨?_, hadds.subA, hadds.addA, hadds.subB, hadds.addB⟩
  intro E s pos Q hr hp
  obtain ⟨u, v, r, h⟩ := hinputs E s pos hr
  exact double_block_post p g hsquare hmul hs E s pos Q u v r hr hp
    h.wellFormed h.prepared h.square h.result h.separate
    h.preparedA h.squareA h.resultA h.preparedB h.squareB h.resultB
    h.constants h.pointers h.contextStores

end Agave.Ed25519.DoubleBase.ExecutionAvx2
