import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2LiveContext
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2LiveRegisters
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Contracts

/-! Discharge every local arithmetic input from the inhabited live context.
All remaining preservation obligations are concrete private-memory frames. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Reduce64.Execution (SmallRange)
open Conformance.BackendExecution (Invocation readPoint)
open Avx2PointAdd.Phases
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem additionMemory_of_liveContext (h : LiveContext g i initial E s)
    (site : Fin 4) (base : Pointer) (index : Fin 64) (bytes : Nat)
    (hr : SmallRange s.mem base bytes) (hi : 160 * index.val + 160 ≤ bytes)
    (hid : base.id.id < initial.alloc.nextFreeBlock ∨
      initial.alloc.nextFreeBlock + 27 ≤ base.id.id)
    (hc : ∃ C : Avx2PointAdd.Point, Avx2PointAdd.pointReduced C ∧
      Avx2FieldMul.Execution.readBlocks s.mem (tableRow base index) = packPoint C ∧
      Avx2PointAdd.pointValue C = avx2Cache (table (side, index.val))) :
    AdditionMemory (LiveContext g i initial) table side E s
      (avx2StackPtr initial 29) (avx2StackPtr initial 28)
      (loopScratch initial site) base index bytes := by
  refine ⟨loopScratch_memory h site _ (tableRow_live hr index hi) (by simpa [tableRow] using hid),
    hr, hi, hc, ?_, ?_, ?_⟩
  · intro k
    exact loopScratch_digits initial site k 29 (by decide)
  · intro k
    exact loopScratch_digits initial site k 28 (by decide)
  · intro s' hf
    exact h.of_privateFrame (LoopPrivateFrame.of_pointAdd hf (loopScratch_private initial site))

theorem additionMemory_dynamic (h : LiveContext g i initial E s)
    (site : Fin 4) (a pos : Nat) :
    AdditionMemory (LiveContext g i initial)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint initial i.pointA))) false E s
      (avx2StackPtr initial 29) (avx2StackPtr initial 28)
      (loopScratch initial site) (avx2StackPtr initial 27) (additionIndex5 a pos) 1280 := by
  have hidx : (additionIndex5 a pos).val < 8 := by
    have hm := (nafMagnitude5 a pos).isLt
    change (nafMagnitude5 a pos).val / 2 < 8
    omega
  apply additionMemory_of_liveContext h site _ _ _ h.framed.1.tableRange
    (by omega) (Or.inr (stack27_protected initial))
  let k : Fin 8 := ⟨(additionIndex5 a pos).val, hidx⟩
  obtain ⟨hred, hval⟩ := h.framed.1.tableValues k
  refine ⟨packedPoint s.mem (tableRow (avx2StackPtr initial 27) (additionIndex5 a pos)),
    hred, (packPoint_readPoint _ _).symm, ?_⟩
  simpa [finiteTable, Tables.avx2DoubleBaseTable, tableRow, hidx, k] using hval

theorem additionMemory_static (h : LiveContext g i initial E s)
    (site : Fin 4) (b pos : Nat) :
    AdditionMemory (LiveContext g i initial)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint initial i.pointA))) true E s
      (avx2StackPtr initial 29) (avx2StackPtr initial 28)
      (loopScratch initial site) g.address2 (additionIndex8 b pos) 10240 := by
  have hidx := (additionIndex8 b pos).isLt
  apply additionMemory_of_liveContext h site _ _ _ h.base.1
    (by omega) (Or.inl h.baseOld)
  obtain ⟨C, hred, hread, hvalue⟩ := h.base.2 (additionIndex8 b pos)
  exact ⟨C, hred, hread, by simpa [finiteTable, Tables.avx2DoubleBaseTable, hidx] using hvalue⟩

/-- No caller hypothesis supplies arithmetic block execution or arbitrary
register readiness: the actual retained loop context supplies every field. -/
theorem liveArithmeticInputs (g : Avx2CFG.Globals) (i : Invocation) (initial : GlobalState) :
    ArithmeticInputs (LiveContext g i initial)
      (initial.mem.readAt i.scalarA 256).toNat (initial.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr initial 29) (avx2StackPtr initial 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint initial i.pointA))) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro E s pos h
    exact ⟨loopScratch initial 0, avx2StackPtr initial 27, 1280,
      h.localContext.registers.addition22, additionMemory_dynamic h.localContext 0 _ _⟩
  · intro E s pos h
    exact ⟨loopScratch initial 1, avx2StackPtr initial 27, 1280,
      h.localContext.registers.addition25, additionMemory_dynamic h.localContext 1 _ _⟩
  · intro E s pos h
    exact ⟨loopScratch initial 2, g.address2, 10240,
      h.localContext.registers.addition29, additionMemory_static h.localContext 2 _ _⟩
  · intro E s pos h
    exact ⟨loopScratch initial 3, g.address2, 10240,
      h.localContext.registers.addition33, additionMemory_static h.localContext 3 _ _⟩
  · intro E s pos h
    refine ⟨avx2StackPtr initial 19, avx2StackPtr initial 18, avx2StackPtr initial 26,
      h.localContext.framed.1.wellFormed, h.localContext.scratch 19 (by decide),
      h.localContext.scratch 18 (by decide), h.localContext.scratch 26 (by decide),
      avx2Stack_separate initial 19 18 (by decide),
      avx2Stack_separate initial 19 29 (by decide),
      avx2Stack_separate initial 18 29 (by decide),
      avx2Stack_separate initial 26 29 (by decide),
      avx2Stack_separate initial 19 28 (by decide),
      avx2Stack_separate initial 18 28 (by decide),
      avx2Stack_separate initial 26 28 (by decide),
      h.localContext.registers.doubleConstants, h.localContext.registers.doublePointers, ?_⟩
    intro P _
    exact h.localContext.of_privateFrame
      (resultState_loopPrivateFrame initial s P h.localContext.framed.1.wellFormed)

theorem liveArithmeticBlocks (g : Avx2CFG.Globals) (i : Invocation) (initial : GlobalState)
    (table : Vals [.ptr, .ptr] → EffectM (Vals []))
    (panic : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])) :
    ArithmeticBlocks (linkedArithmetic table panic) g (LiveContext g i initial)
      (initial.mem.readAt i.scalarA 256).toNat (initial.mem.readAt i.scalarB 256).toNat
      (avx2StackPtr initial 29) (avx2StackPtr initial 28)
      (finiteTable (Tables.avx2DoubleBaseTable (readPoint initial i.pointA))) :=
  arithmeticBlocks_of_local_inputs _ g rfl imported_square_contract
    (liveContext_stable g i initial) (liveArithmeticInputs g i initial)

end Agave.Ed25519.DoubleBase.ExecutionAvx2
