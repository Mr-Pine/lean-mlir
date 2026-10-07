import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.AdditionState
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2AdditionDefs

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
open Avx2PointAdd (Point pointReduced pointValue)
open Avx2PointAdd.Phases
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem addition22_post (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2) (hs : ContextStable ctx)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (pos : Fin 256) (Q : Extended F)
    (q : Scratch) (base : Pointer) (bytes : Nat)
    (hready : LadderReady ctx a b da db E s pos)
    (hpoint : PointAt .doubled E Q) (hn : nafDigits 5 a pos.val < 0)
    (hi : E.read (%527) = .value (BitVec.ofNat 64 ((nafMagnitude5 a pos.val).val / 2)))
    (hstatic : AdditionStatic22 E q base)
    (hm : AdditionMemory ctx table false E s da db q base (additionIndex5 a pos.val) bytes) :
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 22 26 .afterA
      (signedPoint table false (nafDigits 5 a pos.val) Q) E s pos E' s' := by
  obtain ⟨P, hP, hQ, hreads⟩ := hpoint
  obtain ⟨C, hC, hcache, hCvalue⟩ := hm.cache
  let index := additionIndex5 a pos.val
  let E' := Avx2PointAdd.CFG.exit22Env E q base index P C
  let s' := pipelineState s q true P C 7
  have hf : OutputFrame q s s' := Avx2PointAdd.CFG.block22_memoryFrame s q P C hm.memory.wf
  have hr : RegisterFrame 427 avx2Kernel.Γ.n E E' := Avx2PointAdd.CFG.exit22_frame E q base index P C
  refine ⟨E', s', ⟨?_, hready.of_pointAddFrame hs hm hf hr, ?_, hr⟩⟩
  · exact Avx2PointAdd.CFG.block22_correct p E s q base index bytes P C hmul
      (hstatic.input hreads hi) hm.memory hm.tableRange hm.indexRange hcache hP hC
  · refine ⟨resultPoint true P C, Avx2PointAdd.CFG.block22_reduced hP hC, ?_, ?_⟩
    · have hv := Avx2PointAdd.CFG.block22_field hP hC
      rw [hQ, hCvalue] at hv
      have hnpos : ¬ 0 < nafDigits 5 a pos.val := by omega
      simpa [signedPoint, digitOps, hn, hnpos, avx2Step, avx2Add,
        avx2Cache_negatePoint, additionIndex5, nafMagnitude5] using hv
    · obtain ⟨h3, h2, h1, h0, h4⟩ := Avx2PointAdd.CFG.exit22_point E q base index P C
      intro k
      fin_cases k
      · simpa [E', pointReg] using h0
      · simpa [E', pointReg] using h1
      · simpa [E', pointReg] using h2
      · simpa [E', pointReg] using h3
      · simpa [E', pointReg] using h4

theorem addition25_post (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2) (hs : ContextStable ctx)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (pos : Fin 256) (Q : Extended F)
    (q : Scratch) (base : Pointer) (bytes : Nat)
    (hready : LadderReady ctx a b da db E s pos)
    (hpoint : PointAt .doubled E Q) (hn : 0 < nafDigits 5 a pos.val)
    (hi : E.read (%625) = .value (BitVec.ofNat 64 ((nafMagnitude5 a pos.val).val / 2)))
    (hstatic : AdditionStatic25 E q base)
    (hm : AdditionMemory ctx table false E s da db q base (additionIndex5 a pos.val) bytes) :
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 25 26 .afterA
      (signedPoint table false (nafDigits 5 a pos.val) Q) E s pos E' s' := by
  obtain ⟨P, hP, hQ, hreads⟩ := hpoint
  obtain ⟨C, hC, hcache, hCvalue⟩ := hm.cache
  let index := additionIndex5 a pos.val
  let E' := Avx2PointAdd.CFG.exit25Env E q base index P C
  let s' := pipelineState s q false P C 7
  have hf : OutputFrame q s s' := Avx2PointAdd.CFG.block25_memoryFrame s q P C hm.memory.wf
  have hr : RegisterFrame 427 avx2Kernel.Γ.n E E' := Avx2PointAdd.CFG.exit25_frame E q base index P C
  refine ⟨E', s', ⟨?_, hready.of_pointAddFrame hs hm hf hr, ?_, hr⟩⟩
  · exact Avx2PointAdd.CFG.block25_correct p E s q base index bytes P C hmul
      (hstatic.input hreads hi) hm.memory hm.tableRange hm.indexRange hcache hP hC
  · refine ⟨resultPoint false P C, Avx2PointAdd.CFG.block25_reduced hP hC, ?_, ?_⟩
    · have hv := Avx2PointAdd.CFG.block25_field hP hC
      rw [hQ, hCvalue] at hv
      simpa [signedPoint, digitOps, hn, avx2Step, avx2Add,
        additionIndex5, nafMagnitude5] using hv
    · obtain ⟨h3, h2, h1, h0, h4⟩ := Avx2PointAdd.CFG.exit25_point E q base index P C
      intro k
      fin_cases k
      · simpa [E', pointReg] using h0
      · simpa [E', pointReg] using h1
      · simpa [E', pointReg] using h2
      · simpa [E', pointReg] using h3
      · simpa [E', pointReg] using h4

theorem addition29_post (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2) (hs : ContextStable ctx)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (pos : Fin 256) (Q : Extended F)
    (q : Scratch) (base : Pointer) (bytes : Nat)
    (hready : LadderReady ctx a b da db E s pos)
    (hpoint : PointAt .afterA E Q) (hn : nafDigits 8 b pos.val < 0)
    (hi : E.read (%708) = .value (BitVec.ofNat 64 ((nafMagnitude8 b pos.val).val / 2)))
    (hstatic : AdditionStatic29 E q base)
    (hm : AdditionMemory ctx table true E s da db q base (additionIndex8 b pos.val) bytes) :
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 29 30 .afterB
      (signedPoint table true (nafDigits 8 b pos.val) Q) E s pos E' s' := by
  obtain ⟨P, hP, hQ, hreads⟩ := hpoint
  obtain ⟨C, hC, hcache, hCvalue⟩ := hm.cache
  let index := additionIndex8 b pos.val
  let E' := Avx2PointAdd.CFG.exit29Env E q base index P C
  let s' := pipelineState s q true P C 7
  have hf : OutputFrame q s s' := Avx2PointAdd.CFG.block29_memoryFrame s q P C hm.memory.wf
  have hr : RegisterFrame 427 avx2Kernel.Γ.n E E' := Avx2PointAdd.CFG.exit29_frame E q base index P C
  refine ⟨E', s', ⟨?_, hready.of_pointAddFrame hs hm hf hr, ?_, hr⟩⟩
  · exact Avx2PointAdd.CFG.block29_correct p E s q base index bytes P C hmul
      (hstatic.input hreads hi) hm.memory hm.tableRange hm.indexRange hcache hP hC
  · refine ⟨resultPoint true P C, Avx2PointAdd.CFG.block29_reduced hP hC, ?_, ?_⟩
    · have hv := Avx2PointAdd.CFG.block29_field hP hC
      rw [hQ, hCvalue] at hv
      have hnpos : ¬ 0 < nafDigits 8 b pos.val := by omega
      simpa [signedPoint, digitOps, hn, hnpos, avx2Step, avx2Add,
        avx2Cache_negatePoint, additionIndex8, nafMagnitude8] using hv
    · obtain ⟨h3, h2, h1, h0, h4⟩ := Avx2PointAdd.CFG.exit29_point E q base index P C
      intro k
      fin_cases k
      · simpa [E', pointReg] using h0
      · simpa [E', pointReg] using h1
      · simpa [E', pointReg] using h2
      · simpa [E', pointReg] using h3
      · simpa [E', pointReg] using h4

theorem addition33_post (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hmul : Avx2PointAdd.Execution.MulContract p.call2) (hs : ContextStable ctx)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (pos : Fin 256) (Q : Extended F)
    (q : Scratch) (base : Pointer) (bytes : Nat)
    (hready : LadderReady ctx a b da db E s pos)
    (hpoint : PointAt .afterA E Q) (hn : 0 < nafDigits 8 b pos.val)
    (hi : E.read (%813) = .value (BitVec.ofNat 64 ((nafMagnitude8 b pos.val).val / 2)))
    (hstatic : AdditionStatic33 E q base)
    (hm : AdditionMemory ctx table true E s da db q base (additionIndex8 b pos.val) bytes) :
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 33 30 .afterB
      (signedPoint table true (nafDigits 8 b pos.val) Q) E s pos E' s' := by
  obtain ⟨P, hP, hQ, hreads⟩ := hpoint
  obtain ⟨C, hC, hcache, hCvalue⟩ := hm.cache
  let index := additionIndex8 b pos.val
  let E' := Avx2PointAdd.CFG.exit33Env E q base index P C
  let s' := pipelineState s q false P C 7
  have hf : OutputFrame q s s' := Avx2PointAdd.CFG.block33_memoryFrame s q P C hm.memory.wf
  have hr : RegisterFrame 427 avx2Kernel.Γ.n E E' := Avx2PointAdd.CFG.exit33_frame E q base index P C
  refine ⟨E', s', ⟨?_, hready.of_pointAddFrame hs hm hf hr, ?_, hr⟩⟩
  · exact Avx2PointAdd.CFG.block33_correct p E s q base index bytes P C hmul
      (hstatic.input hreads hi) hm.memory hm.tableRange hm.indexRange hcache hP hC
  · refine ⟨resultPoint false P C, Avx2PointAdd.CFG.block33_reduced hP hC, ?_, ?_⟩
    · have hv := Avx2PointAdd.CFG.block33_field hP hC
      rw [hQ, hCvalue] at hv
      simpa [signedPoint, digitOps, hn, avx2Step, avx2Add,
        additionIndex8, nafMagnitude8] using hv
    · obtain ⟨h3, h2, h1, h0, h4⟩ := Avx2PointAdd.CFG.exit33_point E q base index P C
      intro k
      fin_cases k
      · simpa [E', pointReg] using h0
      · simpa [E', pointReg] using h1
      · simpa [E', pointReg] using h2
      · simpa [E', pointReg] using h3
      · simpa [E', pointReg] using h4

/-- Ordinary live-in register and memory/cache invariants for the four
arithmetic sites. These fields contain no block execution or arithmetic-result
premise. The already proved guards supply each dynamic digit-index register. -/
structure AdditionInputs (ctx : LocalContext) (a b : Nat) (da db : Pointer)
    (table : TableIndex → Extended F) : Prop where
  subA : ∀ E s pos, LadderReady ctx a b da db E s pos →
    ∃ q base bytes, AdditionStatic22 E q base ∧
      AdditionMemory ctx table false E s da db q base (additionIndex5 a pos.val) bytes
  addA : ∀ E s pos, LadderReady ctx a b da db E s pos →
    ∃ q base bytes, AdditionStatic25 E q base ∧
      AdditionMemory ctx table false E s da db q base (additionIndex5 a pos.val) bytes
  subB : ∀ E s pos, LadderReady ctx a b da db E s pos →
    ∃ q base bytes, AdditionStatic29 E q base ∧
      AdditionMemory ctx table true E s da db q base (additionIndex8 b pos.val) bytes
  addB : ∀ E s pos, LadderReady ctx a b da db E s pos →
    ∃ q base bytes, AdditionStatic33 E q base ∧
      AdditionMemory ctx table true E s da db q base (additionIndex8 b pos.val) bytes

/-- Discharge all four ladder addition obligations with the actual imported
AVX2 field multiplier. Square, doubling and table-constructor execution are
independent of this theorem. -/
theorem additionBlocks_of_imported_mul (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (hcall : p.call2 = Avx2FieldMul.program.call) (hs : ContextStable ctx)
    (hinputs : AdditionInputs ctx a b da db table) :
    AdditionBlocks p g ctx a b da db table := by
  have hmul : Avx2PointAdd.Execution.MulContract p.call2 := by
    rw [hcall]
    exact Avx2PointAdd.Execution.imported_mul_contract
  constructor
  · intro E s pos Q hr hp hn hi
    obtain ⟨q, base, bytes, hstatic, hm⟩ := hinputs.subA E s pos hr
    exact addition22_post p g hmul hs E s pos Q q base bytes hr hp hn hi hstatic hm
  · intro E s pos Q hr hp hn hi
    obtain ⟨q, base, bytes, hstatic, hm⟩ := hinputs.addA E s pos hr
    exact addition25_post p g hmul hs E s pos Q q base bytes hr hp hn hi hstatic hm
  · intro E s pos Q hr hp hn hi
    obtain ⟨q, base, bytes, hstatic, hm⟩ := hinputs.subB E s pos hr
    exact addition29_post p g hmul hs E s pos Q q base bytes hr hp hn hi hstatic hm
  · intro E s pos Q hr hp hn hi
    obtain ⟨q, base, bytes, hstatic, hm⟩ := hinputs.addB E s pos hr
    exact addition33_post p g hmul hs E s pos Q q base bytes hr hp hn hi hstatic hm

end Agave.Ed25519.DoubleBase.ExecutionAvx2
