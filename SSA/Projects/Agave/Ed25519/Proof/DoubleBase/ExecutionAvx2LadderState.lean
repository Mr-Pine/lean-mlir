import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2NAFFrame
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2GuardRun
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Avx2Group
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseRepresentation
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Refinement

/-! Concrete register relations at the four point-operation boundaries of the
actual AVX2 ladder. They expose reduced physical limbs and the exact packed
register permutation, rather than assuming a backend or iteration refinement. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F)
open Avx2PointAdd.Phases (packPoint)
open NAF.Memory (Buffer)
set_option maxRecDepth 10000

inductive PointStage
  | loop
  | doubled
  | afterA
  | afterB

def pointReg : PointStage → Fin 5 → Reg avx2Kernel.Γ (.vec 8 32)
  | .loop => ![%424, %423, %422, %421, %425]
  | .doubled => ![%517, %518, %519, %520, %521]
  | .afterA => ![%701, %700, %699, %698, %702]
  | .afterB => ![%808, %807, %806, %805, %809]

def PointReads (stage : PointStage) (E : ⟪avx2Kernel.Γ⟫)
    (P : Avx2PointAdd.Point) : Prop :=
  ∀ k : Fin 5, E.read (pointReg stage k) = Ty.wrap (packPoint P k)

/-- The witness is an actual nonpoison reduced packed limb point. -/
def PointAt (stage : PointStage) (E : ⟪avx2Kernel.Γ⟫) (Q : Extended F) : Prop :=
  ∃ P : Avx2PointAdd.Point,
    Avx2PointAdd.pointReduced P ∧ Avx2PointAdd.pointValue P = Q ∧ PointReads stage E P

structure ControlReady (E : ⟪avx2Kernel.Γ⟫) (digitsA digitsB : Pointer) : Prop where
  zeroByte : E.read (%1) = .value 0#8
  zeroWord : E.read (%4) = .value 0#64
  one : E.read (%10) = .value 1#64
  decrement : E.read (%19) = .value (-1 : BitVec 64)
  limit5 : E.read (%117) = .value 16#8
  minusByte : E.read (%222) = .value (-1 : BitVec 8)
  digitsA : E.read (%266) = .value digitsA
  digitsB : E.read (%265) = .value digitsB

structure DigitMemory (s : GlobalState) (digitsA digitsB : Pointer) (a b : Nat) : Prop where
  bufferA : Buffer s.mem digitsA 256
  bufferB : Buffer s.mem digitsB 256
  readA : ∀ i : Fin 256,
    s.mem.readAt (digitsA.add (BitVec.ofNat 64 i.val)) 8 = Execution.nafByte 5 a i.val
  readB : ∀ i : Fin 256,
    s.mem.readAt (digitsB.add (BitVec.ofNat 64 i.val)) 8 = Execution.nafByte 8 b i.val

theorem ControlReady.of_frame (h : ControlReady E a b)
    (hf : RegisterFrame 427 avx2Kernel.Γ.n E E') : ControlReady E' a b := by
  rcases h with ⟨h1, h4, h10, h19, h117, h222, ha, hb⟩
  constructor
  all_goals rw [hf.read _ (by decide)]
  all_goals assumption

theorem cursor_of_frame {E E' : ⟪avx2Kernel.Γ⟫} (pos : Fin 256) (hf : RegisterFrame 427 avx2Kernel.Γ.n E E')
    (h : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    E'.read (%426) = .value (BitVec.ofNat 64 pos.val) := by
  rw [hf.read _ (by decide)]
  exact h

theorem dispatchBInput_of_ready (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer) (pos : Fin 256)
    (h : ControlReady E a b) (hc : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    dispatchBInput E b pos = E := by
  unfold dispatchBInput
  rw [Env.write_of_read E (%1) h.zeroByte, Env.write_of_read E (%265) h.digitsB,
    Env.write_of_read E (%426) hc]

theorem backedgeInput_of_ready (E : ⟪avx2Kernel.Γ⟫) (a b : Pointer) (pos : Fin 256)
    (h : ControlReady E a b) (hc : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    backedgeInput E pos = E := by
  unfold backedgeInput
  rw [Env.write_of_read E (%4) h.zeroWord, Env.write_of_read E (%19) h.decrement,
    Env.write_of_read E (%426) hc]

theorem PointAt.backedgeNext (h : PointAt .afterB E Q) (pos : Fin 256) :
    PointAt .loop (backedgeNext E pos) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.backedgeNext, ExecutionAvx2.backedgeResult, backedgeInput, mlir_env] using hk

theorem PointAt.backedgeResult (h : PointAt .afterB E Q) (pos : Fin 256) :
    PointAt .afterB (backedgeResult E pos) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.backedgeResult, backedgeInput, mlir_env] using hk

theorem PointAt.dispatchBZero (h : PointAt .afterA E Q) (digits : Pointer)
    (pos : Fin 256) (digit : BitVec 8) :
    PointAt .afterB (dispatchBZero E digits pos digit) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.dispatchBZero, ExecutionAvx2.dispatchBResult, dispatchBInput, mlir_env] using hk

theorem PointAt.dispatchBResult (h : PointAt .afterA E Q) (digits : Pointer)
    (pos : Fin 256) (digit : BitVec 8) :
    PointAt .afterA (dispatchBResult E digits pos digit) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.dispatchBResult, dispatchBInput, mlir_env] using hk

theorem PointAt.negative5Result (h : PointAt .doubled E Q) (m : Fin 16) :
    PointAt .doubled (negative5Result E m) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.negative5Result, negative5Input, mlir_env] using hk

theorem PointAt.positive5Result (h : PointAt .doubled E Q) (m : Fin 16) :
    PointAt .doubled (positive5Result E m) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.positive5Result, positive5Input, mlir_env] using hk

theorem PointAt.negative8Result (h : PointAt .afterA E Q) (m : Fin 128) :
    PointAt .afterA (negative8Result E m) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.negative8Result, negative8Input, mlir_env] using hk

theorem PointAt.positive8Result (h : PointAt .afterA E Q) (m : Fin 128) :
    PointAt .afterA (positive8Result E m) Q := by
  obtain ⟨P, hP, hQ, hreads⟩ := h
  refine ⟨P, hP, hQ, ?_⟩
  intro k
  have hk := hreads k
  fin_cases k <;> simpa [pointReg, ExecutionAvx2.positive8Result, positive8Input, mlir_env] using hk

theorem ControlReady.backedgeNext (h : ControlReady E a b) (pos : Fin 256) :
    ControlReady (backedgeNext E pos) a b := by
  rcases h with ⟨h1, h4, h10, h19, h117, h222, ha, hb⟩
  constructor <;> simp_all [ExecutionAvx2.backedgeNext, ExecutionAvx2.backedgeResult, backedgeInput, mlir_env]

theorem backedgeNext_cursor (E : ⟪avx2Kernel.Γ⟫) (n : Nat) (hn : n + 1 < 256) :
    (backedgeNext E ⟨n + 1, hn⟩).read (%426) = .value (BitVec.ofNat 64 n) := by
  have hsub : ((n + 1 : Nat) : Int) - 1 = (n : Int) := by omega
  simp [ExecutionAvx2.backedgeNext, mlir_env, hsub]

/-- Actual zero exit and nonzero backedge, carrying the concrete packed point
relation through the source's reverse-first-four register transfer. -/
theorem backedge_point_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (a b : Pointer) (pos : Fin 256)
    (Q : Extended F) (hready : ControlReady E a b) (hpoint : PointAt .afterB E Q)
    (hc : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    (avx2Kernel p g).runFrom E 30 s =
      if pos.val = 0 then (avx2Kernel p g).runFrom (backedgeResult E pos) 34 s
      else (avx2Kernel p g).runFrom (backedgeNext E pos) 18 s := by
  have hrun := backedge_run p g E pos s
  rwa [backedgeInput_of_ready E a b pos hready hc] at hrun

end Agave.Ed25519.DoubleBase.ExecutionAvx2
