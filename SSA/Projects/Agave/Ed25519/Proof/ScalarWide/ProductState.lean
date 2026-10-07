import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ProductRefinement

/-! Exact register and memory states between the nine product columns. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def productStates (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) (scratch : Fin 9 → Pointer) : Fin 9 → GlobalState :=
  let s0 := state
  let s1 := {s0 with mem := s0.mem.storeAt (scratch 1) (column1Word a b left right)}
  let s2 := {s1 with mem := s1.mem.storeAt (scratch 2) (column2Word a b left right)}
  let s3 := {s2 with mem := s2.mem.storeAt (scratch 3) (column3Word a b left right)}
  let s4 := {s3 with mem := s3.mem.storeAt (scratch 4) (column4Word a b left right)}
  let s5 := {s4 with mem := s4.mem.storeAt (scratch 5) (column5Word a b left right)}
  let s6 := {s5 with mem := s5.mem.storeAt (scratch 6) (column6Word a b left right)}
  let s7 := {s6 with mem := s6.mem.storeAt (scratch 7) (column7Word a b left right)}
  let s8 := {s7 with mem := s7.mem.storeAt (scratch 8) (column8Word a b left right)}
  ![s0, s1, s2, s3, s4, s5, s6, s7, s8]

def productEnvs (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) : Fin 9 → Env program.Γ :=
  let e0 := inputProductEnv E (a 0) (b 0)
  let e1 := column1Env e0 a b left right
  let e2 := column2Env e1 a b left right
  let e3 := column3Env e2 a b left right
  let e4 := column4Env e3 a b left right
  let e5 := column5Env e4 a b left right
  let e6 := column6Env e5 a b left right
  let e7 := column7Env e6 a b left right
  let e8 := column8Env e7 a b left right
  ![e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem productStates_smallRange (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) (scratch : Fin 9 → Pointer) (q : Pointer) (count : Nat)
    (h : SmallRange state.mem q count) (i : Fin 9) :
    SmallRange (productStates state a b left right scratch i).mem q count := by
  fin_cases i <;> simp only [productStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_fin_one]
  all_goals repeat apply SmallRange.storeAt
  all_goals exact h

theorem productStates_fits (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) (scratch : Fin 9 → Pointer) (q : Pointer) (width : Nat)
    (h : Fits state.mem q width) (i : Fin 9) :
    Fits (productStates state a b left right scratch i).mem q width := by
  fin_cases i <;> simp only [productStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_fin_one]
  all_goals repeat apply Fits.storeAt
  all_goals exact h

theorem productStates_read (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) (scratch : Fin 9 → Pointer) (q : Pointer) (width : Nat)
    (h : ∀ j, (scratch j).id ≠ q.id) (i : Fin 9) :
    (productStates state a b left right scratch i).mem.readAt q width = state.mem.readAt q width := by
  fin_cases i <;> simp only [productStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_fin_one]
  all_goals simp only [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne (h _))]

theorem productStates_wf (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) (scratch : Fin 9 → Pointer) (h : state.WF) (i : Fin 9) :
    (productStates state a b left right scratch i).WF := by
  fin_cases i <;> simp only [productStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_fin_one]
  all_goals repeat apply GlobalState.WF.storeAt_mk
  all_goals exact h

/-- All product scratch stores disappear under the enclosing frame cleanup. -/
theorem productStates_erase (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (left right : Pointer) (scratch : Fin 9 → Pointer) (mark : Nat)
    (h : ∀ j, mark ≤ (scratch j).id.id) (i : Fin 9) :
    (productStates state a b left right scratch i).mem.eraseFrom mark = state.mem.eraseFrom mark := by
  fin_cases i <;> simp only [productStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_fin_one]
  all_goals simp only [MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le (h _)]

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
