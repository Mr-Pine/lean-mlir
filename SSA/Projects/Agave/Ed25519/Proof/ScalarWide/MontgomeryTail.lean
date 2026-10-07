import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryBorrow
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryAddback
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.CallPhases
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBox

/-! Composition of the final 78 imported Montgomery instructions, including
the actual black-box callee, all retained flags, stores, and zeroizations. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul

open LeanMLIR.RIR
open ScalarWide.Subtraction
open Agave.Ed25519.Reduce64.Execution (SmallRange)

/-- A proved instruction slice advances the actual block continuation. -/
theorem runBodyFrom_chunk {block : BasicBlock Γ ts bp} {E E' : Env Γ}
    {s s' : GlobalState} {start count : Nat}
    (h : List.foldlM Instr.run E ((block.body.drop start).take count) s = .value (E', s')) :
    block.runBodyFrom E start s = block.runBodyFrom E' (start + count) s' := by
  unfold BasicBlock.runBodyFrom
  conv_lhs => rw [← List.take_append_drop count (block.body.drop start), List.foldlM_append]
  simp only [EffectM.bind_eq, h, mlir_effect, List.drop_drop]
  rfl

/-- Compose the tail while treating each phase's register and memory states as
parameters. Keeping these states abstract avoids normalizing the full register
update chain while checking the continuation proof. -/
private theorem compose_tail {block : BasicBlock Γ ts bp}
    {E E1 E2 E3 E4 : Env Γ} {state state1 state2 : GlobalState}
    (hborrow : List.foldlM Instr.run E ((block.body.drop 208).take 18) state =
      .value (E1, state))
    (hcall : block.runBodyFrom E1 226 state = block.runBodyFrom E2 227 state1)
    (hadd : List.foldlM Instr.run E2 ((block.body.drop 227).take 23) state1 =
      .value (E3, state1))
    (hstores : List.foldlM Instr.run E3 (block.body.drop 250) state1 =
      .value (E4, state2)) :
    block.runBodyFrom E 208 state = .value (E4, state2) :=
  (runBodyFrom_chunk hborrow).trans
    (hcall.trans ((runBodyFrom_chunk hadd).trans hstores))

/-- Concrete register invariant at source instruction 208. Only the five
normalized quotient limbs vary; all other fields are startup constants,
caller output, and the nine allocated scratch pointers. -/
structure TailReady (E : Env program.Γ) (x : Fin 5 → BitVec 52)
    (out : Pointer) (scratch : Fin 9 → Pointer) : Prop where
  x0 : E.read (%165) = .value ((x 0).setWidth 64)
  x1 : E.read (%173) = .value ((x 1).setWidth 64)
  x2 : E.read (%179) = .value ((x 2).setWidth 64)
  x3 : E.read (%185) = .value ((x 3).setWidth 64)
  x4 : E.read (%187) = .value ((x 4).setWidth 64)
  out : E.read (%arg0) = .value (out)
  scratch0 : E.read (%24) = .value (scratch 0)
  scratch1 : E.read (%25) = .value (scratch 1)
  scratch2 : E.read (%26) = .value (scratch 2)
  scratch3 : E.read (%27) = .value (scratch 3)
  scratch4 : E.read (%28) = .value (scratch 4)
  scratch5 : E.read (%29) = .value (scratch 5)
  scratch6 : E.read (%30) = .value (scratch 6)
  scratch7 : E.read (%31) = .value (scratch 7)
  scratch8 : E.read (%32) = .value (scratch 8)
  c1 : E.read (%1) = .value (8#64)
  c2 : E.read (%2) = .value (16#64)
  c3 : E.read (%3) = .value (24#64)
  c4 : E.read (%4) = .value (32#64)
  c6 : E.read (%6) = .value (4503599627370495#64)
  c12 : E.read (%12) = .value ((-671914833335277 : BitVec 64))
  c13 : E.read (%13) = .value (63#64)
  c14 : E.read (%14) = .value ((-3916664325105025 : BitVec 64))
  c15 : E.read (%15) = .value ((-1367801 : BitVec 64))
  c16 : E.read (%16) = .value ((-17592186044416 : BitVec 64))
  c17 : E.read (%17) = .value (0#64)
  c18 : E.read (%18) = .value (671914833335277#64)
  c19 : E.read (%19) = .value (3916664325105025#64)
  c20 : E.read (%20) = .value (52#64)
  c21 : E.read (%21) = .value (1367801#64)
  c22 : E.read (%22) = .value (17592186044416#64)
  c23 : E.read (%23) = .value (0#128)

def tailLow (x : Fin 5 → BitVec 52) : Fin 4 → BitVec 64 :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  fun i => d ⟨i.val, by omega⟩ &&& 4503599627370495#64

def tailWords (x : Fin 5 → BitVec 52) : Fin 5 → BitVec 64 :=
  addback (differences (x 0) (x 1) (x 2) (x 3) (x 4))

def tailEnv (E : Env program.Γ) (x : Fin 5 → BitVec 52) (out : Pointer) : Env program.Γ :=
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  storesEnv (addbackEnv ((borrowEnv E x)[%206 := .value (borrowByte d)])
    (tailLow x) (d 4) (borrowByte d)) out

def tailState (state : GlobalState) (x : Fin 5 → BitVec 52)
    (out : Pointer) (scratch : Fin 9 → Pointer) : GlobalState :=
  { alloc := (state.alloca 1).alloc,
    mem := zeroizeStores (outputStores state.mem out (tailWords x)) scratch }

/-- A suffix update preserves the earlier registers without inspecting any
of the arithmetic values installed by that suffix. -/
private theorem addbackEnv_read_early (E : Env program.Γ)
    (low : Fin 4 → BitVec 64) (top : BitVec 64) (byte : BitVec 8)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 207) :
    (addbackEnv E low top byte).read (.val i ht) = E.read (.val i ht) := by
  unfold addbackEnv
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

private theorem borrowEnv_read_early (E : Env program.Γ) (x : Fin 5 → BitVec 52)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 188) :
    (borrowEnv E x).read (.val i ht) = E.read (.val i ht) := by
  unfold borrowEnv
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

private def maskedLow (d : Limbs) : Fin 4 → BitVec 64 :=
  fun i => d ⟨i.val, by omega⟩ &&& 4503599627370495#64

private theorem addbackEnv_output0 (E : Env program.Γ) (d : Limbs) :
    (addbackEnv E (maskedLow d) (d 4) (borrowByte d)).read (%211) =
      .value (addback d 0) := by
  rfl

private theorem addbackEnv_output1 (E : Env program.Γ) (d : Limbs) :
    (addbackEnv E (maskedLow d) (d 4) (borrowByte d)).read (%216) =
      .value (addback d 1) := by
  rfl

private theorem addbackEnv_output2 (E : Env program.Γ) (d : Limbs) :
    (addbackEnv E (maskedLow d) (d 4) (borrowByte d)).read (%221) =
      .value (addback d 2) := by
  rfl

private theorem addbackEnv_output3 (E : Env program.Γ) (d : Limbs) :
    (addbackEnv E (maskedLow d) (d 4) (borrowByte d)).read (%224) =
      .value (addback d 3) := by
  rfl

private theorem addbackEnv_output4 (E : Env program.Γ) (d : Limbs) :
    (addbackEnv E (maskedLow d) (d 4) (borrowByte d)).read (%229) =
      .value (addback d 4) := by
  rfl

/-- Actual complete borrow/black-box/addback/store/zeroize tail. No phase
execution premise is assumed; only its entry register and live-memory facts. -/
theorem tail_run (p : Primitives)
    (hblack : p.blackBoxByte = Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program.call)
    (E : Env program.Γ) (state : GlobalState) (x : Fin 5 → BitVec 52)
    (out : Pointer) (scratch : Fin 9 → Pointer)
    (hr : TailReady E x out scratch) (hwf : state.WF)
    (hout : SmallRange state.mem out 40) (hscratch : ∀ i, Fits state.mem (scratch i) 128) :
    (program.entry p).runBodyFrom E 208 state =
      .value (tailEnv E x out, tailState state x out scratch) := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  let byte := borrowByte d
  let E1 := borrowEnv E x
  let E2 := E1[%206 := .value byte]
  let E3 := addbackEnv E2 (tailLow x) (d 4) byte
  let state1 : GlobalState := {state with alloc := (state.alloca 1).alloc}
  have hx0 := hr.x0
  have hx1 := hr.x1
  have hx2 := hr.x2
  have hx3 := hr.x3
  have hx4 := hr.x4
  have houtReg := hr.out
  change E.args 0 = .value out at houtReg
  have hscratch0 := hr.scratch0
  have hscratch1 := hr.scratch1
  have hscratch2 := hr.scratch2
  have hscratch3 := hr.scratch3
  have hscratch4 := hr.scratch4
  have hscratch5 := hr.scratch5
  have hscratch6 := hr.scratch6
  have hscratch7 := hr.scratch7
  have hscratch8 := hr.scratch8
  have hc1 := hr.c1
  have hc2 := hr.c2
  have hc3 := hr.c3
  have hc4 := hr.c4
  have hc6 := hr.c6
  have hc12 := hr.c12
  have hc13 := hr.c13
  have hc14 := hr.c14
  have hc15 := hr.c15
  have hc16 := hr.c16
  have hc17 := hr.c17
  have hc18 := hr.c18
  have hc19 := hr.c19
  have hc20 := hr.c20
  have hc21 := hr.c21
  have hc22 := hr.c22
  have hc23 := hr.c23
  have hborrow := borrow_run p E state x hr.x0 hr.x1 hr.x2 hr.x3 hr.x4
    hr.c6 hr.c12 hr.c13 hr.c14 hr.c15 hr.c16
  have hcall : p.blackBoxByte (.cons (.value byte) .nil) state =
      .value (.cons (.value byte) .nil, state1) := by
    rw [hblack]
    exact Agave.Ed25519.Encoding.Decompress.Execution.BlackBox.program_call byte state hwf
  have hbyte : E1.read (%205) = .value byte := by simp [E1, byte, d, borrowEnv, mlir_env]
  have hlow (i : Fin 4) : (tailLow x i).toNat < 2 ^ 52 := by
    rw [tailLow, mask52_toNat]
    exact Nat.mod_lt _ (by decide)
  have hadd : List.foldlM Instr.run E2 (((program.entry p).body.drop 227).take 23) state1 =
      .value (E3, state1) := by
    apply addback_run p E2 state1 (tailLow x) (d 4) byte hlow <;>
      simp [E2, E1, borrowEnv, tailLow, d, byte,
        hc6, hc17, hc18, hc19, hc20, hc21, hc22, mlir_env]
  have hstores : List.foldlM Instr.run E3 ((program.entry p).body.drop 250) state1 =
      .value (storesEnv E3 out, tailState state x out scratch) := by
    apply output_and_zeroize_run p E3 state1 out (tailWords x) scratch
    · exact houtReg
    · exact addbackEnv_output0 E2 d
    · exact addbackEnv_output1 E2 d
    · exact addbackEnv_output2 E2 d
    · exact addbackEnv_output3 E2 d
    · exact addbackEnv_output4 E2 d
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch0
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch1
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch2
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch3
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch4
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch5
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch6
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch7
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hscratch8
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hc1
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hc2
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hc3
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hc4
    · simp (disch := decide) only [E3, E2, E1, addbackEnv_read_early,
        borrowEnv_read_early, mlir_env]
      exact hc23
    · exact hout
    · exact hscratch
  have hresult := compose_tail hborrow
    (conditional_subtraction_black_box_call p E1 state state1 byte hbyte hcall)
    hadd hstores
  have henv : storesEnv E3 out = tailEnv E x out := rfl
  exact Eq.mp (congrArg (fun finalEnv =>
    (program.entry p).runBodyFrom E 208 state =
      .value (finalEnv, tailState state x out scratch)) henv) hresult

/-- The concrete tail's five output words satisfy exact subgroup subtraction. -/
theorem tailWords_value (x : Fin 5 → BitVec 52) :
    Agave.Ed25519.ScalarReduce32.Arithmetic.limbs
      (tailWords x 0).toNat (tailWords x 1).toNat (tailWords x 2).toNat
      (tailWords x 3).toNat (tailWords x 4).toNat =
      if rawValue x < Agave.Ed25519.Bridge.subgroupOrder then rawValue x
      else rawValue x - Agave.Ed25519.Bridge.subgroupOrder :=
  conditional_subtract_words x

end Agave.Ed25519.Verifier.Execution.ScalarMontgomeryMul
