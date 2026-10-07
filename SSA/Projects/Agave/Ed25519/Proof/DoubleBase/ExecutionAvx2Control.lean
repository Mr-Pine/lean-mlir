import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Avx2Program
import SSA.Projects.Agave.Ed25519.Proof.NAF.BlockExecution

/-!
# Control blocks of the imported AVX2 double-base kernel

These equations execute blocks of `RIR.avx2Kernel` itself. In particular the
two even-digit paths retain their unsigned/signed no-wrap flags and distinguish
the final 255-to-256 exit from the loop backedge. These are local block/run
equations, not a whole-function refinement theorem.

The imported CFG has 35 blocks. Blocks 0--14 initialize and emit both NAFs;
16--17 scan the digits, 15 constructs the dynamic table, 18 doubles, 20--25
handle the first signed digit, 26--33 handle the basepoint digit and backedge,
and 34 writes the ordinary point representation. Block 19 is unreachable;
21, 24, 28 and 32 are panic successors.
-/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR
open RIR

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

-- Closed projections avoid unfolding the entire dependent finite table.
@[simp] theorem kernel_params0 : avx2Kernel.blockParams 0 = Dsts.nil := rfl
@[simp] theorem kernel_params1 : avx2Kernel.blockParams 1 = .cons (%268) (.cons (%269) (.nil)) := rfl
@[simp] theorem kernel_params2 : avx2Kernel.blockParams 2 = .cons (%270) (.nil) := rfl
@[simp] theorem kernel_params3 : avx2Kernel.blockParams 3 = Dsts.nil := rfl
@[simp] theorem kernel_params4 : avx2Kernel.blockParams 4 = .cons (%283) (.nil) := rfl
@[simp] theorem kernel_params5 : avx2Kernel.blockParams 5 = Dsts.nil := rfl
@[simp] theorem kernel_params6 : avx2Kernel.blockParams 6 = Dsts.nil := rfl
@[simp] theorem kernel_params7 : avx2Kernel.blockParams 7 = Dsts.nil := rfl
@[simp] theorem kernel_params8 : avx2Kernel.blockParams 8 = .cons (%299) (.cons (%300) (.nil)) := rfl
@[simp] theorem kernel_params9 : avx2Kernel.blockParams 9 = .cons (%301) (.nil) := rfl
@[simp] theorem kernel_params10 : avx2Kernel.blockParams 10 = Dsts.nil := rfl
@[simp] theorem kernel_params11 : avx2Kernel.blockParams 11 = .cons (%314) (.nil) := rfl
@[simp] theorem kernel_params12 : avx2Kernel.blockParams 12 = Dsts.nil := rfl
@[simp] theorem kernel_params13 : avx2Kernel.blockParams 13 = Dsts.nil := rfl
@[simp] theorem kernel_params14 : avx2Kernel.blockParams 14 = Dsts.nil := rfl
@[simp] theorem kernel_params15 : avx2Kernel.blockParams 15 = Dsts.nil := rfl
@[simp] theorem kernel_params16 : avx2Kernel.blockParams 16 = .cons (%411) (.nil) := rfl
@[simp] theorem kernel_params17 : avx2Kernel.blockParams 17 = Dsts.nil := rfl
@[simp] theorem kernel_params18 : avx2Kernel.blockParams 18 = .cons (%421) (.cons (%422) (.cons (%423) (.cons (%424) (.cons (%425) (.cons (%426) (.nil)))))) := rfl
@[simp] theorem kernel_params19 : avx2Kernel.blockParams 19 = Dsts.nil := rfl
@[simp] theorem kernel_params20 : avx2Kernel.blockParams 20 = Dsts.nil := rfl
@[simp] theorem kernel_params21 : avx2Kernel.blockParams 21 = Dsts.nil := rfl
@[simp] theorem kernel_params22 : avx2Kernel.blockParams 22 = Dsts.nil := rfl
@[simp] theorem kernel_params23 : avx2Kernel.blockParams 23 = Dsts.nil := rfl
@[simp] theorem kernel_params24 : avx2Kernel.blockParams 24 = Dsts.nil := rfl
@[simp] theorem kernel_params25 : avx2Kernel.blockParams 25 = Dsts.nil := rfl
@[simp] theorem kernel_params26 : avx2Kernel.blockParams 26 = .cons (%698) (.cons (%699) (.cons (%700) (.cons (%701) (.cons (%702) (.nil))))) := rfl
@[simp] theorem kernel_params27 : avx2Kernel.blockParams 27 = Dsts.nil := rfl
@[simp] theorem kernel_params28 : avx2Kernel.blockParams 28 = Dsts.nil := rfl
@[simp] theorem kernel_params29 : avx2Kernel.blockParams 29 = Dsts.nil := rfl
@[simp] theorem kernel_params30 : avx2Kernel.blockParams 30 = .cons (%805) (.cons (%806) (.cons (%807) (.cons (%808) (.cons (%809) (.nil))))) := rfl
@[simp] theorem kernel_params31 : avx2Kernel.blockParams 31 = Dsts.nil := rfl
@[simp] theorem kernel_params32 : avx2Kernel.blockParams 32 = Dsts.nil := rfl
@[simp] theorem kernel_params33 : avx2Kernel.blockParams 33 = Dsts.nil := rfl
@[simp] theorem kernel_params34 : avx2Kernel.blockParams 34 = Dsts.nil := rfl

/-- The width-five carry-entry block forwards the cursor, preserving carry. -/
theorem carry5_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel p g).runFrom E 1 s =
      (avx2Kernel p g).runFrom (E[%270 := E.read (%268)]) 2 s := by
  rw [Func.runFrom_eq]
  rfl

/-- The width-eight copy of the carry-entry block. -/
theorem carry8_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel p g).runFrom E 8 s =
      (avx2Kernel p g).runFrom (E[%301 := E.read (%299)]) 9 s := by
  rw [Func.runFrom_eq]
  rfl

def evenInput5 (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  E[%2 := .value 256#64, %10 := .value 1#64,
    %270 := .value (BitVec.ofNat 64 pos.val)]

def evenResult5 (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  (evenInput5 E pos)[%288 := .value (BitVec.ofNat 64 (pos.val + 1)),
    %289 := .value (if pos.val + 1 = 256 then 1#1 else 0#1)]

theorem even5_block (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    avx2Kernel.bb5.run avx2Kernel.blockParams (evenInput5 E pos) s =
      if pos.val + 1 = 256 then
        .value ((evenResult5 E pos, .inr 7), s)
      else .value (((evenResult5 E pos)[%270 := .value (BitVec.ofNat 64 (pos.val + 1))], .inr 2), s) := by
  obtain ⟨hadd, hcmp⟩ := NAF.RIR.cursor_one pos
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb5,
      evenInput5, evenResult5, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, hadd, hcmp, hend, Exit.run, Jump.run, Regs.read_cons,
      Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem even5_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    (avx2Kernel p g).runFrom (evenInput5 E pos) 5 s =
      if pos.val + 1 = 256 then
        (avx2Kernel p g).runFrom (evenResult5 E pos) 7 s
      else (avx2Kernel p g).runFrom ((evenResult5 E pos)[%270 := .value (BitVec.ofNat 64 (pos.val + 1))]) 2 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 5 = avx2Kernel.bb5 from rfl, even5_block]
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, if_true, if_false, PoisonOr.value_bind, Func.continue]

def evenInput8 (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  E[%2 := .value 256#64, %10 := .value 1#64,
    %301 := .value (BitVec.ofNat 64 pos.val)]

def evenResult8 (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  (evenInput8 E pos)[%319 := .value (BitVec.ofNat 64 (pos.val + 1)),
    %320 := .value (if pos.val + 1 = 256 then 1#1 else 0#1)]

theorem even8_block (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    avx2Kernel.bb12.run avx2Kernel.blockParams (evenInput8 E pos) s =
      if pos.val + 1 = 256 then
        .value ((evenResult8 E pos, .inr 14), s)
      else .value (((evenResult8 E pos)[%301 := .value (BitVec.ofNat 64 (pos.val + 1))], .inr 9), s) := by
  obtain ⟨hadd, hcmp⟩ := NAF.RIR.cursor_one pos
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb12,
      evenInput8, evenResult8, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, hadd, hcmp, hend, Exit.run, Jump.run, Regs.read_cons,
      Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem even8_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    (avx2Kernel p g).runFrom (evenInput8 E pos) 12 s =
      if pos.val + 1 = 256 then
        (avx2Kernel p g).runFrom (evenResult8 E pos) 14 s
      else (avx2Kernel p g).runFrom ((evenResult8 E pos)[%301 := .value (BitVec.ofNat 64 (pos.val + 1))]) 9 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 12 = avx2Kernel.bb12 from rfl, even8_block]
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, if_true, if_false, PoisonOr.value_bind, Func.continue]

def windowInput5 (E : ⟪avx2Kernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%4 := .value 0#64, %9 := .value 31#64, %10 := .value 1#64,
    %269 := .value (BitVec.ofNat 64 carry.val), %283 := .value raw]

def windowResult5 (E : ⟪avx2Kernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) :
    ⟪avx2Kernel.Γ⟫ :=
  (windowInput5 E raw carry)[%284 := .value (BitVec.ofNat 64 (NAF.RIR.mask5 raw).val),
     %285 := .value (BitVec.ofNat 64 (NAF.RIR.sum5 (NAF.RIR.mask5 raw) carry).val),
     %286 := .value (BitVec.ofNat 64 ((NAF.RIR.sum5 (NAF.RIR.mask5 raw) carry).val % 2)),
     %287 := .value (if (NAF.RIR.sum5 (NAF.RIR.mask5 raw) carry).val % 2 = 0
       then 1#1 else 0#1)]

/-- The four arithmetic instructions and exact parity successor, with every
flag proved from the masked window and one-bit carry. -/
theorem window5_block (E : ⟪avx2Kernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2)
    (s : GlobalState) :
    avx2Kernel.bb4.run avx2Kernel.blockParams (windowInput5 E raw carry) s =
      .value ((windowResult5 E raw carry,
        .inr (if (NAF.RIR.sum5 (NAF.RIR.mask5 raw) carry).val % 2 = 0
          then 5 else 6)), s) := by
  have hmask := NAF.RIR.mask5_instruction raw
  obtain ⟨hadd, hlow, hcmp⟩ := NAF.RIR.window_arithmetic5 (NAF.RIR.mask5 raw) carry
  by_cases heven : (NAF.RIR.sum5 (NAF.RIR.mask5 raw) carry).val % 2 = 0 <;>
    simp only [heven, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb4,
      windowInput5, windowResult5, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, hmask, hadd, hlow, hcmp, heven, Exit.run, Jump.run,
      Regs.read_nil, Env.writeMany_nil]

def windowInput8 (E : ⟪avx2Kernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%4 := .value 0#64, %16 := .value 255#64, %10 := .value 1#64,
    %300 := .value (BitVec.ofNat 64 carry.val), %314 := .value raw]

def windowResult8 (E : ⟪avx2Kernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) :
    ⟪avx2Kernel.Γ⟫ :=
  (windowInput8 E raw carry)[%315 := .value (BitVec.ofNat 64 (NAF.RIR.mask8 raw).val),
     %316 := .value (BitVec.ofNat 64 (NAF.RIR.sum8 (NAF.RIR.mask8 raw) carry).val),
     %317 := .value (BitVec.ofNat 64 ((NAF.RIR.sum8 (NAF.RIR.mask8 raw) carry).val % 2)),
     %318 := .value (if (NAF.RIR.sum8 (NAF.RIR.mask8 raw) carry).val % 2 = 0
       then 1#1 else 0#1)]

theorem window8_block (E : ⟪avx2Kernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2)
    (s : GlobalState) :
    avx2Kernel.bb11.run avx2Kernel.blockParams (windowInput8 E raw carry) s =
      .value ((windowResult8 E raw carry,
        .inr (if (NAF.RIR.sum8 (NAF.RIR.mask8 raw) carry).val % 2 = 0
          then 12 else 13)), s) := by
  have hmask := NAF.RIR.mask8_instruction raw
  obtain ⟨hadd, hlow, hcmp⟩ := NAF.RIR.window_arithmetic8 (NAF.RIR.mask8 raw) carry
  by_cases heven : (NAF.RIR.sum8 (NAF.RIR.mask8 raw) carry).val % 2 = 0 <;>
    simp only [heven, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb11,
      windowInput8, windowResult8, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind,
      mlir_env, hmask, hadd, hlow, hcmp, heven, Exit.run, Jump.run,
      Regs.read_nil, Env.writeMany_nil]

theorem ladder_cursor : ∀ pos : Fin 256,
    Operation.icmp .eq (.value (BitVec.ofNat 64 pos.val)) (.value 0#64) =
      .value (if pos.val = 0 then 1#1 else 0#1) ∧
    Operation.add {nsw := true} (.value (BitVec.ofNat 64 pos.val)) (.value 18446744073709551615#64) =
      .value (BitVec.ofInt 64 ((pos.val : Int) - 1)) := by
  decide +kernel

def backedgeInput (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  E[%4 := .value 0#64, %19 := .value (-1 : BitVec 64),
    %426 := .value (BitVec.ofNat 64 pos.val)]

def backedgeResult (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  (backedgeInput E pos)[%810 := .value (if pos.val = 0 then 1#1 else 0#1),
     %811 := .value (BitVec.ofInt 64 ((pos.val : Int) - 1))]

def backedgeNext (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  (backedgeResult E pos)[%421 := E.read (%805), %422 := E.read (%806), %423 := E.read (%807),
     %424 := E.read (%808), %425 := E.read (%809),
     %426 := .value (BitVec.ofInt 64 ((pos.val : Int) - 1))]

/-- The original ladder executes digit zero, then exits. Its final signed
decrement to -1 is defined but is not used on another loop iteration. -/
theorem backedge_block (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    avx2Kernel.bb30.run avx2Kernel.blockParams (backedgeInput E pos) s =
      if pos.val = 0 then .value ((backedgeResult E pos, .inr 34), s)
      else .value ((backedgeNext E pos, .inr 18), s) := by
  obtain ⟨hcmp, hdec⟩ := ladder_cursor pos
  by_cases hzero : pos.val = 0 <;>
    simp only [hzero, ite_true, ite_false] at hcmp hdec <;>
    simp [BasicBlock.run, avx2Kernel.bb30,
      backedgeInput, backedgeResult, backedgeNext, List.foldlM_cons,
      List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hcmp, hdec, hzero,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil]

theorem backedge_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    (avx2Kernel p g).runFrom (backedgeInput E pos) 30 s =
      if pos.val = 0 then (avx2Kernel p g).runFrom (backedgeResult E pos) 34 s
      else (avx2Kernel p g).runFrom (backedgeNext E pos) 18 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 30 = avx2Kernel.bb30 from rfl, backedge_block]
  by_cases hzero : pos.val = 0 <;>
    simp only [hzero, if_true, if_false, PoisonOr.value_bind, Func.continue]

/-- Finishing the second NAF starts the descending scan at cursor 256,
using the entry block's constant register. The lifetime marker is a no-op. -/
theorem scan_entry_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel p g).runFrom E 14 s =
      (avx2Kernel p g).runFrom (E[%411 := E.read (%2)]) 16 s := by
  rw [Func.runFrom_eq]
  rfl

/-- Reaching the switch default is UB regardless of every helper contract. -/
theorem unreachable_block (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    avx2Kernel.bb19.run avx2Kernel.blockParams E s = .poison := by
  rfl

theorem unreachable_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) :
    (avx2Kernel p g).runFrom E 19 s = .poison := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 19 = avx2Kernel.bb19 from rfl, unreachable_block]
  rfl

end Agave.Ed25519.DoubleBase.ExecutionAvx2
