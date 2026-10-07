import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Control
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Execution

/-! The two memory-bearing scan blocks of the actual AVX2 CFG. The predecessor
counter, every inbounds index, each one-byte load and the zero fallback are
retained. A single live 256-byte buffer justifies every interior access. -/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2

open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem byte_zero_test : ∀ digit : BitVec 8,
    Operation.icmp .eq (.value digit) (.value 0#8) =
      .value (if digit = 0#8 then 1#1 else 0#1) ∧
    Operation.icmp .ne (.value digit) (.value 0#8) =
      .value (if digit ≠ 0#8 then 1#1 else 0#1) := by
  decide +kernel

theorem cursor_zero_test : ∀ pos : Fin 256,
    Operation.icmp .eq (.value (BitVec.ofNat 64 pos.val)) (.value 0#64) =
      .value (if pos.val = 0 then 1#1 else 0#1) := by
  decide +kernel

theorem flag_or (a b : Prop) [Decidable a] [Decidable b] :
    Operation.or false (.value (if a then 1#1 else 0#1))
      (.value (if b then 1#1 else 0#1)) =
        .value (if a ∨ b then 1#1 else 0#1) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, Operation.or]

def scanAInput (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %19 := .value (-1 : BitVec 64), %266 := .value digits,
    %411 := .value (BitVec.ofNat 64 (pos.val + 1))]

def scanAResult (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) : ⟪avx2Kernel.Γ⟫ :=
  (scanAInput E digits pos)[%412 := .value (BitVec.ofNat 64 pos.val),
    %413 := .value (digits.add (BitVec.ofNat 64 pos.val)), %414 := .value digit,
    %415 := .value (if digit = 0#8 then 1#1 else 0#1)]

/-- The scan decrements before its first load, so entry counter 256 reads byte
255. The allocation and cursor bound discharge the emitted GEP promise. -/
theorem scanA_block (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit) :
    avx2Kernel.bb16.run avx2Kernel.blockParams (scanAInput E digits pos) s =
      .value ((scanAResult E digits pos digit, .inr (if digit = 0#8 then 17 else 15)), s) := by
  have hdec := Execution.scan_decrement pos
  change Operation.add {nsw := true}
    (.value (BitVec.ofNat 64 (pos.val + 1))) (.value 18446744073709551615#64) =
      .value (BitVec.ofNat 64 pos.val) at hdec
  have hscale := NAF.RIR.cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%414 : Dst avx2Kernel.Γ (.bv 8))
        (.value (digits.add (BitVec.ofNat 64 pos.val))) env s =
          .value (env[%414 := .value digit], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 8) = _
    rw [hread]
  have hcmp := (byte_zero_test digit).1
  by_cases hzero : digit = 0#8 <;>
    simp only [hzero, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb16,
      scanAInput, scanAResult, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hdec, hscale, hgep,
      hload, hcmp, hzero, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

theorem scanA_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit) :
    (avx2Kernel p g).runFrom (scanAInput E digits pos) 16 s =
      (avx2Kernel p g).runFrom (scanAResult E digits pos digit)
        (if digit = 0#8 then 17 else 15) s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 16 = avx2Kernel.bb16 from rfl, scanA_block E digits pos digit s hbuffer hread]
  rfl

def scanBInput (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %4 := .value 0#64, %265 := .value digits,
    %412 := .value (BitVec.ofNat 64 pos.val)]

def scanBResult (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) : ⟪avx2Kernel.Γ⟫ :=
  (scanBInput E digits pos)[%416 := .value (digits.add (BitVec.ofNat 64 pos.val)), %417 := .value digit,
     %418 := .value (if digit ≠ 0#8 then 1#1 else 0#1),
     %419 := .value (if pos.val = 0 then 1#1 else 0#1),
     %420 := .value (if digit ≠ 0#8 ∨ pos.val = 0 then 1#1 else 0#1)]

/-- The B load terminates the scan even for two zero digits at index zero.
Thus the loop cannot take the decrementing backedge from zero. -/
theorem scanB_block (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit) :
    avx2Kernel.bb17.run avx2Kernel.blockParams (scanBInput E digits pos) s =
      if digit ≠ 0#8 ∨ pos.val = 0 then
        .value ((scanBResult E digits pos digit, .inr 15), s)
      else .value (((scanBResult E digits pos digit)[%411 := .value (BitVec.ofNat 64 pos.val)], .inr 16), s) := by
  have hscale := NAF.RIR.cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%417 : Dst avx2Kernel.Γ (.bv 8))
        (.value (digits.add (BitVec.ofNat 64 pos.val))) env s =
          .value (env[%417 := .value digit], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 8) = _
    rw [hread]
  have hdigit := (byte_zero_test digit).2
  have hpos := cursor_zero_test pos
  have hor := flag_or (digit ≠ 0#8) (pos.val = 0)
  by_cases hstop : digit ≠ 0#8 ∨ pos.val = 0 <;>
    simp only [hstop, ite_true, ite_false] at hor <;>
    simp only [ne_eq, ite_not, Fin.val_eq_zero_iff] at hor hstop <;>
    simp [BasicBlock.run, avx2Kernel.bb17,
      scanBInput, scanBResult, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hscale, hgep, hload,
      hdigit, hpos, hor, hstop, Exit.run, Jump.run, Regs.read_cons,
      Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem scanB_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit) :
    (avx2Kernel p g).runFrom (scanBInput E digits pos) 17 s =
      if digit ≠ 0#8 ∨ pos.val = 0 then
        (avx2Kernel p g).runFrom (scanBResult E digits pos digit) 15 s
      else (avx2Kernel p g).runFrom ((scanBResult E digits pos digit)[%411 := .value (BitVec.ofNat 64 pos.val)]) 16 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 17 = avx2Kernel.bb17 from rfl, scanB_block E digits pos digit s hbuffer hread]
  by_cases hstop : digit ≠ 0#8 ∨ pos.val = 0 <;>
    simp only [hstop, if_true, if_false, PoisonOr.value_bind, Func.continue]

end Agave.Ed25519.DoubleBase.ExecutionAvx2
