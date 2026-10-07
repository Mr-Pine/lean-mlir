import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialNAF
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Execution

/-!
# The original serial scan and ladder backedge

The live cursor bounds justify the flagged decrement and the byte load. These
are equations on the imported CFG, with no successful-run premise. In
particular, the zero-index guard is executed before the scan can decrement
again. The full descending-scan induction is not asserted here.
-/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

theorem byte_zero_compare : ∀ digit : BitVec 8,
    Operation.icmp .eq (.value digit) (.value 0#8) =
      .value (if digit = 0#8 then 1#1 else 0#1) ∧
    Operation.icmp .ne (.value digit) (.value 0#8) =
      .value (if digit ≠ 0#8 then 1#1 else 0#1) := by
  decide +kernel

theorem scan_zero_compare : ∀ i : Fin 256,
    Operation.icmp .eq (.value (BitVec.ofNat 64 i.val)) (.value 0#64) =
      .value (if i.val = 0 then 1#1 else 0#1) := by
  decide +kernel

/-- Exact one-bit OR used by the scan's mandatory zero-index fallback. -/
theorem scan_flag_or (a b : Prop) [Decidable a] [Decidable b] :
    Operation.or false (.value (if a then 1#1 else 0#1))
      (.value (if b then 1#1 else 0#1)) =
        .value (if a ∨ b then 1#1 else 0#1) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, Operation.or]

def scanInput (E : ⟪serialKernel.Γ⟫) (a : Pointer) (i : Fin 256) :
    ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %19 := .value (-1 : BitVec 64), %41 := .value a,
    %102 := .value (BitVec.ofNat 64 (i.val + 1))]

def scanResult (E : ⟪serialKernel.Γ⟫) (a : Pointer) (i : Fin 256)
    (digit : BitVec 8) : ⟪serialKernel.Γ⟫ :=
  (scanInput E a i)[%103 := .value (BitVec.ofNat 64 i.val),
    %104 := .value (a.add (BitVec.ofNat 64 i.val)), %105 := .value digit,
    %106 := .value (if digit = 0#8 then 1#1 else 0#1)]

/-- Block 15 decrements once, reads the A digit, and chooses the original edge.
The output byte is an actual memory read, not an assumed NAF digit. -/
theorem serial_scan_a_block (E : ⟪serialKernel.Γ⟫) (a : Pointer) (i : Fin 256)
    (s : GlobalState) (ha : Buffer s.mem a 256) :
    serialKernel.bb15.run serialKernel.blockParams (scanInput E a i) s =
      let digit := s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8
      .value ((scanResult E a i digit, .inr (if digit = 0#8 then 17 else 16)), s) := by
  have hparams17 : serialKernel.blockParams 17 = .nil := rfl
  have hparams16 : serialKernel.blockParams 16 = .nil := rfl
  have hdec := Execution.scan_decrement i
  change Operation.add {nsw := true} (.value (BitVec.ofNat 64 (i.val + 1)))
    (.value 18446744073709551615#64) = .value (BitVec.ofNat 64 i.val) at hdec
  have hscale := NAF.RIR.cursor_byte_offset i
  have hgep := ha.gep i.val (by have := i.isLt; omega)
  have hfits := ha.fits_at i.val 1 (by have := i.isLt; omega)
  have hload (env : ⟪serialKernel.Γ⟫) := run_load (env := env) (dst := %105) hfits
    (show Ty.unflatten (.bv 8) (s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8) =
      .value (s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8) from rfl)
  have hcmp := (byte_zero_compare (s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8)).1
  by_cases hz : s.mem.readAt (a.add (BitVec.ofNat 64 i.val)) 8 = 0#8 <;>
    simp only [hz, ite_true, ite_false] at hcmp <;>
    simp [hparams17, hparams16, BasicBlock.run, serialKernel.bb15,
      scanInput, scanResult, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hdec, hscale, hgep, hload,
      hcmp, hz, Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def scanBInput (E : ⟪serialKernel.Γ⟫) (b : Pointer) (i : Fin 256) :
    ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %4 := .value 0#64, %40 := .value b,
    %103 := .value (BitVec.ofNat 64 i.val)]

def scanBResult (E : ⟪serialKernel.Γ⟫) (b : Pointer) (i : Fin 256)
    (digit : BitVec 8) : ⟪serialKernel.Γ⟫ :=
  (scanBInput E b i)[%126 := .value (b.add (BitVec.ofNat 64 i.val)),
    %127 := .value digit, %128 := .value (if digit ≠ 0#8 then 1#1 else 0#1),
    %129 := .value (if i.val = 0 then 1#1 else 0#1),
    %130 := .value (if digit ≠ 0#8 ∨ i.val = 0 then 1#1 else 0#1)]

/-- Block 17 loads B only after A was zero. At cursor zero its backedge is
impossible for every byte, including an all-zero scalar pair. -/
theorem serial_scan_b_block (E : ⟪serialKernel.Γ⟫) (b : Pointer) (i : Fin 256)
    (s : GlobalState) (hb : Buffer s.mem b 256) :
    serialKernel.bb17.run serialKernel.blockParams (scanBInput E b i) s =
      let digit := s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8
      if digit ≠ 0#8 ∨ i.val = 0 then
        .value ((scanBResult E b i digit, .inr 16), s)
      else .value (((scanBResult E b i digit)[%102 := .value (BitVec.ofNat 64 i.val)], .inr 15), s) := by
  have hparams16 : serialKernel.blockParams 16 = .nil := rfl
  have hparams15 : serialKernel.blockParams 15 = .cons (%102) .nil := rfl
  have hscale := NAF.RIR.cursor_byte_offset i
  have hgep := hb.gep i.val (by have := i.isLt; omega)
  have hfits := hb.fits_at i.val 1 (by have := i.isLt; omega)
  have hload (env : ⟪serialKernel.Γ⟫) := run_load (env := env) (dst := %127) hfits
    (show Ty.unflatten (.bv 8) (s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8) =
      .value (s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8) from rfl)
  have hcmp := (byte_zero_compare (s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8)).2
  have hzero := scan_zero_compare i
  have hor := scan_flag_or
    (s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 ≠ 0#8) (i.val = 0)
  by_cases hstop : s.mem.readAt (b.add (BitVec.ofNat 64 i.val)) 8 ≠ 0#8 ∨ i.val = 0 <;>
    simp only [hstop, ite_true, ite_false] at hor <;>
    simp [hparams16, hparams15, BasicBlock.run, serialKernel.bb17,
      scanBInput, scanBResult, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hscale, hgep, hload,
      hcmp, hzero, hor, hstop, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil] <;>
    simp_all [Operation.or]

def backedgeInput (E : ⟪serialKernel.Γ⟫) (i : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%19 := .value (-1 : BitVec 64), %131 := .value (BitVec.ofNat 64 (i.val + 1))]

/-- The inclusive ladder decrements only on its non-final path. -/
theorem serial_ladder_backedge_block (E : ⟪serialKernel.Γ⟫)
    (i : Fin 256) (s : GlobalState) :
    serialKernel.bb35.run serialKernel.blockParams (backedgeInput E i) s =
      .value ((((backedgeInput E i)[%160 := .value (BitVec.ofNat 64 i.val),
         %131 := .value (BitVec.ofNat 64 i.val)]), .inr 18), s) := by
  have hparams18 : serialKernel.blockParams 18 = .cons (%131) .nil := rfl
  have hdec := Execution.scan_decrement i
  change Operation.add {nsw := true} (.value (BitVec.ofNat 64 (i.val + 1)))
    (.value 18446744073709551615#64) = .value (BitVec.ofNat 64 i.val) at hdec
  simp [hparams18, BasicBlock.run, serialKernel.bb35,
    backedgeInput, List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hdec,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil]

theorem serial_ladder_backedge (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (i : Fin 256) (s : GlobalState) :
    (serialKernel p g).runFrom (backedgeInput E i) 35 s =
      (serialKernel p g).runFrom ((backedgeInput E i)[%160 := .value (BitVec.ofNat 64 i.val),
         %131 := .value (BitVec.ofNat 64 i.val)]) 18 s := by
  have hblock : (serialKernel p g).blocks 35 = serialKernel.bb35 := rfl
  rw [Func.runFrom_eq, hblock, serial_ladder_backedge_block]
  rfl

end Agave.Ed25519.DoubleBase.RIR
