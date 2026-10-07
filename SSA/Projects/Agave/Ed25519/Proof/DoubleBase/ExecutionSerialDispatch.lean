import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialBlocks
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialContracts
import SSA.Projects.Agave.Ed25519.Proof.NAF.BlockExecution

/-!
# Actual serial signed-digit dispatch

The B block is executed outright. The A block first invokes the single
projective-doubling primitive; its narrow write-frame contract preserves the
NAF array. Both compiler switches then exclude their unreachable default for
every byte, before the NAF magnitude proof discharges later table guards.
-/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

def serialDigitSign (digit : BitVec 8) : BitVec 8 :=
  if digit.toInt < 0 then 255#8 else if digit = 0#8 then 0#8 else 1#8

theorem serialDigitSign_cmp : ∀ digit : BitVec 8,
    Operation.cmp true (.value digit) (.value 0#8) = .value (serialDigitSign digit) := by
  decide +kernel

def serialDispatchBInput (E : ⟪serialKernel.Γ⟫) (digits : Pointer)
    (i : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %40 := .value digits,
    %131 := .value (BitVec.ofNat 64 i.val)]

def serialDispatchBResult (E : ⟪serialKernel.Γ⟫) (digits : Pointer)
    (i : Fin 256) (digit : BitVec 8) : ⟪serialKernel.Γ⟫ :=
  (serialDispatchBInput E digits i)[%144 := .value (digits.add (BitVec.ofNat 64 i.val)),
    %145 := .value digit, %146 := .value (serialDigitSign digit)]

theorem serial_dispatchB_block (E : ⟪serialKernel.Γ⟫) (digits : Pointer)
    (i : Fin 256) (digit : BitVec 8) (s : GlobalState)
    (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = digit)
    : serialKernel.bb26.run serialKernel.blockParams
      (serialDispatchBInput E digits i) s =
      if digit.toInt < 0 then .value ((serialDispatchBResult E digits i digit, .inr 27), s)
      else if digit = 0#8 then .value ((serialDispatchBResult E digits i digit, .inr 28), s)
      else .value ((serialDispatchBResult E digits i digit, .inr 29), s) := by
  have hscale := NAF.RIR.cursor_byte_offset i
  have hgep := hbuffer.gep i.val (by have := i.isLt; omega)
  have hfits := hbuffer.fits_at i.val 1 (by have := i.isLt; omega)
  have hload (env : ⟪serialKernel.Γ⟫) :
      Operation.load (%145 : Dst serialKernel.Γ (.bv 8))
        (.value (digits.add (BitVec.ofNat 64 i.val))) env s =
          .value (env[%145 := .value digit], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 8) = _
    rw [hread]
  have hcmp := serialDigitSign_cmp digit
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp only [serialDigitSign, hneg, hzero, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, serialKernel.bb26, serialDispatchBInput, serialDispatchBResult,
      serialDigitSign, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hscale, hgep, hload,
      hcmp, hneg, hzero, Exit.run, switchTarget, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem serial_dispatchB_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (digits : Pointer)
    (i : Fin 256) (digit : BitVec 8) (s : GlobalState)
    (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = digit)
    : (serialKernel p g).runFrom (serialDispatchBInput E digits i) 26 s =
      (serialKernel p g).runFrom (serialDispatchBResult E digits i digit)
        (if digit.toInt < 0 then 27 else if digit = 0#8 then 28 else 29) s := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 26 = serialKernel.bb26 from rfl,
    serial_dispatchB_block E digits i digit s hbuffer hread]
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp [hneg, hzero, PoisonOr.value_bind, Func.continue]

def serialDispatchAInput (E : ⟪serialKernel.Γ⟫) (digits : Pointer) (completed projective : Pointer)
    (i : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %37 := .value completed, %38 := .value projective, %41 := .value digits,
    %131 := .value (BitVec.ofNat 64 i.val)]

def serialDispatchAResult (E : ⟪serialKernel.Γ⟫) (digits : Pointer) (completed projective : Pointer)
    (i : Fin 256) (digit : BitVec 8) : ⟪serialKernel.Γ⟫ :=
  (serialDispatchAInput E digits completed projective i)[%132 := .value (digits.add (BitVec.ofNat 64 i.val)),
    %133 := .value digit, %134 := .value (serialDigitSign digit)]

theorem serial_dispatchA_block     (p : SerialCFG.Primitives)
(E : ⟪serialKernel.Γ⟫) (digits : Pointer) (completed projective : Pointer)
    (i : Fin 256) (digit : BitVec 8) (s final : GlobalState)
    (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = digit)
    (hcall : p.call1 (.cons (.value completed) (.cons (.value projective) .nil)) s =
      .value (.nil, final))
    (hframe : SerialContracts.WritesOnly completed 160 s final)
    (hseparate : digits.id ≠ completed.id)
    : (serialKernel.bb18 p).run serialKernel.blockParams
      (serialDispatchAInput E digits completed projective i) s =
      if digit.toInt < 0 then .value ((serialDispatchAResult E digits completed projective i digit, .inr 20), final)
      else if digit = 0#8 then .value ((serialDispatchAResult E digits completed projective i digit, .inr 26), final)
      else .value ((serialDispatchAResult E digits completed projective i digit, .inr 21), final) := by
  have hbufferFinal : Buffer final.mem digits 256 := hframe.smallRange hbuffer
  have hreadFinal : final.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = digit := by
    rw [hframe.readFrame _ _
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hseparate))]
    exact hread
  have hscale := NAF.RIR.cursor_byte_offset i
  have hgep := hbufferFinal.gep i.val (by have := i.isLt; omega)
  have hfits := hbufferFinal.fits_at i.val 1 (by have := i.isLt; omega)
  have hload (env : ⟪serialKernel.Γ⟫) :
      Operation.load (%133 : Dst serialKernel.Γ (.bv 8))
        (.value (digits.add (BitVec.ofNat 64 i.val))) env final =
          .value (env[%133 := .value digit], final) := by
    apply run_load hfits
    change PoisonOr.value (final.mem.readAt _ 8) = _
    rw [hreadFinal]
  have hcmp := serialDigitSign_cmp digit
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp only [serialDigitSign, hneg, hzero, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, serialKernel.bb18, serialDispatchAInput, serialDispatchAResult,
      serialDigitSign, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hscale, hgep, hload,
      hcall, hcmp, hneg, hzero, Exit.run, switchTarget, Jump.run,
      Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem serial_dispatchA_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (digits : Pointer) (completed projective : Pointer)
    (i : Fin 256) (digit : BitVec 8) (s final : GlobalState)
    (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 i.val)) 8 = digit)
    (hcall : p.call1 (.cons (.value completed) (.cons (.value projective) .nil)) s =
      .value (.nil, final))
    (hframe : SerialContracts.WritesOnly completed 160 s final)
    (hseparate : digits.id ≠ completed.id)
    : (serialKernel p g).runFrom (serialDispatchAInput E digits completed projective i) 18 s =
      (serialKernel p g).runFrom (serialDispatchAResult E digits completed projective i digit)
        (if digit.toInt < 0 then 20 else if digit = 0#8 then 26 else 21) final := by
  rw [Func.runFrom_eq,
    show (serialKernel p g).blocks 18 = serialKernel.bb18 p from rfl,
    serial_dispatchA_block p E digits completed projective i digit s final hbuffer hread hcall hframe hseparate]
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp [hneg, hzero, PoisonOr.value_bind, Func.continue]

end Agave.Ed25519.DoubleBase.RIR
