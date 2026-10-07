import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Control

/-! The actual basepoint digit load and signed switch. The switch default is
unreachable for every byte, independently of the stronger NAF magnitude
invariant used by the four subsequent index guards. -/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def digitSign (digit : BitVec 8) : BitVec 8 :=
  if digit.toInt < 0 then 255#8 else if digit = 0#8 then 0#8 else 1#8

theorem digitSign_cmp : ∀ digit : BitVec 8,
    Operation.cmp true (.value digit) (.value 0#8) = .value (digitSign digit) := by
  decide +kernel

def dispatchBInput (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %265 := .value digits,
    %426 := .value (BitVec.ofNat 64 pos.val)]

def dispatchBResult (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) : ⟪avx2Kernel.Γ⟫ :=
  (dispatchBInput E digits pos)[%703 := .value (digits.add (BitVec.ofNat 64 pos.val)),
    %704 := .value digit, %705 := .value (digitSign digit)]

def dispatchBZero (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) : ⟪avx2Kernel.Γ⟫ :=
  (dispatchBResult E digits pos digit)[%805 := E.read (%698), %806 := E.read (%699),
    %807 := E.read (%700), %808 := E.read (%701), %809 := E.read (%702)]

theorem dispatchB_block (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit) :
    avx2Kernel.bb26.run avx2Kernel.blockParams (dispatchBInput E digits pos) s =
      if digit.toInt < 0 then .value ((dispatchBResult E digits pos digit, .inr 27), s)
      else if digit = 0#8 then .value ((dispatchBZero E digits pos digit, .inr 30), s)
      else .value ((dispatchBResult E digits pos digit, .inr 31), s) := by
  have hscale := NAF.RIR.cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%704 : Dst avx2Kernel.Γ (.bv 8))
        (.value (digits.add (BitVec.ofNat 64 pos.val))) env s =
          .value (env[%704 := .value digit], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 8) = _
    rw [hread]
  have hcmp := digitSign_cmp digit
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp only [digitSign, hneg, hzero, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb26, dispatchBInput, dispatchBResult,
      dispatchBZero, digitSign, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hscale, hgep, hload,
      hcmp, hneg, hzero, Exit.run, switchTarget, Jump.run, Regs.read_cons,
      Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem dispatchB_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) (s : GlobalState) (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit) :
    (avx2Kernel p g).runFrom (dispatchBInput E digits pos) 26 s =
      if digit.toInt < 0 then
        (avx2Kernel p g).runFrom (dispatchBResult E digits pos digit) 27 s
      else if digit = 0#8 then
        (avx2Kernel p g).runFrom (dispatchBZero E digits pos digit) 30 s
      else (avx2Kernel p g).runFrom (dispatchBResult E digits pos digit) 31 s := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 26 = avx2Kernel.bb26 from rfl,
    dispatchB_block E digits pos digit s hbuffer hread]
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp [hneg, hzero, PoisonOr.value_bind, Func.continue]

end Agave.Ed25519.DoubleBase.ExecutionAvx2
