import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.SerialProgram
import SSA.Projects.Agave.Ed25519.Proof.NAF.BlockExecution

/-!
# Actual serial-kernel NAF blocks

These equations execute the original serial double-base CFG, with its original
registers and successors. The arithmetic lemmas are shared with the standalone
NAF emitter; the left-hand sides are the imported `serialKernel` blocks.
They do not assume successful execution, a digit-array relation, or a whole
function refinement. The allocation premise on a store is a live, small
256-byte range. The loop induction and initialization are separate obligations.
-/
namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)
open NAF.RIR

set_option maxRecDepth 10000

def evenInput5 (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%2 := .value 256#64, %10 := .value 1#64, %45 := .value (BitVec.ofNat 64 pos.val)]

def evenResult5 (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  (evenInput5 E pos)[%63 := .value (BitVec.ofNat 64 (pos.val + 1)),
    %64 := .value (if pos.val + 1 = 256 then 1#1 else 0#1)]

/-- Exact execution of the width-five even block, including the final 255→256
exit and the otherwise taken backedge. Memory and carry remain unchanged. -/
theorem serial5_even_block (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    serialKernel.bb5.run serialKernel.blockParams (evenInput5 E pos) s =
      if pos.val + 1 = 256 then
        .value ((evenResult5 E pos, .inr 7), s)
      else .value (((evenResult5 E pos)[%45 := .value (BitVec.ofNat 64 (pos.val + 1))],
        .inr 2), s) := by
  obtain ⟨hadd, hcmp⟩ := cursor_one pos
  have hparams7 : serialKernel.blockParams 7 = .nil := rfl
  have hparams2 : serialKernel.blockParams 2 = .cons (%45) .nil := rfl
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false] at hcmp <;>
    simp [hparams7, hparams2, BasicBlock.run, serialKernel.bb5, evenInput5, evenResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hadd, hcmp, hend,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def evenInput8 (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%2 := .value 256#64, %10 := .value 1#64, %76 := .value (BitVec.ofNat 64 pos.val)]

def evenResult8 (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  (evenInput8 E pos)[%94 := .value (BitVec.ofNat 64 (pos.val + 1)),
    %95 := .value (if pos.val + 1 = 256 then 1#1 else 0#1)]

theorem serial8_even_block (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    serialKernel.bb12.run serialKernel.blockParams (evenInput8 E pos) s =
      if pos.val + 1 = 256 then
        .value ((evenResult8 E pos, .inr 14), s)
      else .value (((evenResult8 E pos)[%76 := .value (BitVec.ofNat 64 (pos.val + 1))],
        .inr 9), s) := by
  obtain ⟨hadd, hcmp⟩ := cursor_one pos
  have hparams14 : serialKernel.blockParams 14 = .nil := rfl
  have hparams9 : serialKernel.blockParams 9 = .cons (%76) .nil := rfl
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false] at hcmp <;>
    simp [hparams14, hparams9, BasicBlock.run, serialKernel.bb12, evenInput8, evenResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hadd, hcmp, hend,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def windowInput5 (E : ⟪serialKernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪serialKernel.Γ⟫ :=
  E[%4 := .value 0#64, %9 := .value 31#64, %10 := .value 1#64,
    %44 := .value (BitVec.ofNat 64 carry.val), %58 := .value raw]

def windowResult5 (E : ⟪serialKernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪serialKernel.Γ⟫ :=
  (windowInput5 E raw carry)[%59 := .value (BitVec.ofNat 64 (mask5 raw).val),
    %60 := .value (BitVec.ofNat 64 (sum5 (mask5 raw) carry).val),
    %61 := .value (BitVec.ofNat 64 ((sum5 (mask5 raw) carry).val % 2)),
    %62 := .value (if (sum5 (mask5 raw) carry).val % 2 = 0 then 1#1 else 0#1)]

/-- The imported mask/carry/parity block is total for every raw word and the
one-bit carry invariant. Both overflow promises and its exact edge are proved. -/
theorem serial5_window_block (E : ⟪serialKernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2)
    (s : GlobalState) :
    serialKernel.bb4.run serialKernel.blockParams (windowInput5 E raw carry) s =
      .value ((windowResult5 E raw carry,
        .inr (if (sum5 (mask5 raw) carry).val % 2 = 0 then 5 else 6)), s) := by
  have hmask := mask5_instruction raw
  obtain ⟨hadd, hlow, hcmp⟩ := window_arithmetic5 (mask5 raw) carry
  have hparams5 : serialKernel.blockParams 5 = .nil := rfl
  have hparams6 : serialKernel.blockParams 6 = .nil := rfl
  by_cases heven : (sum5 (mask5 raw) carry).val % 2 = 0 <;>
    simp only [heven, ite_true, ite_false] at hcmp <;>
    simp [hparams5, hparams6, BasicBlock.run, serialKernel.bb4, windowInput5, windowResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hmask, hadd, hlow, hcmp, heven,
      Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def windowInput8 (E : ⟪serialKernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪serialKernel.Γ⟫ :=
  E[%4 := .value 0#64, %16 := .value 255#64, %10 := .value 1#64,
    %75 := .value (BitVec.ofNat 64 carry.val), %89 := .value raw]

def windowResult8 (E : ⟪serialKernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪serialKernel.Γ⟫ :=
  (windowInput8 E raw carry)[%90 := .value (BitVec.ofNat 64 (mask8 raw).val),
    %91 := .value (BitVec.ofNat 64 (sum8 (mask8 raw) carry).val),
    %92 := .value (BitVec.ofNat 64 ((sum8 (mask8 raw) carry).val % 2)),
    %93 := .value (if (sum8 (mask8 raw) carry).val % 2 = 0 then 1#1 else 0#1)]

theorem serial8_window_block (E : ⟪serialKernel.Γ⟫) (raw : BitVec 64) (carry : Fin 2)
    (s : GlobalState) :
    serialKernel.bb11.run serialKernel.blockParams (windowInput8 E raw carry) s =
      .value ((windowResult8 E raw carry,
        .inr (if (sum8 (mask8 raw) carry).val % 2 = 0 then 12 else 13)), s) := by
  have hmask := mask8_instruction raw
  obtain ⟨hadd, hlow, hcmp⟩ := window_arithmetic8 (mask8 raw) carry
  have hparams12 : serialKernel.blockParams 12 = .nil := rfl
  have hparams13 : serialKernel.blockParams 13 = .nil := rfl
  by_cases heven : (sum8 (mask8 raw) carry).val % 2 = 0 <;>
    simp only [heven, ite_true, ite_false] at hcmp <;>
    simp [hparams12, hparams13, BasicBlock.run, serialKernel.bb11, windowInput8, windowResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hmask, hadd, hlow, hcmp, heven,
      Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def storeInput5 (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) (window : Fin 33) : ⟪serialKernel.Γ⟫ :=
  E[%1 := .value 0#8, %11 := .value 15#64, %12 := .value (-32 : BitVec 8),
    %13 := .value 5#64, %14 := .value 251#64, %45 := .value (BitVec.ofNat 64 pos.val),
    %60 := .value (BitVec.ofNat 64 window.val)]

def storeResult5 (E : ⟪serialKernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 33) :
    ⟪serialKernel.Γ⟫ :=
  (storeInput5 E pos window)[%65 := .value (high5 window),
    %66 := .value (BitVec.ofNat 8 window.val), %67 := .value (bias5 window),
    %68 := .value (byte5 window), %69 := .value (carry5 window),
    %70 := .value (out.add (BitVec.ofNat 64 pos.val)),
    %71 := .value (BitVec.ofNat 64 (pos.val + 5)),
    %72 := .value (if pos.val < 251 then 1#1 else 0#1)]

/-- The original width-five store block writes exactly one byte and returns
the concrete carry/cursor edge. The GEP and store are justified by the outer
256-byte allocation, with no index-safety premise on the digit. -/
theorem serial5_store_block (E : ⟪serialKernel.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 33) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%41) = .value out) :
    serialKernel.bb6.run serialKernel.blockParams (storeInput5 E pos window) s =
      if pos.val < 251 then
        .value (((storeResult5 E out pos window)[%43 := .value (BitVec.ofNat 64 (pos.val + 5)), %44 := .value (carry5 window)],
          .inr 1), {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)})
      else .value ((storeResult5 E out pos window, .inr 7),
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}) := by
  obtain ⟨hhigh, htrunc, hselect, hdigit, hcarry⟩ := store_arithmetic5 window
  change Operation.select (τ := .bv 8) (.value (high5 window)) (.value 224#8) (.value 0#8) =
    .value (bias5 window) at hselect
  obtain ⟨hadd, hcmp⟩ := cursor_five pos
  have hscale := cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hstore (env : ⟪serialKernel.Γ⟫) := run_store (env := env) hfits
    (show Ty.flatten (.bv 8) (.value (byte5 window)) = .value (byte5 window) from rfl)
  have hparams1 : serialKernel.blockParams 1 = .cons (%43) (.cons (%44) .nil) := rfl
  have hparams7 : serialKernel.blockParams 7 = .nil := rfl
  by_cases hnext : pos.val < 251 <;>
    simp [hparams1, hparams7, BasicBlock.run, serialKernel.bb6, storeInput5, storeResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, UnOp.compute,
      TernOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hout, hhigh, htrunc,
      hselect, hdigit, hcarry, hscale, hgep, hstore, hadd, hcmp, hnext,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def storeInput8 (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) (window : Fin 257) : ⟪serialKernel.Γ⟫ :=
  E[%8 := .value 8#64, %17 := .value 127#64, %18 := .value 248#64,
    %76 := .value (BitVec.ofNat 64 pos.val), %91 := .value (BitVec.ofNat 64 window.val)]

def storeResult8 (E : ⟪serialKernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 257) :
    ⟪serialKernel.Γ⟫ :=
  (storeInput8 E pos window)[%96 := .value (high8 window), %97 := .value (byte8 window),
    %98 := .value (carry8 window), %99 := .value (out.add (BitVec.ofNat 64 pos.val)),
    %100 := .value (BitVec.ofNat 64 (pos.val + 8)),
    %101 := .value (if pos.val < 248 then 1#1 else 0#1)]

theorem serial8_store_block (E : ⟪serialKernel.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 257) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%40) = .value out) :
    serialKernel.bb13.run serialKernel.blockParams (storeInput8 E pos window) s =
      if pos.val < 248 then
        .value (((storeResult8 E out pos window)[%74 := .value (BitVec.ofNat 64 (pos.val + 8)), %75 := .value (carry8 window)],
          .inr 8), {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)})
      else .value ((storeResult8 E out pos window, .inr 14),
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}) := by
  obtain ⟨hhigh, hdigit, hcarry⟩ := store_arithmetic8 window
  obtain ⟨hadd, hcmp⟩ := cursor_eight pos
  have hscale := cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hstore (env : ⟪serialKernel.Γ⟫) := run_store (env := env) hfits
    (show Ty.flatten (.bv 8) (.value (byte8 window)) = .value (byte8 window) from rfl)
  have hparams8 : serialKernel.blockParams 8 = .cons (%74) (.cons (%75) .nil) := rfl
  have hparams14 : serialKernel.blockParams 14 = .nil := rfl
  by_cases hnext : pos.val < 248 <;>
    simp [hparams8, hparams14, BasicBlock.run, serialKernel.bb13, storeInput8, storeResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, UnOp.compute,
      GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hout, hhigh, hdigit, hcarry,
      hscale, hgep, hstore, hadd, hcmp, hnext,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]


/-- The actual post-emitter continuation is block 7, not a function return. -/
theorem serial5_even_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    (serialKernel p g).runFrom (evenInput5 E pos) 5 s =
      if pos.val + 1 = 256 then
        (serialKernel p g).runFrom (evenResult5 E pos) 7 s
      else (serialKernel p g).runFrom
        ((evenResult5 E pos)[%45 := .value (BitVec.ofNat 64 (pos.val + 1))]) 2 s := by
  have hblock : (serialKernel p g).blocks 5 = serialKernel.bb5 := rfl
  rw [Func.runFrom_eq, hblock, serial5_even_block]
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false, PoisonOr.value_bind, Func.continue]

/-- Width eight exits into the scan setup, retaining its concrete environment. -/
theorem serial8_even_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    (serialKernel p g).runFrom (evenInput8 E pos) 12 s =
      if pos.val + 1 = 256 then
        (serialKernel p g).runFrom (evenResult8 E pos) 14 s
      else (serialKernel p g).runFrom
        ((evenResult8 E pos)[%76 := .value (BitVec.ofNat 64 (pos.val + 1))]) 9 s := by
  have hblock : (serialKernel p g).blocks 12 = serialKernel.bb12 := rfl
  rw [Func.runFrom_eq, hblock, serial8_even_block]
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false, PoisonOr.value_bind, Func.continue]

theorem serial5_store_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 33)
    (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%41) = .value out) :
    (serialKernel p g).runFrom (storeInput5 E pos window) 6 s =
      if pos.val < 251 then (serialKernel p g).runFrom
        ((storeResult5 E out pos window)[%43 := .value (BitVec.ofNat 64 (pos.val + 5)), %44 := .value (carry5 window)]) 1
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}
      else (serialKernel p g).runFrom (storeResult5 E out pos window) 7
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)} := by
  have hblock : (serialKernel p g).blocks 6 = serialKernel.bb6 := rfl
  rw [Func.runFrom_eq, hblock, serial5_store_block E out pos window s hbuffer hout]
  by_cases hnext : pos.val < 251 <;>
    simp only [hnext, ite_true, ite_false, PoisonOr.value_bind, Func.continue]

theorem serial8_store_run (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 257)
    (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%40) = .value out) :
    (serialKernel p g).runFrom (storeInput8 E pos window) 13 s =
      if pos.val < 248 then (serialKernel p g).runFrom
        ((storeResult8 E out pos window)[%74 := .value (BitVec.ofNat 64 (pos.val + 8)), %75 := .value (carry8 window)]) 8
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}
      else (serialKernel p g).runFrom (storeResult8 E out pos window) 14
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)} := by
  have hblock : (serialKernel p g).blocks 13 = serialKernel.bb13 := rfl
  rw [Func.runFrom_eq, hblock, serial8_store_block E out pos window s hbuffer hout]
  by_cases hnext : pos.val < 248 <;>
    simp only [hnext, ite_true, ite_false, PoisonOr.value_bind, Func.continue]

/-- Width-five carry transport changes only the inner cursor register. -/
theorem serial5_carry_entry (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) :
    (serialKernel p g).runFrom E 1 s =
      (serialKernel p g).runFrom (E[%45 := E.read (%43)]) 2 s := by
  rw [Func.runFrom_eq]
  rfl

/-- Width-eight carry transport changes only the inner cursor register. -/
theorem serial8_carry_entry (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) :
    (serialKernel p g).runFrom E 8 s =
      (serialKernel p g).runFrom (E[%76 := E.read (%74)]) 9 s := by
  rw [Func.runFrom_eq]
  rfl

/-- The actual width-eight exit enters the scan at counter 256, as held in %2. -/
theorem serial8_scan_entry (p : SerialCFG.Primitives) (g : SerialCFG.Globals)
    (E : ⟪serialKernel.Γ⟫) (s : GlobalState) :
    (serialKernel p g).runFrom E 14 s =
      (serialKernel p g).runFrom (E[%102 := E.read (%2)]) 15 s := by
  rw [Func.runFrom_eq]
  rfl

end Agave.Ed25519.DoubleBase.RIR
