import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialBlocks
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialNAF

/-! The actual serial double-base limb-window blocks, retaining both loads,
flagged interior addresses, cross-word shifts, and original successors. -/

namespace Agave.Ed25519.DoubleBase.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)
open NAF.RIR

set_option maxRecDepth 10000

def loadInput5 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %31 := .value scratch, %45 := .value (BitVec.ofNat 64 pos.val)]

def loadResult5 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (bits : BitVec 320) :
    ⟪serialKernel.Γ⟫ :=
  (loadInput5 E scratch pos)[%46 := .value (BitVec.ofNat 64 (pos.val / 64)),
    %47 := .value (BitVec.ofNat 64 (pos.val % 64)),
    %48 := .value (if pos.val % 64 < 59 then 1#1 else 0#1),
    %49 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))),
    %50 := .value (NAF.WordWindow.word bits (pos.val / 64)),
    %51 := .value (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))]

/-- The first real word load and its branch. The complete scratch object
supplies both the address promise and the loaded word, for every live cursor. -/
theorem serial5_load_block (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (bits : BitVec 320) (s : GlobalState) (hbuffer : Buffer s.mem scratch 40)
    (hbits : s.mem.readAt scratch 320 = bits) :
    serialKernel.bb2.run serialKernel.blockParams (loadInput5 E scratch pos) s =
      if pos.val % 64 < 59 then
        .value (((loadResult5 E scratch pos bits)[%58 := .value (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))], .inr 4), s)
      else .value ((loadResult5 E scratch pos bits, .inr 3), s) := by
  obtain ⟨hindex, hbit, hscale, hcmp, _⟩ := cursor_words pos
  have hgep := hbuffer.gep (8 * (pos.val / 64)) (by have := pos.isLt; omega)
  simp only [Int.natCast_mul, Int.natCast_ediv, Int.cast_ofNat_Int] at hgep
  have hfits := hbuffer.fits_at (8 * (pos.val / 64)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits ⟨pos.val / 64, by have := pos.isLt; omega⟩
  have hload (env : ⟪serialKernel.Γ⟫) :
      Operation.load (%50 : Dst serialKernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64))))) env s =
          .value (env[%50 := .value (NAF.WordWindow.word bits (pos.val / 64))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hlow := low_shift (NAF.WordWindow.word bits (pos.val / 64)) pos
  by_cases hcross : pos.val % 64 < 59 <;>
    simp [BasicBlock.run, serialKernel.bb2, loadInput5, loadResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
      EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      hindex, hbit, hscale, hcmp, hgep, hload, hlow, hcross,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def loadInput8 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) : ⟪serialKernel.Γ⟫ :=
  E[%5 := .value 6#64, %6 := .value 63#64, %15 := .value 56#64,
    %30 := .value scratch, %76 := .value (BitVec.ofNat 64 pos.val)]

def loadResult8 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (bits : BitVec 320) :
    ⟪serialKernel.Γ⟫ :=
  (loadInput8 E scratch pos)[%77 := .value (BitVec.ofNat 64 (pos.val / 64)),
    %78 := .value (BitVec.ofNat 64 (pos.val % 64)),
    %79 := .value (if pos.val % 64 < 56 then 1#1 else 0#1),
    %80 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))),
    %81 := .value (NAF.WordWindow.word bits (pos.val / 64)),
    %82 := .value (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))]

theorem serial8_load_block (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (bits : BitVec 320) (s : GlobalState) (hbuffer : Buffer s.mem scratch 40)
    (hbits : s.mem.readAt scratch 320 = bits) :
    serialKernel.bb9.run serialKernel.blockParams (loadInput8 E scratch pos) s =
      if pos.val % 64 < 56 then
        .value (((loadResult8 E scratch pos bits)[%89 := .value (NAF.WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))], .inr 11), s)
      else .value ((loadResult8 E scratch pos bits, .inr 10), s) := by
  obtain ⟨hindex, hbit, hscale, _, hcmp⟩ := cursor_words pos
  have hgep := hbuffer.gep (8 * (pos.val / 64)) (by have := pos.isLt; omega)
  simp only [Int.natCast_mul, Int.natCast_ediv, Int.cast_ofNat_Int] at hgep
  have hfits := hbuffer.fits_at (8 * (pos.val / 64)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits ⟨pos.val / 64, by have := pos.isLt; omega⟩
  have hload (env : ⟪serialKernel.Γ⟫) :
      Operation.load (%81 : Dst serialKernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64))))) env s =
          .value (env[%81 := .value (NAF.WordWindow.word bits (pos.val / 64))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hlow := low_shift (NAF.WordWindow.word bits (pos.val / 64)) pos
  by_cases hcross : pos.val % 64 < 56 <;>
    simp [BasicBlock.run, serialKernel.bb9, loadInput8, loadResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
      EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      hindex, hbit, hscale, hcmp, hgep, hload, hlow, hcross,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def crossInput5 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (low : BitVec 64) :
    ⟪serialKernel.Γ⟫ :=
  E[%4 := .value 0#64, %6 := .value 63#64, %8 := .value 8#64,
    %45 := .value (BitVec.ofNat 64 pos.val),
    %49 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))), %51 := .value low]

def crossResult5 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) : ⟪serialKernel.Γ⟫ :=
  (crossInput5 E scratch pos low)[%52 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))),
    %53 := .value (NAF.WordWindow.word bits (pos.val / 64 + 1)),
    %54 := .value (-BitVec.ofNat 64 pos.val),
    %55 := .value (BitVec.ofNat 64 (64 - pos.val % 64)),
    %56 := .value (NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)),
    %57 := .value ((NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

theorem serial5_cross_block (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (hcross : ¬pos.val % 64 < 59) :
    serialKernel.bb3.run serialKernel.blockParams (crossInput5 E scratch pos low) s =
      .value (((crossResult5 E scratch pos low bits)[%58 := .value ((NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)],
        .inr 4), s) := by
  have hbase := hbuffer.slice (8 * (pos.val / 64)) 16 (by have := pos.isLt; omega)
  have hgep := hbase.gep 8 (by decide)
  simp only [Pointer.add_add, next_word_offset pos, Int.cast_ofNat_Int] at hgep
  have hscale : Operation.gepInboundsIndex 1 (.value 8#64) = .value (8 : Int) := by decide +kernel
  have hfits := hbuffer.fits_at (8 * (pos.val / 64 + 1)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits
    ⟨pos.val / 64 + 1, by have := pos.isLt; omega⟩
  have hload (env : ⟪serialKernel.Γ⟫) :
      Operation.load (%53 : Dst serialKernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1))))) env s =
          .value (env[%53 := .value (NAF.WordWindow.word bits (pos.val / 64 + 1))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hneg := cursor_negate pos
  have hcount := cursor_cross_shift 5 (Or.inl rfl) pos hcross
  have hs := (NAF.cross_word_shift_safe pos.val 5 (Or.inl rfl) hcross).2
  have hhigh := high_shift (NAF.WordWindow.word bits (pos.val / 64 + 1)) _ hs
  simp [BasicBlock.run, serialKernel.bb3, crossInput5, crossResult5,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hscale, hgep, hload, hneg, hcount, hhigh, Operation.or,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def crossInput8 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (low : BitVec 64) :
    ⟪serialKernel.Γ⟫ :=
  E[%4 := .value 0#64, %6 := .value 63#64, %8 := .value 8#64,
    %76 := .value (BitVec.ofNat 64 pos.val),
    %80 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))), %82 := .value low]

def crossResult8 (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) : ⟪serialKernel.Γ⟫ :=
  (crossInput8 E scratch pos low)[%83 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))),
    %84 := .value (NAF.WordWindow.word bits (pos.val / 64 + 1)),
    %85 := .value (-BitVec.ofNat 64 pos.val),
    %86 := .value (BitVec.ofNat 64 (64 - pos.val % 64)),
    %87 := .value (NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)),
    %88 := .value ((NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

theorem serial8_cross_block (E : ⟪serialKernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (hcross : ¬pos.val % 64 < 56) :
    serialKernel.bb10.run serialKernel.blockParams (crossInput8 E scratch pos low) s =
      .value (((crossResult8 E scratch pos low bits)[%89 := .value ((NAF.WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)],
        .inr 11), s) := by
  have hbase := hbuffer.slice (8 * (pos.val / 64)) 16 (by have := pos.isLt; omega)
  have hgep := hbase.gep 8 (by decide)
  simp only [Pointer.add_add, next_word_offset pos, Int.cast_ofNat_Int] at hgep
  have hscale : Operation.gepInboundsIndex 1 (.value 8#64) = .value (8 : Int) := by decide +kernel
  have hfits := hbuffer.fits_at (8 * (pos.val / 64 + 1)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits
    ⟨pos.val / 64 + 1, by have := pos.isLt; omega⟩
  have hload (env : ⟪serialKernel.Γ⟫) :
      Operation.load (%84 : Dst serialKernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1))))) env s =
          .value (env[%84 := .value (NAF.WordWindow.word bits (pos.val / 64 + 1))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hneg := cursor_negate pos
  have hcount := cursor_cross_shift 8 (Or.inr rfl) pos hcross
  have hs := (NAF.cross_word_shift_safe pos.val 8 (Or.inr rfl) hcross).2
  have hhigh := high_shift (NAF.WordWindow.word bits (pos.val / 64 + 1)) _ hs
  simp [BasicBlock.run, serialKernel.bb10, crossInput8, crossResult8,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hscale, hgep, hload, hneg, hcount, hhigh, Operation.or,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

end Agave.Ed25519.DoubleBase.RIR
