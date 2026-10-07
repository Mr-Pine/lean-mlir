import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Control

/-! Actual AVX2 NAF word-load, cross-word, and digit-store blocks. Every
memory operation is justified by a live buffer, and all index and overflow
conditions are derived from the finite cursor and carry/window ranges. -/

namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR NAF NAF.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def loadInput5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  E[%5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %258 := .value scratch, %270 := .value (BitVec.ofNat 64 pos.val)]

def loadResult5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (bits : BitVec 320) :
    ⟪avx2Kernel.Γ⟫ :=
  (loadInput5 E scratch pos)[%271 := .value (BitVec.ofNat 64 (pos.val / 64)),
    %272 := .value (BitVec.ofNat 64 (pos.val % 64)),
    %273 := .value (if pos.val % 64 < 59 then 1#1 else 0#1),
    %274 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))),
    %275 := .value (WordWindow.word bits (pos.val / 64)),
    %276 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))]

/-- The first real word load and its branch. The complete scratch object
supplies both the address promise and the loaded word, for every live cursor. -/
theorem load5_block (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (bits : BitVec 320) (s : GlobalState) (hbuffer : Buffer s.mem scratch 40)
    (hbits : s.mem.readAt scratch 320 = bits) :
    avx2Kernel.bb2.run avx2Kernel.blockParams (loadInput5 E scratch pos) s =
      if pos.val % 64 < 59 then
        .value (((loadResult5 E scratch pos bits)[%283 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))], .inr 4), s)
      else .value ((loadResult5 E scratch pos bits, .inr 3), s) := by
  obtain ⟨hindex, hbit, hscale, hcmp, _⟩ := cursor_words pos
  have hgep := hbuffer.gep (8 * (pos.val / 64)) (by have := pos.isLt; omega)
  simp only [Int.natCast_mul, Int.natCast_ediv, Int.cast_ofNat_Int] at hgep
  have hfits := hbuffer.fits_at (8 * (pos.val / 64)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits ⟨pos.val / 64, by have := pos.isLt; omega⟩
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%275 : Dst avx2Kernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64))))) env s =
          .value (env[%275 := .value (WordWindow.word bits (pos.val / 64))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hlow := low_shift (WordWindow.word bits (pos.val / 64)) pos
  by_cases hcross : pos.val % 64 < 59 <;>
    simp only [hcross, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb2, loadInput5, loadResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
      EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      hindex, hbit, hscale, hcmp, hgep, hload, hlow, hcross,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def loadInput8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) : ⟪avx2Kernel.Γ⟫ :=
  E[%5 := .value 6#64, %6 := .value 63#64, %15 := .value 56#64,
    %257 := .value scratch, %301 := .value (BitVec.ofNat 64 pos.val)]

def loadResult8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (bits : BitVec 320) :
    ⟪avx2Kernel.Γ⟫ :=
  (loadInput8 E scratch pos)[%302 := .value (BitVec.ofNat 64 (pos.val / 64)),
    %303 := .value (BitVec.ofNat 64 (pos.val % 64)),
    %304 := .value (if pos.val % 64 < 56 then 1#1 else 0#1),
    %305 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))),
    %306 := .value (WordWindow.word bits (pos.val / 64)),
    %307 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))]

theorem load8_block (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (bits : BitVec 320) (s : GlobalState) (hbuffer : Buffer s.mem scratch 40)
    (hbits : s.mem.readAt scratch 320 = bits) :
    avx2Kernel.bb9.run avx2Kernel.blockParams (loadInput8 E scratch pos) s =
      if pos.val % 64 < 56 then
        .value (((loadResult8 E scratch pos bits)[%314 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))], .inr 11), s)
      else .value ((loadResult8 E scratch pos bits, .inr 10), s) := by
  obtain ⟨hindex, hbit, hscale, _, hcmp⟩ := cursor_words pos
  have hgep := hbuffer.gep (8 * (pos.val / 64)) (by have := pos.isLt; omega)
  simp only [Int.natCast_mul, Int.natCast_ediv, Int.cast_ofNat_Int] at hgep
  have hfits := hbuffer.fits_at (8 * (pos.val / 64)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits ⟨pos.val / 64, by have := pos.isLt; omega⟩
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%306 : Dst avx2Kernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64))))) env s =
          .value (env[%306 := .value (WordWindow.word bits (pos.val / 64))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hlow := low_shift (WordWindow.word bits (pos.val / 64)) pos
  by_cases hcross : pos.val % 64 < 56 <;>
    simp only [hcross, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb9, loadInput8, loadResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
      EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      hindex, hbit, hscale, hcmp, hgep, hload, hlow, hcross,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def crossInput5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (low : BitVec 64) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%4 := .value 0#64, %6 := .value 63#64, %8 := .value 8#64,
    %270 := .value (BitVec.ofNat 64 pos.val),
    %274 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))), %276 := .value low]

def crossResult5 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  (crossInput5 E scratch pos low)[%277 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))),
    %278 := .value (WordWindow.word bits (pos.val / 64 + 1)),
    %279 := .value (-BitVec.ofNat 64 pos.val),
    %280 := .value (BitVec.ofNat 64 (64 - pos.val % 64)),
    %281 := .value (WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)),
    %282 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

theorem cross5_block (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (hcross : ¬pos.val % 64 < 59) :
    avx2Kernel.bb3.run avx2Kernel.blockParams (crossInput5 E scratch pos low) s =
      .value (((crossResult5 E scratch pos low bits)[%283 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)],
        .inr 4), s) := by
  have hbase := hbuffer.slice (8 * (pos.val / 64)) 16 (by have := pos.isLt; omega)
  have hgep := hbase.gep 8 (by decide)
  simp only [Pointer.add_add, next_word_offset pos, Int.cast_ofNat_Int] at hgep
  have hscale : Operation.gepInboundsIndex 1 (.value 8#64) = .value (8 : Int) := by decide +kernel
  have hfits := hbuffer.fits_at (8 * (pos.val / 64 + 1)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits
    ⟨pos.val / 64 + 1, by have := pos.isLt; omega⟩
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%278 : Dst avx2Kernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1))))) env s =
          .value (env[%278 := .value (WordWindow.word bits (pos.val / 64 + 1))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hneg := cursor_negate pos
  have hcount := cursor_cross_shift 5 (Or.inl rfl) pos hcross
  have hs := (cross_word_shift_safe pos.val 5 (Or.inl rfl) hcross).2
  have hhigh := high_shift (WordWindow.word bits (pos.val / 64 + 1)) _ hs
  simp [BasicBlock.run, avx2Kernel.bb3, crossInput5, crossResult5,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hscale, hgep, hload, hneg, hcount, hhigh, Operation.or,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def crossInput8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256) (low : BitVec 64) :
    ⟪avx2Kernel.Γ⟫ :=
  E[%4 := .value 0#64, %6 := .value 63#64, %8 := .value 8#64,
    %301 := .value (BitVec.ofNat 64 pos.val),
    %305 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))), %307 := .value low]

def crossResult8 (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) : ⟪avx2Kernel.Γ⟫ :=
  (crossInput8 E scratch pos low)[%308 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))),
    %309 := .value (WordWindow.word bits (pos.val / 64 + 1)),
    %310 := .value (-BitVec.ofNat 64 pos.val),
    %311 := .value (BitVec.ofNat 64 (64 - pos.val % 64)),
    %312 := .value (WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)),
    %313 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

theorem cross8_block (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (hcross : ¬pos.val % 64 < 56) :
    avx2Kernel.bb10.run avx2Kernel.blockParams (crossInput8 E scratch pos low) s =
      .value (((crossResult8 E scratch pos low bits)[%314 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)],
        .inr 11), s) := by
  have hbase := hbuffer.slice (8 * (pos.val / 64)) 16 (by have := pos.isLt; omega)
  have hgep := hbase.gep 8 (by decide)
  simp only [Pointer.add_add, next_word_offset pos, Int.cast_ofNat_Int] at hgep
  have hscale : Operation.gepInboundsIndex 1 (.value 8#64) = .value (8 : Int) := by decide +kernel
  have hfits := hbuffer.fits_at (8 * (pos.val / 64 + 1)) 8 (by have := pos.isLt; omega)
  have hread := NAF.Memory.read_word hbuffer bits hbits
    ⟨pos.val / 64 + 1, by have := pos.isLt; omega⟩
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%309 : Dst avx2Kernel.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1))))) env s =
          .value (env[%309 := .value (WordWindow.word bits (pos.val / 64 + 1))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hneg := cursor_negate pos
  have hcount := cursor_cross_shift 8 (Or.inr rfl) pos hcross
  have hs := (cross_word_shift_safe pos.val 8 (Or.inr rfl) hcross).2
  have hhigh := high_shift (WordWindow.word bits (pos.val / 64 + 1)) _ hs
  simp [BasicBlock.run, avx2Kernel.bb10, crossInput8, crossResult8,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hscale, hgep, hload, hneg, hcount, hhigh, Operation.or,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def storeInput5 (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (window : Fin 33) : ⟪avx2Kernel.Γ⟫ :=
  E[%1 := .value 0#8, %11 := .value 15#64, %12 := .value (-32 : BitVec 8),
    %13 := .value 5#64, %14 := .value 251#64, %270 := .value (BitVec.ofNat 64 pos.val),
    %285 := .value (BitVec.ofNat 64 window.val)]

def storeResult5 (E : ⟪avx2Kernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 33) :
    ⟪avx2Kernel.Γ⟫ :=
  (storeInput5 E pos window)[%290 := .value (high5 window),
    %291 := .value (BitVec.ofNat 8 window.val), %292 := .value (bias5 window),
    %293 := .value (byte5 window), %294 := .value (carry5 window),
    %295 := .value (out.add (BitVec.ofNat 64 pos.val)),
    %296 := .value (BitVec.ofNat 64 (pos.val + 5)),
    %297 := .value (if pos.val < 251 then 1#1 else 0#1)]

/-- The original width-five store block writes exactly one byte and returns
the concrete carry/cursor edge. The GEP and store are justified by the outer
256-byte allocation, with no index-safety premise on the digit. -/
theorem store5_block (E : ⟪avx2Kernel.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 33) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%266) = .value out) :
    avx2Kernel.bb6.run avx2Kernel.blockParams (storeInput5 E pos window) s =
      if pos.val < 251 then
        .value (((storeResult5 E out pos window)[%268 := .value (BitVec.ofNat 64 (pos.val + 5)), %269 := .value (carry5 window)],
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
  have hstore (env : ⟪avx2Kernel.Γ⟫) := run_store (env := env) hfits
    (show Ty.flatten (.bv 8) (.value (byte5 window)) = .value (byte5 window) from rfl)
  by_cases hnext : pos.val < 251 <;>
    simp only [hnext, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb6, storeInput5, storeResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, UnOp.compute,
      TernOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hout, hhigh, htrunc,
      hselect, hdigit, hcarry, hscale, hgep, hstore, hadd, hcmp, hnext,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def storeInput8 (E : ⟪avx2Kernel.Γ⟫) (pos : Fin 256) (window : Fin 257) : ⟪avx2Kernel.Γ⟫ :=
  E[%8 := .value 8#64, %17 := .value 127#64, %18 := .value 248#64,
    %301 := .value (BitVec.ofNat 64 pos.val), %316 := .value (BitVec.ofNat 64 window.val)]

def storeResult8 (E : ⟪avx2Kernel.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 257) :
    ⟪avx2Kernel.Γ⟫ :=
  (storeInput8 E pos window)[%321 := .value (high8 window), %322 := .value (byte8 window),
    %323 := .value (carry8 window), %324 := .value (out.add (BitVec.ofNat 64 pos.val)),
    %325 := .value (BitVec.ofNat 64 (pos.val + 8)),
    %326 := .value (if pos.val < 248 then 1#1 else 0#1)]

theorem store8_block (E : ⟪avx2Kernel.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 257) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%265) = .value out) :
    avx2Kernel.bb13.run avx2Kernel.blockParams (storeInput8 E pos window) s =
      if pos.val < 248 then
        .value (((storeResult8 E out pos window)[%299 := .value (BitVec.ofNat 64 (pos.val + 8)), %300 := .value (carry8 window)],
          .inr 8), {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)})
      else .value ((storeResult8 E out pos window, .inr 14),
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}) := by
  obtain ⟨hhigh, hdigit, hcarry⟩ := store_arithmetic8 window
  obtain ⟨hadd, hcmp⟩ := cursor_eight pos
  have hscale := cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hstore (env : ⟪avx2Kernel.Γ⟫) := run_store (env := env) hfits
    (show Ty.flatten (.bv 8) (.value (byte8 window)) = .value (byte8 window) from rfl)
  by_cases hnext : pos.val < 248 <;>
    simp only [hnext, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, avx2Kernel.bb13, storeInput8, storeResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, UnOp.compute,
      GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hout, hhigh, hdigit, hcarry,
      hscale, hgep, hstore, hadd, hcmp, hnext,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

end Agave.Ed25519.DoubleBase.ExecutionAvx2
