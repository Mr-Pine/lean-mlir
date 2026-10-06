import SSA.Projects.Agave.Ed25519.Proof.NAF.Program
import SSA.Projects.Agave.Ed25519.Proof.NAF.Memory
import SSA.Projects.Agave.Ed25519.Proof.NAF.OperationWindow
import SSA.Projects.RIR.Run.Tactic

/-!
# Execution of imported NAF loop blocks

The left-hand sides here are `BasicBlock.run` and `Func.runFrom` for the exact
compiler blocks imported by `import_program.py`. Registers and successors are
retained. Local entry environments describe the loop invariant; no execution
result or absence-of-poison hypothesis is used to prove these block equations.
-/
namespace Agave.Ed25519.NAF.RIR

open LeanMLIR.RIR
open NAF.Memory (Buffer)

set_option maxRecDepth 10000

-- The importer represents the finite block tables with nested `Fin.cases`.
-- These closed projection equations expose their exact branch arguments.
@[simp] theorem kernel5_params0 : kernel5.blockParams 0 = Dsts.nil := rfl
@[simp] theorem kernel5_params1 : kernel5.blockParams 1 = .cons (%17) (.cons (%18) .nil) := rfl
@[simp] theorem kernel5_params2 : kernel5.blockParams 2 = .cons (%19) .nil := rfl
@[simp] theorem kernel5_params3 : kernel5.blockParams 3 = Dsts.nil := rfl
@[simp] theorem kernel5_params4 : kernel5.blockParams 4 = .cons (%32) .nil := rfl
@[simp] theorem kernel5_params5 : kernel5.blockParams 5 = Dsts.nil := rfl
@[simp] theorem kernel5_params6 : kernel5.blockParams 6 = Dsts.nil := rfl
@[simp] theorem kernel5_params7 : kernel5.blockParams 7 = Dsts.nil := rfl

@[simp] theorem kernel8_params0 : kernel8.blockParams 0 = Dsts.nil := rfl
@[simp] theorem kernel8_params1 : kernel8.blockParams 1 = .cons (%15) (.cons (%16) .nil) := rfl
@[simp] theorem kernel8_params2 : kernel8.blockParams 2 = .cons (%17) .nil := rfl
@[simp] theorem kernel8_params3 : kernel8.blockParams 3 = Dsts.nil := rfl
@[simp] theorem kernel8_params4 : kernel8.blockParams 4 = .cons (%30) .nil := rfl
@[simp] theorem kernel8_params5 : kernel8.blockParams 5 = Dsts.nil := rfl
@[simp] theorem kernel8_params6 : kernel8.blockParams 6 = Dsts.nil := rfl
@[simp] theorem kernel8_params7 : kernel8.blockParams 7 = Dsts.nil := rfl

/-- Every possible live cursor satisfies the compiler's flagged increment. -/
theorem cursor_one : ∀ pos : Fin 256,
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 pos.val)) (.value 1#64) =
      .value (BitVec.ofNat 64 (pos.val + 1)) ∧
    Operation.icmp .eq (.value (BitVec.ofNat 64 (pos.val + 1))) (.value 256#64) =
      .value (if pos.val + 1 = 256 then 1#1 else 0#1) := by
  decide +kernel

theorem cursor_five : ∀ pos : Fin 256,
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 pos.val)) (.value 5#64) =
      .value (BitVec.ofNat 64 (pos.val + 5)) ∧
    Operation.icmp .ult (.value (BitVec.ofNat 64 pos.val)) (.value 251#64) =
      .value (if pos.val < 251 then 1#1 else 0#1) := by
  decide +kernel

theorem cursor_eight : ∀ pos : Fin 256,
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 pos.val)) (.value 8#64) =
      .value (BitVec.ofNat 64 (pos.val + 8)) ∧
    Operation.icmp .ult (.value (BitVec.ofNat 64 pos.val)) (.value 248#64) =
      .value (if pos.val < 248 then 1#1 else 0#1) := by
  decide +kernel

theorem cursor_byte_offset : ∀ pos : Fin 256,
    Operation.gepInboundsIndex 1 (.value (BitVec.ofNat 64 pos.val)) =
      .value (pos.val : Int) := by
  decide +kernel

theorem cursor_words : ∀ pos : Fin 256,
    Operation.lshr false (.value (BitVec.ofNat 64 pos.val)) (.value 6#64) =
      .value (BitVec.ofNat 64 (pos.val / 64)) ∧
    Operation.and (.value (BitVec.ofNat 64 pos.val)) (.value 63#64) =
      .value (BitVec.ofNat 64 (pos.val % 64)) ∧
    Operation.gepInboundsIndex 8 (.value (BitVec.ofNat 64 (pos.val / 64))) =
      .value ((8 * (pos.val / 64) : Nat) : Int) ∧
    Operation.icmp .ult (.value (BitVec.ofNat 64 (pos.val % 64))) (.value 59#64) =
      .value (if pos.val % 64 < 59 then 1#1 else 0#1) ∧
    Operation.icmp .ult (.value (BitVec.ofNat 64 (pos.val % 64))) (.value 56#64) =
      .value (if pos.val % 64 < 56 then 1#1 else 0#1) := by
  decide +kernel

theorem low_shift (word : BitVec 64) (pos : Fin 256) :
    Operation.lshr false (.value word) (.value (BitVec.ofNat 64 (pos.val % 64))) =
      .value (word >>> (pos.val % 64)) := by
  have hbit : pos.val % 64 < 64 := Nat.mod_lt _ (by decide)
  have hbit64 : pos.val % 64 < 2 ^ 64 := by omega
  simp only [Operation.lshr, PoisonOr.value_bind, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hbit64, Nat.not_le_of_lt hbit, if_false, PoisonOr.pure_def, Bool.false_eq_true]
  rfl

theorem high_shift (word : BitVec 64) (shift : Nat) (hs : shift < 64) :
    Operation.shl {} (.value word) (.value (BitVec.ofNat 64 shift)) =
      .value (word <<< shift) := by
  have hs64 : shift < 2 ^ 64 := by omega
  simp only [Operation.shl, PoisonOr.value_bind, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs64]
  simp [Nat.not_le_of_lt hs]

theorem cursor_negate (pos : Fin 256) :
    Operation.sub {nsw := true} (.value 0#64) (.value (BitVec.ofNat 64 pos.val)) =
      .value (-BitVec.ofNat 64 pos.val) := by
  have hn := WordWindow.compiled_negation_no_overflow pos
  simp [Operation.sub, hn]

theorem cursor_cross_shift (width : Nat) (hw : Supported width) (pos : Fin 256)
    (hcross : ¬pos.val % 64 < 64 - width) :
    Operation.and (.value (-BitVec.ofNat 64 pos.val)) (.value 63#64) =
      .value (BitVec.ofNat 64 (64 - pos.val % 64)) := by
  have hv := WordWindow.compiled_cross_shift width hw pos hcross
  have hs := cross_word_shift_safe pos.val width hw hcross
  have hs64 : 64 - pos.val % 64 < 2 ^ 64 := by omega
  have hb : (-BitVec.ofNat 64 pos.val) &&& 63#64 =
      BitVec.ofNat 64 (64 - pos.val % 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs64]
  simp only [Operation.and, PoisonOr.value_bind, PoisonOr.pure_def, hb]

theorem next_word_offset : ∀ pos : Fin 256,
    BitVec.ofNat 64 (8 * (pos.val / 64)) + 8#64 =
      BitVec.ofNat 64 (8 * (pos.val / 64 + 1)) := by
  decide +kernel

theorem kernel5_exit_block (E : ⟪kernel5.Γ⟫) (s : GlobalState) :
    kernel5.bb7.run kernel5.blockParams E s = .value ((E, .inl .nil), s) := by
  rfl

theorem kernel8_exit_block (E : ⟪kernel8.Γ⟫) (s : GlobalState) :
    kernel8.bb7.run kernel8.blockParams E s = .value ((E, .inl .nil), s) := by
  rfl

theorem kernel5_exit_run (E : ⟪kernel5.Γ⟫) (s : GlobalState) :
    kernel5.runFrom E 7 s = .value (.nil, s) := by
  rw [Func.runFrom_eq, show kernel5.blocks 7 = kernel5.bb7 from rfl, kernel5_exit_block]
  rfl

theorem kernel8_exit_run (E : ⟪kernel8.Γ⟫) (s : GlobalState) :
    kernel8.runFrom E 7 s = .value (.nil, s) := by
  rw [Func.runFrom_eq, show kernel8.blocks 7 = kernel8.bb7 from rfl, kernel8_exit_block]
  rfl

/-- The outer carry block changes only the inner loop cursor. -/
theorem kernel5_carry_entry (E : ⟪kernel5.Γ⟫) (s : GlobalState) :
    kernel5.runFrom E 1 s = kernel5.runFrom (E[%19 := E.read (%17)]) 2 s := by
  rw [Func.runFrom_eq]
  rfl

theorem kernel8_carry_entry (E : ⟪kernel8.Γ⟫) (s : GlobalState) :
    kernel8.runFrom E 1 s = kernel8.runFrom (E[%17 := E.read (%15)]) 2 s := by
  rw [Func.runFrom_eq]
  rfl

def loadInput5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256) : ⟪kernel5.Γ⟫ :=
  E[%5 := .value 6#64, %6 := .value 63#64, %7 := .value 59#64,
    %15 := .value scratch, %19 := .value (BitVec.ofNat 64 pos.val)]

def loadResult5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256) (bits : BitVec 320) :
    ⟪kernel5.Γ⟫ :=
  (loadInput5 E scratch pos)[%20 := .value (BitVec.ofNat 64 (pos.val / 64)),
    %21 := .value (BitVec.ofNat 64 (pos.val % 64)),
    %22 := .value (if pos.val % 64 < 59 then 1#1 else 0#1),
    %23 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))),
    %24 := .value (WordWindow.word bits (pos.val / 64)),
    %25 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))]

/-- The first real word load and its branch. The complete scratch object
supplies both the address promise and the loaded word, for every live cursor. -/
theorem kernel5_load_block (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (bits : BitVec 320) (s : GlobalState) (hbuffer : Buffer s.mem scratch 40)
    (hbits : s.mem.readAt scratch 320 = bits) :
    kernel5.bb2.run kernel5.blockParams (loadInput5 E scratch pos) s =
      if pos.val % 64 < 59 then
        .value (((loadResult5 E scratch pos bits)[%32 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))], .inr 4), s)
      else .value ((loadResult5 E scratch pos bits, .inr 3), s) := by
  obtain ⟨hindex, hbit, hscale, hcmp, _⟩ := cursor_words pos
  have hgep := hbuffer.gep (8 * (pos.val / 64)) (by have := pos.isLt; omega)
  simp only [Int.natCast_mul, Int.natCast_ediv, Int.cast_ofNat_Int] at hgep
  have hfits := hbuffer.fits_at (8 * (pos.val / 64)) 8 (by have := pos.isLt; omega)
  have hread := Memory.read_word hbuffer bits hbits ⟨pos.val / 64, by have := pos.isLt; omega⟩
  have hload (env : ⟪kernel5.Γ⟫) :
      Operation.load (%24 : Dst kernel5.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64))))) env s =
          .value (env[%24 := .value (WordWindow.word bits (pos.val / 64))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hlow := low_shift (WordWindow.word bits (pos.val / 64)) pos
  by_cases hcross : pos.val % 64 < 59 <;>
    simp [BasicBlock.run, kernel5.bb2, loadInput5, loadResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
      EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      hindex, hbit, hscale, hcmp, hgep, hload, hlow, hcross,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def loadInput8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256) : ⟪kernel8.Γ⟫ :=
  E[%5 := .value 6#64, %6 := .value 63#64, %7 := .value 56#64,
    %13 := .value scratch, %17 := .value (BitVec.ofNat 64 pos.val)]

def loadResult8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256) (bits : BitVec 320) :
    ⟪kernel8.Γ⟫ :=
  (loadInput8 E scratch pos)[%18 := .value (BitVec.ofNat 64 (pos.val / 64)),
    %19 := .value (BitVec.ofNat 64 (pos.val % 64)),
    %20 := .value (if pos.val % 64 < 56 then 1#1 else 0#1),
    %21 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))),
    %22 := .value (WordWindow.word bits (pos.val / 64)),
    %23 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))]

theorem kernel8_load_block (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (bits : BitVec 320) (s : GlobalState) (hbuffer : Buffer s.mem scratch 40)
    (hbits : s.mem.readAt scratch 320 = bits) :
    kernel8.bb2.run kernel8.blockParams (loadInput8 E scratch pos) s =
      if pos.val % 64 < 56 then
        .value (((loadResult8 E scratch pos bits)[%30 := .value (WordWindow.word bits (pos.val / 64) >>> (pos.val % 64))], .inr 4), s)
      else .value ((loadResult8 E scratch pos bits, .inr 3), s) := by
  obtain ⟨hindex, hbit, hscale, _, hcmp⟩ := cursor_words pos
  have hgep := hbuffer.gep (8 * (pos.val / 64)) (by have := pos.isLt; omega)
  simp only [Int.natCast_mul, Int.natCast_ediv, Int.cast_ofNat_Int] at hgep
  have hfits := hbuffer.fits_at (8 * (pos.val / 64)) 8 (by have := pos.isLt; omega)
  have hread := Memory.read_word hbuffer bits hbits ⟨pos.val / 64, by have := pos.isLt; omega⟩
  have hload (env : ⟪kernel8.Γ⟫) :
      Operation.load (%22 : Dst kernel8.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64))))) env s =
          .value (env[%22 := .value (WordWindow.word bits (pos.val / 64))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hlow := low_shift (WordWindow.word bits (pos.val / 64)) pos
  by_cases hcross : pos.val % 64 < 56 <;>
    simp [BasicBlock.run, kernel8.bb2, loadInput8, loadResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
      EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
      hindex, hbit, hscale, hcmp, hgep, hload, hlow, hcross,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def crossInput5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256) (low : BitVec 64) :
    ⟪kernel5.Γ⟫ :=
  E[%4 := .value 0#64, %6 := .value 63#64, %8 := .value 8#64,
    %19 := .value (BitVec.ofNat 64 pos.val),
    %23 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))), %25 := .value low]

def crossResult5 (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) : ⟪kernel5.Γ⟫ :=
  (crossInput5 E scratch pos low)[%26 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))),
    %27 := .value (WordWindow.word bits (pos.val / 64 + 1)),
    %28 := .value (-BitVec.ofNat 64 pos.val),
    %29 := .value (BitVec.ofNat 64 (64 - pos.val % 64)),
    %30 := .value (WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)),
    %31 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

theorem kernel5_cross_block (E : ⟪kernel5.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (hcross : ¬pos.val % 64 < 59) :
    kernel5.bb3.run kernel5.blockParams (crossInput5 E scratch pos low) s =
      .value (((crossResult5 E scratch pos low bits)[%32 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)],
        .inr 4), s) := by
  have hbase := hbuffer.slice (8 * (pos.val / 64)) 16 (by have := pos.isLt; omega)
  have hgep := hbase.gep 8 (by decide)
  simp only [Pointer.add_add, next_word_offset pos, Int.cast_ofNat_Int] at hgep
  have hscale : Operation.gepInboundsIndex 1 (.value 8#64) = .value (8 : Int) := by decide +kernel
  have hfits := hbuffer.fits_at (8 * (pos.val / 64 + 1)) 8 (by have := pos.isLt; omega)
  have hread := Memory.read_word hbuffer bits hbits
    ⟨pos.val / 64 + 1, by have := pos.isLt; omega⟩
  have hload (env : ⟪kernel5.Γ⟫) :
      Operation.load (%27 : Dst kernel5.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1))))) env s =
          .value (env[%27 := .value (WordWindow.word bits (pos.val / 64 + 1))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hneg := cursor_negate pos
  have hcount := cursor_cross_shift 5 (Or.inl rfl) pos hcross
  have hs := (cross_word_shift_safe pos.val 5 (Or.inl rfl) hcross).2
  have hhigh := high_shift (WordWindow.word bits (pos.val / 64 + 1)) _ hs
  simp [BasicBlock.run, kernel5.bb3, crossInput5, crossResult5,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hscale, hgep, hload, hneg, hcount, hhigh, Operation.or,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def crossInput8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256) (low : BitVec 64) :
    ⟪kernel8.Γ⟫ :=
  E[%4 := .value 0#64, %6 := .value 63#64, %8 := .value 8#64,
    %17 := .value (BitVec.ofNat 64 pos.val),
    %21 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64)))), %23 := .value low]

def crossResult8 (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) : ⟪kernel8.Γ⟫ :=
  (crossInput8 E scratch pos low)[%24 := .value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1)))),
    %25 := .value (WordWindow.word bits (pos.val / 64 + 1)),
    %26 := .value (-BitVec.ofNat 64 pos.val),
    %27 := .value (BitVec.ofNat 64 (64 - pos.val % 64)),
    %28 := .value (WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)),
    %29 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)]

theorem kernel8_cross_block (E : ⟪kernel8.Γ⟫) (scratch : Pointer) (pos : Fin 256)
    (low : BitVec 64) (bits : BitVec 320) (s : GlobalState)
    (hbuffer : Buffer s.mem scratch 40) (hbits : s.mem.readAt scratch 320 = bits)
    (hcross : ¬pos.val % 64 < 56) :
    kernel8.bb3.run kernel8.blockParams (crossInput8 E scratch pos low) s =
      .value (((crossResult8 E scratch pos low bits)[%30 := .value ((WordWindow.word bits (pos.val / 64 + 1) <<< (64 - pos.val % 64)) ||| low)],
        .inr 4), s) := by
  have hbase := hbuffer.slice (8 * (pos.val / 64)) 16 (by have := pos.isLt; omega)
  have hgep := hbase.gep 8 (by decide)
  simp only [Pointer.add_add, next_word_offset pos, Int.cast_ofNat_Int] at hgep
  have hscale : Operation.gepInboundsIndex 1 (.value 8#64) = .value (8 : Int) := by decide +kernel
  have hfits := hbuffer.fits_at (8 * (pos.val / 64 + 1)) 8 (by have := pos.isLt; omega)
  have hread := Memory.read_word hbuffer bits hbits
    ⟨pos.val / 64 + 1, by have := pos.isLt; omega⟩
  have hload (env : ⟪kernel8.Γ⟫) :
      Operation.load (%25 : Dst kernel8.Γ (.bv 64))
        (.value (scratch.add (BitVec.ofNat 64 (8 * (pos.val / 64 + 1))))) env s =
          .value (env[%25 := .value (WordWindow.word bits (pos.val / 64 + 1))], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 64) = _
    rw [hread]
  have hneg := cursor_negate pos
  have hcount := cursor_cross_shift 8 (Or.inr rfl) pos hcross
  have hs := (cross_word_shift_safe pos.val 8 (Or.inr rfl) hcross).2
  have hhigh := high_shift (WordWindow.word bits (pos.val / 64 + 1)) _ hs
  simp [BasicBlock.run, kernel8.bb3, crossInput8, crossResult8,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, GepIndex.inboundsOffset,
    EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq, PoisonOr.value_bind, mlir_env,
    hscale, hgep, hload, hneg, hcount, hhigh, Operation.or,
    Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

def evenInput5 (E : ⟪kernel5.Γ⟫) (pos : Fin 256) : ⟪kernel5.Γ⟫ :=
  E[%2 := .value 256#64, %10 := .value 1#64, %19 := .value (BitVec.ofNat 64 pos.val)]

def evenResult5 (E : ⟪kernel5.Γ⟫) (pos : Fin 256) : ⟪kernel5.Γ⟫ :=
  (evenInput5 E pos)[%37 := .value (BitVec.ofNat 64 (pos.val + 1)),
    %38 := .value (if pos.val + 1 = 256 then 1#1 else 0#1)]

/-- Exact execution of the width-five even block, including the final 255→256
exit and the otherwise taken backedge. Memory and carry remain unchanged. -/
theorem kernel5_even_block (E : ⟪kernel5.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    kernel5.bb5.run kernel5.blockParams (evenInput5 E pos) s =
      if pos.val + 1 = 256 then
        .value ((evenResult5 E pos, .inr 7), s)
      else .value (((evenResult5 E pos)[%19 := .value (BitVec.ofNat 64 (pos.val + 1))],
        .inr 2), s) := by
  obtain ⟨hadd, hcmp⟩ := cursor_one pos
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, kernel5.bb5, evenInput5, evenResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hadd, hcmp, hend,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem kernel5_even_run (E : ⟪kernel5.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    kernel5.runFrom (evenInput5 E pos) 5 s =
      if pos.val + 1 = 256 then .value (.nil, s)
      else kernel5.runFrom
        ((evenResult5 E pos)[%19 := .value (BitVec.ofNat 64 (pos.val + 1))]) 2 s := by
  rw [Func.runFrom_eq, show kernel5.blocks 5 = kernel5.bb5 from rfl, kernel5_even_block]
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, if_true, if_false, PoisonOr.value_bind, Func.continue]
  exact kernel5_exit_run _ s

def evenInput8 (E : ⟪kernel8.Γ⟫) (pos : Fin 256) : ⟪kernel8.Γ⟫ :=
  E[%2 := .value 256#64, %10 := .value 1#64, %17 := .value (BitVec.ofNat 64 pos.val)]

def evenResult8 (E : ⟪kernel8.Γ⟫) (pos : Fin 256) : ⟪kernel8.Γ⟫ :=
  (evenInput8 E pos)[%35 := .value (BitVec.ofNat 64 (pos.val + 1)),
    %36 := .value (if pos.val + 1 = 256 then 1#1 else 0#1)]

theorem kernel8_even_block (E : ⟪kernel8.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    kernel8.bb5.run kernel8.blockParams (evenInput8 E pos) s =
      if pos.val + 1 = 256 then
        .value ((evenResult8 E pos, .inr 7), s)
      else .value (((evenResult8 E pos)[%17 := .value (BitVec.ofNat 64 (pos.val + 1))],
        .inr 2), s) := by
  obtain ⟨hadd, hcmp⟩ := cursor_one pos
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, kernel8.bb5, evenInput8, evenResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hadd, hcmp, hend,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem kernel8_even_run (E : ⟪kernel8.Γ⟫) (pos : Fin 256) (s : GlobalState) :
    kernel8.runFrom (evenInput8 E pos) 5 s =
      if pos.val + 1 = 256 then .value (.nil, s)
      else kernel8.runFrom
        ((evenResult8 E pos)[%17 := .value (BitVec.ofNat 64 (pos.val + 1))]) 2 s := by
  rw [Func.runFrom_eq, show kernel8.blocks 5 = kernel8.bb5 from rfl, kernel8_even_block]
  by_cases hend : pos.val + 1 = 256 <;>
    simp only [hend, if_true, if_false, PoisonOr.value_bind, Func.continue]
  exact kernel8_exit_run _ s

def mask5 (raw : BitVec 64) : Fin 32 :=
  ⟨(raw &&& 31#64).toNat, by
    change raw.toNat &&& 31 < 32
    exact Nat.lt_succ_of_le Nat.and_le_right⟩

def mask8 (raw : BitVec 64) : Fin 256 :=
  ⟨(raw &&& 255#64).toNat, by
    change raw.toNat &&& 255 < 256
    exact Nat.lt_succ_of_le Nat.and_le_right⟩

def sum5 (raw : Fin 32) (carry : Fin 2) : Fin 33 :=
  ⟨raw.val + carry.val, by have := raw.isLt; have := carry.isLt; omega⟩

def sum8 (raw : Fin 256) (carry : Fin 2) : Fin 257 :=
  ⟨raw.val + carry.val, by have := raw.isLt; have := carry.isLt; omega⟩

theorem mask5_instruction (raw : BitVec 64) :
    Operation.and (.value raw) (.value 31#64) = .value (BitVec.ofNat 64 (mask5 raw).val) := by
  simp only [mask5, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Operation.and, PoisonOr.value_bind, PoisonOr.pure_def]

theorem mask8_instruction (raw : BitVec 64) :
    Operation.and (.value raw) (.value 255#64) = .value (BitVec.ofNat 64 (mask8 raw).val) := by
  simp only [mask8, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Operation.and, PoisonOr.value_bind, PoisonOr.pure_def]

theorem window_arithmetic5 : ∀ raw : Fin 32, ∀ carry : Fin 2,
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 raw.val))
      (.value (BitVec.ofNat 64 carry.val)) = .value (BitVec.ofNat 64 (sum5 raw carry).val) ∧
    Operation.and (.value (BitVec.ofNat 64 (sum5 raw carry).val)) (.value 1#64) =
      .value (BitVec.ofNat 64 ((sum5 raw carry).val % 2)) ∧
    Operation.icmp .eq (.value (BitVec.ofNat 64 ((sum5 raw carry).val % 2))) (.value 0#64) =
      .value (if (sum5 raw carry).val % 2 = 0 then 1#1 else 0#1) := by
  decide +kernel

theorem window_arithmetic8 : ∀ raw : Fin 256, ∀ carry : Fin 2,
    Operation.add {nsw := true, nuw := true} (.value (BitVec.ofNat 64 raw.val))
      (.value (BitVec.ofNat 64 carry.val)) = .value (BitVec.ofNat 64 (sum8 raw carry).val) ∧
    Operation.and (.value (BitVec.ofNat 64 (sum8 raw carry).val)) (.value 1#64) =
      .value (BitVec.ofNat 64 ((sum8 raw carry).val % 2)) ∧
    Operation.icmp .eq (.value (BitVec.ofNat 64 ((sum8 raw carry).val % 2))) (.value 0#64) =
      .value (if (sum8 raw carry).val % 2 = 0 then 1#1 else 0#1) := by
  decide +kernel

def windowInput5 (E : ⟪kernel5.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪kernel5.Γ⟫ :=
  E[%4 := .value 0#64, %9 := .value 31#64, %10 := .value 1#64,
    %18 := .value (BitVec.ofNat 64 carry.val), %32 := .value raw]

def windowResult5 (E : ⟪kernel5.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪kernel5.Γ⟫ :=
  (windowInput5 E raw carry)[%33 := .value (BitVec.ofNat 64 (mask5 raw).val),
    %34 := .value (BitVec.ofNat 64 (sum5 (mask5 raw) carry).val),
    %35 := .value (BitVec.ofNat 64 ((sum5 (mask5 raw) carry).val % 2)),
    %36 := .value (if (sum5 (mask5 raw) carry).val % 2 = 0 then 1#1 else 0#1)]

/-- The imported mask/carry/parity block is total for every raw word and the
one-bit carry invariant. Both overflow promises and its exact edge are proved. -/
theorem kernel5_window_block (E : ⟪kernel5.Γ⟫) (raw : BitVec 64) (carry : Fin 2)
    (s : GlobalState) :
    kernel5.bb4.run kernel5.blockParams (windowInput5 E raw carry) s =
      .value ((windowResult5 E raw carry,
        .inr (if (sum5 (mask5 raw) carry).val % 2 = 0 then 5 else 6)), s) := by
  have hmask := mask5_instruction raw
  obtain ⟨hadd, hlow, hcmp⟩ := window_arithmetic5 (mask5 raw) carry
  by_cases heven : (sum5 (mask5 raw) carry).val % 2 = 0 <;>
    simp only [heven, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, kernel5.bb4, windowInput5, windowResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hmask, hadd, hlow, hcmp, heven,
      Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def windowInput8 (E : ⟪kernel8.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪kernel8.Γ⟫ :=
  E[%4 := .value 0#64, %9 := .value 255#64, %10 := .value 1#64,
    %16 := .value (BitVec.ofNat 64 carry.val), %30 := .value raw]

def windowResult8 (E : ⟪kernel8.Γ⟫) (raw : BitVec 64) (carry : Fin 2) : ⟪kernel8.Γ⟫ :=
  (windowInput8 E raw carry)[%31 := .value (BitVec.ofNat 64 (mask8 raw).val),
    %32 := .value (BitVec.ofNat 64 (sum8 (mask8 raw) carry).val),
    %33 := .value (BitVec.ofNat 64 ((sum8 (mask8 raw) carry).val % 2)),
    %34 := .value (if (sum8 (mask8 raw) carry).val % 2 = 0 then 1#1 else 0#1)]

theorem kernel8_window_block (E : ⟪kernel8.Γ⟫) (raw : BitVec 64) (carry : Fin 2)
    (s : GlobalState) :
    kernel8.bb4.run kernel8.blockParams (windowInput8 E raw carry) s =
      .value ((windowResult8 E raw carry,
        .inr (if (sum8 (mask8 raw) carry).val % 2 = 0 then 5 else 6)), s) := by
  have hmask := mask8_instruction raw
  obtain ⟨hadd, hlow, hcmp⟩ := window_arithmetic8 (mask8 raw) carry
  by_cases heven : (sum8 (mask8 raw) carry).val % 2 = 0 <;>
    simp only [heven, ite_true, ite_false] at hcmp <;>
    simp [BasicBlock.run, kernel8.bb4, windowInput8, windowResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, EffectM.bind_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hmask, hadd, hlow, hcmp, heven,
      Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil]

def high5 (window : Fin 33) : BitVec 1 := if 15 < window.val then 1#1 else 0#1
def bias5 (window : Fin 33) : BitVec 8 := if 15 < window.val then -32#8 else 0#8
def byte5 (window : Fin 33) : BitVec 8 :=
  BitVec.ofInt 8 (if 15 < window.val then (window.val : Int) - 32 else window.val)
def carry5 (window : Fin 33) : BitVec 64 := if 15 < window.val then 1#64 else 0#64

/-- Every instruction on the five-bit store path is defined for the complete
reachable masked-window-plus-carry range, including either parity. -/
theorem store_arithmetic5 : ∀ window : Fin 33,
    Operation.icmp .ugt (.value (BitVec.ofNat 64 window.val)) (.value 15#64) = .value (high5 window) ∧
    Operation.trunc {nsw := true, nuw := true} (.value (BitVec.ofNat 64 window.val)) =
      .value (BitVec.ofNat 8 window.val) ∧
    Operation.select (τ := .bv 8) (.value (high5 window)) (.value (-32#8)) (.value 0#8) =
      .value (bias5 window) ∧
    Operation.add {nsw := true} (.value (bias5 window)) (.value (BitVec.ofNat 8 window.val)) =
      .value (byte5 window) ∧
    Operation.zext false (.value (high5 window)) = .value (carry5 window) := by
  decide +kernel

def storeInput5 (E : ⟪kernel5.Γ⟫) (pos : Fin 256) (window : Fin 33) : ⟪kernel5.Γ⟫ :=
  E[%1 := .value 0#8, %11 := .value 15#64, %12 := .value (-32 : BitVec 8),
    %13 := .value 5#64, %14 := .value 251#64, %19 := .value (BitVec.ofNat 64 pos.val),
    %34 := .value (BitVec.ofNat 64 window.val)]

def storeResult5 (E : ⟪kernel5.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 33) :
    ⟪kernel5.Γ⟫ :=
  (storeInput5 E pos window)[%39 := .value (high5 window),
    %40 := .value (BitVec.ofNat 8 window.val), %41 := .value (bias5 window),
    %42 := .value (byte5 window), %43 := .value (carry5 window),
    %44 := .value (out.add (BitVec.ofNat 64 pos.val)),
    %45 := .value (BitVec.ofNat 64 (pos.val + 5)),
    %46 := .value (if pos.val < 251 then 1#1 else 0#1)]

/-- The original width-five store block writes exactly one byte and returns
the concrete carry/cursor edge. The GEP and store are justified by the outer
256-byte allocation, with no index-safety premise on the digit. -/
theorem kernel5_store_block (E : ⟪kernel5.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 33) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%arg0) = .value out) :
    kernel5.bb6.run kernel5.blockParams (storeInput5 E pos window) s =
      if pos.val < 251 then
        .value (((storeResult5 E out pos window)[%17 := .value (BitVec.ofNat 64 (pos.val + 5)), %18 := .value (carry5 window)],
          .inr 1), {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)})
      else .value ((storeResult5 E out pos window, .inr 7),
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}) := by
  obtain ⟨hhigh, htrunc, hselect, hdigit, hcarry⟩ := store_arithmetic5 window
  change E.args 0 = .value out at hout
  change Operation.select (τ := .bv 8) (.value (high5 window)) (.value 224#8) (.value 0#8) =
    .value (bias5 window) at hselect
  obtain ⟨hadd, hcmp⟩ := cursor_five pos
  have hscale := cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hstore (env : ⟪kernel5.Γ⟫) := run_store (env := env) hfits
    (show Ty.flatten (.bv 8) (.value (byte5 window)) = .value (byte5 window) from rfl)
  by_cases hnext : pos.val < 251 <;>
    simp [BasicBlock.run, kernel5.bb6, storeInput5, storeResult5,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, UnOp.compute,
      TernOp.compute, GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hout, hhigh, htrunc,
      hselect, hdigit, hcarry, hscale, hgep, hstore, hadd, hcmp, hnext,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem kernel5_store_run (E : ⟪kernel5.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 33) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%arg0) = .value out) :
    kernel5.runFrom (storeInput5 E pos window) 6 s =
      if pos.val < 251 then kernel5.runFrom
        ((storeResult5 E out pos window)[%17 := .value (BitVec.ofNat 64 (pos.val + 5)), %18 := .value (carry5 window)]) 1
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}
      else .value (.nil,
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte5 window)}) := by
  rw [Func.runFrom_eq, show kernel5.blocks 6 = kernel5.bb6 from rfl,
    kernel5_store_block E out pos window s hbuffer hout]
  by_cases hnext : pos.val < 251 <;>
    simp only [hnext, if_true, if_false, PoisonOr.value_bind, Func.continue]
  exact kernel5_exit_run _ _

def high8 (window : Fin 257) : BitVec 1 := if 127 < window.val then 1#1 else 0#1
def byte8 (window : Fin 257) : BitVec 8 := BitVec.ofNat 8 window.val
def carry8 (window : Fin 257) : BitVec 64 := if 127 < window.val then 1#64 else 0#64

theorem store_arithmetic8 : ∀ window : Fin 257,
    Operation.icmp .ugt (.value (BitVec.ofNat 64 window.val)) (.value 127#64) = .value (high8 window) ∧
    Operation.trunc {} (.value (BitVec.ofNat 64 window.val)) = .value (byte8 window) ∧
    Operation.zext false (.value (high8 window)) = .value (carry8 window) := by
  decide +kernel

def storeInput8 (E : ⟪kernel8.Γ⟫) (pos : Fin 256) (window : Fin 257) : ⟪kernel8.Γ⟫ :=
  E[%8 := .value 8#64, %11 := .value 127#64, %12 := .value 248#64,
    %17 := .value (BitVec.ofNat 64 pos.val), %32 := .value (BitVec.ofNat 64 window.val)]

def storeResult8 (E : ⟪kernel8.Γ⟫) (out : Pointer) (pos : Fin 256) (window : Fin 257) :
    ⟪kernel8.Γ⟫ :=
  (storeInput8 E pos window)[%37 := .value (high8 window), %38 := .value (byte8 window),
    %39 := .value (carry8 window), %40 := .value (out.add (BitVec.ofNat 64 pos.val)),
    %41 := .value (BitVec.ofNat 64 (pos.val + 8)),
    %42 := .value (if pos.val < 248 then 1#1 else 0#1)]

theorem kernel8_store_block (E : ⟪kernel8.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 257) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%arg0) = .value out) :
    kernel8.bb6.run kernel8.blockParams (storeInput8 E pos window) s =
      if pos.val < 248 then
        .value (((storeResult8 E out pos window)[%15 := .value (BitVec.ofNat 64 (pos.val + 8)), %16 := .value (carry8 window)],
          .inr 1), {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)})
      else .value ((storeResult8 E out pos window, .inr 7),
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}) := by
  obtain ⟨hhigh, hdigit, hcarry⟩ := store_arithmetic8 window
  change E.args 0 = .value out at hout
  obtain ⟨hadd, hcmp⟩ := cursor_eight pos
  have hscale := cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hstore (env : ⟪kernel8.Γ⟫) := run_store (env := env) hfits
    (show Ty.flatten (.bv 8) (.value (byte8 window)) = .value (byte8 window) from rfl)
  by_cases hnext : pos.val < 248 <;>
    simp [BasicBlock.run, kernel8.bb6, storeInput8, storeResult8,
      List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, UnOp.compute,
      GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq,
      EffectM.pure_eq, PoisonOr.value_bind, mlir_env, hout, hhigh, hdigit, hcarry,
      hscale, hgep, hstore, hadd, hcmp, hnext,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil]

theorem kernel8_store_run (E : ⟪kernel8.Γ⟫) (out : Pointer) (pos : Fin 256)
    (window : Fin 257) (s : GlobalState) (hbuffer : Buffer s.mem out 256)
    (hout : E.read (%arg0) = .value out) :
    kernel8.runFrom (storeInput8 E pos window) 6 s =
      if pos.val < 248 then kernel8.runFrom
        ((storeResult8 E out pos window)[%15 := .value (BitVec.ofNat 64 (pos.val + 8)), %16 := .value (carry8 window)]) 1
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}
      else .value (.nil,
        {s with mem := s.mem.storeAt (out.add (BitVec.ofNat 64 pos.val)) (byte8 window)}) := by
  rw [Func.runFrom_eq, show kernel8.blocks 6 = kernel8.bb6 from rfl,
    kernel8_store_block E out pos window s hbuffer hout]
  by_cases hnext : pos.val < 248 <;>
    simp only [hnext, if_true, if_false, PoisonOr.value_bind, Func.continue]
  exact kernel8_exit_run _ _

end Agave.Ed25519.NAF.RIR
