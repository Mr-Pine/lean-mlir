import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionContext
import SSA.Projects.RIR.Run.Tactic

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
@[simp] theorem blockParams_1 : program.blockParams 1 = .nil := rfl
@[simp] theorem blockParams_2 : program.blockParams 2 = .nil := rfl
@[simp] theorem blockParams_4 : program.blockParams 4 = .nil := rfl
@[simp] theorem blockParams_5 : program.blockParams 5 = .nil := rfl
@[simp] theorem blockParams_6 : program.blockParams 6 = .nil := rfl
@[simp] theorem blockParams_7 : program.blockParams 7 = .nil := rfl
@[simp] theorem blockParams_3 : program.blockParams 3 = .cons (%35) (.cons (%36) .nil) := rfl

def shortEnv (E : Env program.Γ) (ctx : Pointer) (n : BitVec 64) : Env program.Γ :=
  E[%32 := .value (ctx.add 64#64), %33 := .value (n.setWidth 8),
    %34 := .value (64 + n.setWidth 8)]

def shortState (s : GlobalState) (ctx msg : Pointer) (n : BitVec 64) : GlobalState :=
  {s with mem := appendPending s.mem ctx msg 64 n.toNat}

/-- The imported short-message block copies exactly the message bytes after
the encoded R and A, then updates the checked one-byte buffer count. -/
theorem short_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (ctx msg : Pointer) (n : BitVec 64)
    (hctx : E.read (%18) = .value ctx) (hmsg : E.read (%arg3) = .value msg)
    (hn : E.read (%arg4) = .value n) (h64 : E.read (%27) = .value 64#64)
    (hcount : E.read (%26) = .value 64#8)
    (hcountPtr : E.read (%25) = .value (ctx.add 127#64))
    (hlive : SmallRange s.mem ctx 208) (hinput : SmallRange s.mem msg n.toNat)
    (hshort : n.toNat < 64) (hne : ctx.id ≠ msg.id) :
    (program p g).runFrom E 2 s =
      (program p g).runFrom (shortEnv E ctx n) 7 (shortState s ctx msg n) := by
  change E.args 3 = .value msg at hmsg
  change E.args 4 = .value n at hn
  have hg : Operation.gepInboundsLive s.mem (.value ctx) [.value (64 : Int)] =
      .value (ctx.add 64#64) := hlive.gep (k := 64) (by decide)
  have hd : (Range.of (ctx.add 64#64) (8 * n.toNat)).Disjoint
      (Range.of msg (8 * n.toNat)) := Or.inl hne
  have hf : Fits s.mem (ctx.add 64#64) (8 * n.toNat) :=
    hlive.fits_add (k := 64) (count := n.toNat) (by omega)
  have hc : Fits (s.mem.storeAt (ctx.add 64#64) (s.mem.readAt msg (8 * n.toNat)))
      (ctx.add 127#64) 8 := Fits.storeAt (context_count_fits hlive)
  have ht := trunc8_flags n (by omega)
  have ha : Operation.add { nuw := true } (.value 64#8) (.value (n.setWidth 8)) =
      .value (64#8 + n.setWidth 8) := short_buffer_add_flags n hshort
  have hv : BitVec.ofNat 8 (64 + n.toNat) = 64#8 + n.setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    have hncount : (64#8 + n.setWidth 8).toNat = 64 + n.toNat := short_buffer_count n hshort
    rw [hncount]
    exact Nat.mod_eq_of_lt (by omega)
  have hb : program.bb2.run program.blockParams E s =
      .value ((shortEnv E ctx n, .inr 7), shortState s ctx msg n) := by
    simp [BasicBlock.run, program.bb2, shortEnv, shortState, appendPending,
      List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy, Operation.store,
      UnOp.compute, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      Exit.run, Jump.run, Regs.read_nil, Env.writeMany_nil,
      GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
      hctx, hmsg, hn, h64, hcount, hcountPtr, hg, hd, hf, hc, hinput.fits, ht, ha, hv,
      throwUBIf]
  rw [Func.runFrom_eq]
  change ((program.bb2).run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

/-- The initial pending count is 64, so the imported zero-count shortcut is
unreachable; the long path necessarily visits the first-block fill. -/
theorem nonempty_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (hcount : E.read (%26) = .value 64#8)
    (hzero : E.read (%10) = .value 0#8) :
    (program p g).runFrom E 1 s =
      (program p g).runFrom (E[%31 := .value 0#1]) 4 s := by
  have hb : program.bb1.run program.blockParams E s =
      .value ((E[%31 := .value 0#1], .inr 4), s) := by
    simp [BasicBlock.run, program.bb1, List.foldlM_cons, List.foldlM_nil, Instr.run,
      BinOp.compute, Operation.icmp, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
      hcount, hzero]
  rw [Func.runFrom_eq]
  change (program.bb1.run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

def tailEnv (E : Env program.Γ) (n : BitVec 64) : Env program.Γ :=
  E[%52 := .value (n.setWidth 8)]

def tailState (s : GlobalState) (ctx msg : Pointer) (n : BitVec 64) : GlobalState :=
  {s with mem := finishContext s.mem ctx msg n.toNat}

/-- The imported tail block restores the length byte and copies exactly the
residual bytes; this also covers a zero-length residual. -/
theorem tail_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (ctx msg : Pointer) (n : BitVec 64)
    (hctx : E.read (%18) = .value ctx) (hmsg : E.read (%40) = .value msg)
    (hn : E.read (%39) = .value n)
    (hcountPtr : E.read (%25) = .value (ctx.add 127#64))
    (hlive : SmallRange s.mem ctx 208) (hinput : SmallRange s.mem msg n.toNat)
    (hshort : n.toNat < 128) (hne : ctx.id ≠ msg.id) :
    (program p g).runFrom E 6 s =
      (program p g).runFrom (tailEnv E n) 7 (tailState s ctx msg n) := by
  have ht := trunc8_flags n hshort
  have hf : Fits s.mem ctx (8 * n.toNat) := (smallRange_mono hlive (by omega)).fits
  have hd : (Range.of ctx (8 * n.toNat)).Disjoint (Range.of msg (8 * n.toNat)) :=
    Or.inl hne
  have hc : Fits s.mem (ctx.add 127#64) 8 := context_count_fits hlive
  have hv : BitVec.ofNat 8 n.toNat = n.setWidth 8 := by rfl
  have hb : program.bb6.run program.blockParams E s =
      .value ((tailEnv E n, .inr 7), tailState s ctx msg n) := by
    simp [BasicBlock.run, program.bb6, tailEnv, tailState, finishContext,
      List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy, Operation.store,
      UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
      Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
      hctx, hmsg, hn, hcountPtr, hd, hc, hf, hinput.fits, ht, hv, throwUBIf]
  rw [Func.runFrom_eq]
  change (program.bb6.run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

def sliceEnv (E : Env program.Γ) (src : Pointer) (n : BitVec 64) : Env program.Γ :=
  E[%37 := .value (n >>> 7), %38 := .value (n &&& 9223372036854775680),
    %39 := .value (n &&& 127), %40 := .value (src.add (n &&& 9223372036854775680)),
    %41 := .value (BitVec.ofBool ((n >>> 7) == 0))]

/-- Exact full-block/tail split, with the flagged dynamic pointer arithmetic
proved from the live input slice. -/
theorem slice_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s : GlobalState) (src : Pointer) (n : BitVec 64)
    (hn : E.read (%35) = .value n) (hsrc : E.read (%36) = .value src)
    (h7 : E.read (%13) = .value 7#64)
    (hmask : E.read (%14) = .value 9223372036854775680#64)
    (h127 : E.read (%2) = .value 127#64) (h0 : E.read (%15) = .value 0#64)
    (hr : SmallRange s.mem src n.toNat) :
    (program p g).runFrom E 3 s =
      (program p g).runFrom (sliceEnv E src n) (if n >>> 7 = 0 then 6 else 5) s := by
  have hsmall := smallRange_length_lt hr
  have hoff := full_block_offset n hsmall
  have hbound : (n &&& 9223372036854775680#64).toNat ≤ n.toNat := by
    change (n &&& 9223372036854775680#64).toNat = 128 * (n.toNat / 128) at hoff
    omega
  have hi : (n &&& 9223372036854775680).toInt =
      ((n &&& 9223372036854775680).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have hg : Operation.gepInboundsLive s.mem (.value src)
      [.value ((n &&& 9223372036854775680).toInt)] =
      .value (src.add (n &&& 9223372036854775680)) := by
    rw [hi]
    simpa using hr.gep hbound
  have hindex : Operation.gepInboundsIndex 1 (.value (n &&& 9223372036854775680#64)) =
      .value (n &&& 9223372036854775680#64).toInt := by
    have hsr : Operation.GepSignedRange (n &&& 9223372036854775680#64).toInt := by
      change -(2 ^ 63 : Int) ≤ (n &&& 9223372036854775680#64).toInt ∧
        (n &&& 9223372036854775680#64).toInt < 2 ^ 63
      rw [show (n &&& 9223372036854775680#64).toInt =
        ((n &&& 9223372036854775680#64).toNat : Int) from hi]
      constructor <;> omega
    simpa using Operation.gepInboundsIndex_eq 1 (n &&& 9223372036854775680#64) hsr
      (by simpa using hsr) (BitVec.isLt _) (by simpa only [BitVec.ofInt_toInt, Nat.mul_one] using (n &&& 9223372036854775680#64).isLt)
  have hg' : Operation.gepInboundsLive s.mem (.value src)
      [.value (n &&& 9223372036854775680#64).toInt] =
      .value (src.add (n &&& 9223372036854775680#64)) := hg
  simp at hg'
  have hs : Operation.lshr false (.value n) (.value 7#64) = .value (n >>> 7) := block_shift_defined n
  have hb : program.bb3.run program.blockParams E s =
      .value ((sliceEnv E src n, .inr (if n >>> 7 = 0 then 6 else 5)), s) := by
    by_cases hz : n >>> 7 = 0#64 <;>
      simp [BasicBlock.run, program.bb3, sliceEnv,
        List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute, Operation.icmp,
        Operation.and, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
        Exit.run, Jump.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
        GepIndex.inboundsOffset, hindex,
        hn, hsrc, h7, hmask, h127, h0, hg', hs, hz, ofBool_eq_one_iff]
  rw [Func.runFrom_eq]
  change (program.bb3.run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

def bulkEnv (E : Env program.Γ) (ctx : Pointer) (q : BitVec 64) (old : BitVec 128) :
    Env program.Γ :=
  E[%48 := .value (q.setWidth 128), %49 := .value (ctx.add 192#64),
    %50 := .value old, %51 := .value (old + q.setWidth 128)]

/-- The direct-block path executes exactly one call with the quotient count,
after adding that count to the u128 full-block counter. -/
theorem bulk_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s after : GlobalState) (ctx src : Pointer) (n : BitVec 64)
    (hctx : E.read (%18) = .value ctx) (hsrc : E.read (%36) = .value src)
    (hchain : E.read (%24) = .value (ctx.add 128#64))
    (h192 : E.read (%7) = .value 192#64)
    (hn : E.read (%37) = .value (n >>> 7))
    (hlive : SmallRange s.mem ctx 208) (hsmall : n.toNat < 2 ^ 63)
    (hcall : p.sha512Compress (.cons (.value (ctx.add 128#64)) (.cons (.value src)
      (.cons (.value (n >>> 7)) .nil))) (advanceCount s ctx (n >>> 7)) =
        .value (.nil, after)) :
    (program p g).runFrom E 5 s =
      (program p g).runFrom (bulkEnv E ctx (n >>> 7) (s.mem.readAt (ctx.add 192#64) 128))
        6 after := by
  have hg : Operation.gepInboundsLive s.mem (.value ctx) [.value (192 : Int)] =
      .value (ctx.add 192#64) := hlive.gep (k := 192) (by decide)
  have hf : Fits s.mem (ctx.add 192#64) 128 := context_blocks_fits hlive
  have hz := block_count_zext_defined n hsmall
  simp only [advanceCount] at hcall
  change p.sha512Compress (.cons (.value (ctx.add 128#64)) (.cons (.value src)
    (.cons (.value (n >>> 7)) .nil)))
    {s with mem :=
      s.mem.storeAt (ctx.add 192#64) (s.mem.readAt (ctx.add 192#64) 128 + (n >>> 7).setWidth 128)} =
      .value (.nil, after) at hcall
  simp only [BitVec.setWidth_ushiftRight (by decide : 64 ≤ 128)] at hcall
  have hb : (program.bb5 p).run program.blockParams E s =
      .value ((bulkEnv E ctx (n >>> 7) (s.mem.readAt (ctx.add 192#64) 128), .inr 6), after) := by
    simp [BasicBlock.run, program.bb5, bulkEnv,
      List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.load, Operation.store,
      UnOp.compute, BinOp.compute, Operation.add, EffectM.bind_eq, EffectM.pure_eq,
      mlir_effect, mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_nil, GepIndex.inboundsOffset, Operation.gepInboundsIndex,
      Operation.GepSignedRange, hctx, hsrc, hchain, h192, hn, hg, hf, hz, hcall, throwUBIf]
  rw [Func.runFrom_eq]
  change ((program.bb5 p).run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

def firstFill (s : GlobalState) (ctx msg : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt (ctx.add 64#64) (s.mem.readAt msg 512)}

def firstEnv (E : Env program.Γ) (ctx msg : Pointer) (n : BitVec 64) (old : BitVec 128) :
    Env program.Γ :=
  E[%42 := .value (msg.add 64#64), %43 := .value (n - 64), %44 := .value (ctx.add 64#64),
    %45 := .value (ctx.add 192#64), %46 := .value old, %47 := .value (old + 1),
    %35 := .value (n - 64), %36 := .value (msg.add 64#64)]

/-- The first-block path fills the 64-byte gap after R and A, increments the
counter once, and invokes compression on the full context-buffer block. -/
theorem first_block (p : Primitives) (g : Globals) (E : Env program.Γ)
    (s after : GlobalState) (ctx msg : Pointer) (n : BitVec 64)
    (hctx : E.read (%18) = .value ctx) (hmsg : E.read (%arg3) = .value msg)
    (hn : E.read (%arg4) = .value n)
    (hchain : E.read (%24) = .value (ctx.add 128#64))
    (h64 : E.read (%27) = .value 64#64) (hgap : E.read (%29) = .value 64#64)
    (h192 : E.read (%7) = .value 192#64)
    (h1 : E.read (%11) = .value 1#128) (hone : E.read (%12) = .value 1#64)
    (hlive : SmallRange s.mem ctx 208) (hinput : SmallRange s.mem msg n.toNat)
    (hlong : 64 ≤ n.toNat) (hne : ctx.id ≠ msg.id)
    (hcall : p.sha512Compress (.cons (.value (ctx.add 128#64)) (.cons (.value ctx)
      (.cons (.value 1#64) .nil))) (advanceCount (firstFill s ctx msg) ctx 1#64) =
        .value (.nil, after)) :
    (program p g).runFrom E 4 s =
      (program p g).runFrom
        (firstEnv E ctx msg n ((firstFill s ctx msg).mem.readAt (ctx.add 192#64) 128)) 3 after := by
  change E.args 3 = .value msg at hmsg
  change E.args 4 = .value n at hn
  have hgmsg : Operation.gepInboundsLive s.mem (.value msg) [.value (64 : Int)] =
      .value (msg.add 64#64) := hinput.gep hlong
  have hgctx : Operation.gepInboundsLive s.mem (.value ctx) [.value (64 : Int)] =
      .value (ctx.add 64#64) := hlive.gep (k := 64) (by decide)
  have hg192 : Operation.gepInboundsLive (firstFill s ctx msg).mem (.value ctx)
      [.value (192 : Int)] = .value (ctx.add 192#64) :=
    (hlive.storeAt _ _).gep (k := 192) (by decide)
  have hfs : Fits s.mem msg 512 := (smallRange_mono hinput hlong).fits
  have hfd : Fits s.mem (ctx.add 64#64) 512 := hlive.fits_add (k := 64) (count := 64) (by decide)
  have hfc : Fits (s.mem.storeAt (ctx.add 64#64) (s.mem.readAt msg 512)) (ctx.add 192#64) 128 :=
    context_blocks_fits (hlive.storeAt (ctx.add 64#64) (s.mem.readAt msg 512))
  have hd : (Range.of (ctx.add 64#64) 512).Disjoint (Range.of msg 512) := Or.inl hne
  have hs : Operation.sub { nsw := true, nuw := true } (.value n) (.value 64#64) =
      .value (n - 64#64) := message_sub_flags n hlong (smallRange_length_lt hinput)
  dsimp only [advanceCount, firstFill] at hcall hg192
  change p.sha512Compress (.cons (.value (ctx.add 128#64)) (.cons (.value ctx)
    (.cons (.value 1#64) .nil)))
    {s with mem :=
      (s.mem.storeAt (ctx.add 64#64) (s.mem.readAt msg 512)).storeAt (ctx.add 192#64) ((s.mem.storeAt (ctx.add 64#64) (s.mem.readAt msg 512)).readAt (ctx.add 192#64) 128 + 1#128)} = .value (.nil, after) at hcall
  have hb : (program.bb4 p).run program.blockParams E s =
      .value ((firstEnv E ctx msg n ((firstFill s ctx msg).mem.readAt (ctx.add 192#64) 128),
        .inr 3), after) := by
    simp [BasicBlock.run, program.bb4, firstEnv, firstFill,
      List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy, Operation.load,
      Operation.store, BinOp.compute, Operation.add, EffectM.bind_eq, EffectM.pure_eq,
      mlir_effect, mlir_env, Exit.run, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil,
      GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
      hctx, hmsg, hn, hchain, h64, hgap, h192, h1, hone, hgmsg, hgctx, hg192,
      hfs, hfd, hfc, hd, hs, hcall, throwUBIf]
  rw [Func.runFrom_eq]
  change ((program.bb4 p).run program.blockParams E s >>= fun x =>
    (program p g).continue x.1.1 x.1.2 x.2) = _
  rw [hb]
  rfl

end Agave.Ed25519.Verifier.Execution.Challenge
