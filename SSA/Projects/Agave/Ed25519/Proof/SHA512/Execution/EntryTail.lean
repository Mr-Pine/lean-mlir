import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Control
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

/-- The exact RIR byte-swap expression. Its linkage to the length-field byte
list is a separate byte-order theorem, not an assumption of execution. -/
def swapBytes (value : BitVec w) : BitVec w :=
  (List.range (w / 8)).foldl
    (fun acc i => acc ||| ((value >>> (8 * i)) &&& 0xFF) <<< (w - 8 * (i + 1))) 0

def cloned (s : GlobalState) (src ctx : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt ctx (s.mem.readAt src 1664)}

def paddingCleared (s : GlobalState) (src ctx buffer : Pointer) : GlobalState :=
  {cloned s src ctx with mem := (cloned s src ctx).mem.storeAt buffer 0#1024}

def paddingCopied (s : GlobalState) (src ctx buffer : Pointer) (pending : BitVec 8) : GlobalState :=
  let state := paddingCleared s src ctx buffer
  {state with mem := state.mem.storeAt buffer (state.mem.readAt ctx (8 * pending.toNat))}

def paddingState (s : GlobalState) (src ctx buffer : Pointer) (pending : BitVec 8) : GlobalState :=
  let state := paddingCopied s src ctx buffer pending
  {state with mem := state.mem.storeAt (buffer.add (pending.setWidth 64)) 128#8}

def paddingEnv (E : Env program.Γ) (ctx buffer : Pointer)
    (pending : BitVec 8) (blocks : BitVec 128) : Env program.Γ :=
  E[%151 := .value (ctx.add 128#64), %152 := .value (ctx.add 127#64),
    %153 := .value pending, %154 := .value 1#1,
    %155 := .value (pending.setWidth 128), %156 := .value (ctx.add 192#64),
    %157 := .value blocks, %158 := .value (blocks <<< 10),
    %159 := .value (pending.setWidth 128 <<< 3),
    %160 := .value (BitVec.ofNat 128 (8 * (128 * blocks.toNat + pending.toNat))),
    %161 := .value (swapBytes (BitVec.ofNat 128 (8 * (128 * blocks.toNat + pending.toNat)))),
    %162 := .value (pending.setWidth 64),
    %163 := .value (buffer.add (pending.setWidth 64)),
    %164 := .value (pending.setWidth 64 ^^^ 112#64),
    %165 := .value (BitVec.ofBool (Agave.Ed25519.SHA512.needsTwoBlocks pending))]

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- The entire entry suffix after allocation: context cloning, reads,
checked shifts/OR, byte swap, zero fill, pending-byte copy, 0x80 delimiter,
and the actual XOR cutoff computation. -/
theorem padding_tail (E : Env program.Γ) (s : GlobalState)
    (src ctx buffer : Pointer) (pending : BitVec 8) (blocks : BitVec 128)
    (hsrc : E.read (%arg1) = .value src)
    (hctx : E.read (%86) = .value ctx) (hbuffer : E.read (%84) = .value buffer)
    (h208 : E.read (%1) = .value 208#64)
    (h128 : E.read (%2) = .value 128#64)
    (h127 : E.read (%3) = .value 127#64)
    (h255 : E.read (%4) = .value 255#8)
    (h192 : E.read (%5) = .value 192#64)
    (h10 : E.read (%6) = .value 10#128)
    (h3 : E.read (%7) = .value 3#128)
    (h0 : E.read (%8) = .value 0#8)
    (hmarker : E.read (%9) = .value 128#8)
    (h112 : E.read (%10) = .value 112#64)
    (h16 : E.read (%11) = .value 16#64)
    (hs : SmallRange s.mem src 208) (hc : SmallRange s.mem ctx 208)
    (hb : SmallRange s.mem buffer 128)
    (hcs : ctx.id ≠ src.id) (hbc : buffer.id ≠ ctx.id)
    (hpending : s.mem.readAt (src.add 127#64) 8 = pending)
    (hblocks : s.mem.readAt (src.add 192#64) 128 = blocks)
    (hp : pending.toNat < 128) :
    program.bb0.runBodyFrom E 151 s =
      .value (paddingEnv E ctx buffer pending blocks, paddingState s src ctx buffer pending) := by
  change E.args 1 = .value src at hsrc
  have hcc : SmallRange (cloned s src ctx).mem ctx 208 := hc.storeAt _ _
  have hbc' : SmallRange (cloned s src ctx).mem buffer 128 := hb.storeAt _ _
  have hg128 : Operation.gepInboundsLive (cloned s src ctx).mem
      (.value ctx) [.value (128 : Int)] = .value (ctx.add 128#64) :=
    hcc.gep (k := 128) (by decide)
  have hg127 : Operation.gepInboundsLive (cloned s src ctx).mem
      (.value ctx) [.value (127 : Int)] = .value (ctx.add 127#64) :=
    hcc.gep (k := 127) (by decide)
  have hg192 : Operation.gepInboundsLive (cloned s src ctx).mem
      (.value ctx) [.value (192 : Int)] = .value (ctx.add 192#64) :=
    hcc.gep (k := 192) (by decide)
  have hcPending : Fits (cloned s src ctx).mem (ctx.add 127#64) 8 :=
    hcc.fits_add (k := 127) (count := 1) (by decide)
  have hcBlocks : Fits (cloned s src ctx).mem (ctx.add 192#64) 128 :=
    hcc.fits_add (k := 192) (count := 16) (by decide)
  have hrPending : (cloned s src ctx).mem.readAt (ctx.add 127#64) 8 = pending :=
    (copy_readAt_offset s.mem src ctx 208 127 1 hs hc (by decide)).trans hpending
  have hrBlocks : (cloned s src ctx).mem.readAt (ctx.add 192#64) 128 = blocks :=
    (copy_readAt_offset s.mem src ctx 208 192 16 hs hc (by decide)).trans hblocks
  have hpn : (pending.setWidth 64).toNat = pending.toNat := by
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by omega)
  have hpi : (pending.setWidth 64).toInt = (pending.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [hpn]; omega), hpn]
  have hsr : Operation.GepSignedRange (pending.toNat : Int) := by
    change -(2 ^ 63 : Int) ≤ (pending.toNat : Int) ∧ (pending.toNat : Int) < 2 ^ 63
    omega
  have hindex : Operation.gepInboundsIndex 1 (.value (pending.setWidth 64)) =
      .value (pending.toNat : Int) := by
    have h := Operation.gepInboundsIndex_eq 1 (pending.setWidth 64)
      (by simpa [hpi] using hsr) (by simpa [hpi] using hsr)
      (BitVec.isLt _) (by simpa only [BitVec.ofInt_toInt, Nat.mul_one] using
        (pending.setWidth 64).isLt)
    simpa [hpi] using h
  have hbp : SmallRange (paddingCopied s src ctx buffer pending).mem buffer 128 :=
    ((hbc'.storeAt _ _).storeAt _ _)
  have hgPending : Operation.gepInboundsLive (paddingCopied s src ctx buffer pending).mem
      (.value buffer) [.value (pending.toNat : Int)] =
      .value (buffer.add (pending.setWidth 64)) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      hbp.gep (k := pending.toNat) (by omega)
  have hcInput : Fits (paddingCleared s src ctx buffer).mem ctx (8 * pending.toNat) :=
    (smallRange_mono (hcc.storeAt _ _) (by omega : pending.toNat ≤ 208)).fits
  have hbOutput : Fits (paddingCleared s src ctx buffer).mem buffer (8 * pending.toNat) :=
    (smallRange_mono (hbc'.storeAt _ _) (by omega : pending.toNat ≤ 128)).fits
  have hbMarker : Fits (paddingCopied s src ctx buffer pending).mem
      (buffer.add (pending.setWidth 64)) 8 := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      hbp.fits_add (k := pending.toNat) (count := 1) (by omega)
  have hdCopy : (Range.of ctx 1664).Disjoint (Range.of src 1664) := Or.inl hcs
  have hdBuffer : (Range.of buffer (8 * pending.toNat)).Disjoint
      (Range.of ctx (8 * pending.toNat)) := Or.inl hbc
  have hcmp : Operation.icmp .sgt (.value pending) (.value 255#8) = .value 1#1 := by
    have hpi8 : pending.toInt = (pending.toNat : Int) :=
      BitVec.toInt_eq_toNat_of_lt (by omega)
    simp [Operation.icmp, BitVec.slt, hpi8, show (-1 : Int) < pending.toNat by omega]
  have hsgt : BitVec.ofBool ((255#8).slt pending) = 1#1 := by
    simpa [Operation.icmp] using hcmp
  have hswap (v : BitVec 128) : Operation.bswap (.value v) = .value (swapBytes v) := rfl
  have hbshift : Operation.shl {} (.value blocks) (.value 10#128) =
      .value (blocks <<< 10) := by simp [Operation.shl]
  have hz128 := pending_zext128 pending hp
  have hz64 := pending_zext64 pending hp
  have hshift := pending_shift pending
  have hor := bitLength_or_defined blocks pending hp
  dsimp only [cloned, paddingCleared, paddingCopied] at hg128 hg127 hg192 hcPending hcBlocks hrPending hrBlocks hcInput hbOutput hbc' hgPending hbMarker
  simp [BasicBlock.runBodyFrom, program.bb0, paddingEnv, paddingState,
    paddingCopied, paddingCleared, cloned,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy, Operation.memset,
    Operation.store, Operation.load, UnOp.compute, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset,
    hsrc, hctx, hbuffer, h208, h128, h127, h255, h192, h10, h3, h0, hmarker, h112, h16,
    hs.fits, hc.fits, hbc'.fits, hcPending, hcBlocks, hrPending, hrBlocks, hg128, hg127, hg192,
    hcInput, hbOutput, hbMarker, hdCopy, hdBuffer, hsgt, hz128, hz64, hshift, hor,
    hgPending, hindex, hpn, hbshift, hswap,
    Operation.xor, Operation.icmp, Agave.Ed25519.SHA512.needsTwoBlocks, throwUBIf]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
