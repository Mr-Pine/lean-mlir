import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.EntryTail

/-! Actual final-block serialization before the wide-reduction call. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

/-- The source sets the copied context's pending length to zero first. -/
def clearCount (s : GlobalState) (ctx : Pointer) : GlobalState :=
  {s with mem := s.mem.storeAt (ctx.add 127#64) 0#8}

/-- Native u64 reads in source order, before any digest-buffer store. -/
def chainWord (s : GlobalState) (ctx : Pointer) (i : Nat) : BitVec 64 :=
  (clearCount s ctx).mem.readAt (ctx.add (BitVec.ofNat 64 (128 + 8 * i))) 64

/-- Exact eight-word serialization store sequence, including byte swapping. -/
def writeWords (m : MemoryState) (dst : Pointer) (words : Nat → BitVec 64) : Nat → MemoryState
  | 0 => m
  | n + 1 => (writeWords m dst words n).storeAt
      (dst.add (BitVec.ofNat 64 (8 * n))) (swapBytes (words n))

theorem writeWords_live (m : MemoryState) (dst p : Pointer) (words : Nat → BitVec 64)
    (n count : Nat) (h : SmallRange m p count) :
    SmallRange (writeWords m dst words n) p count := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt _ _

theorem writeWords_wf (s : GlobalState) (dst : Pointer) (words : Nat → BitVec 64)
    (n : Nat) (h : s.WF) : {s with mem := writeWords s.mem dst words n}.WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt

def serializedState (s : GlobalState) (ctx dst : Pointer) : GlobalState :=
  {s with mem := writeWords (clearCount s ctx).mem dst (chainWord s ctx) 8}

def serializedEnv (E : Env program.Γ) (s : GlobalState) (ctx dst : Pointer) : Env program.Γ :=
  E[%168 := .value (chainWord s ctx 0),
    %169 := .value (swapBytes (chainWord s ctx 0)),
    %170 := .value (ctx.add 136#64),
    %171 := .value (chainWord s ctx 1),
    %172 := .value (swapBytes (chainWord s ctx 1)),
    %173 := .value (ctx.add 144#64),
    %174 := .value (chainWord s ctx 2),
    %175 := .value (swapBytes (chainWord s ctx 2)),
    %176 := .value (ctx.add 152#64),
    %177 := .value (chainWord s ctx 3),
    %178 := .value (swapBytes (chainWord s ctx 3)),
    %179 := .value (ctx.add 160#64),
    %180 := .value (chainWord s ctx 4),
    %181 := .value (swapBytes (chainWord s ctx 4)),
    %182 := .value (ctx.add 168#64),
    %183 := .value (chainWord s ctx 5),
    %184 := .value (swapBytes (chainWord s ctx 5)),
    %185 := .value (ctx.add 176#64),
    %186 := .value (chainWord s ctx 6),
    %187 := .value (swapBytes (chainWord s ctx 6)),
    %188 := .value (ctx.add 184#64),
    %189 := .value (chainWord s ctx 7),
    %190 := .value (swapBytes (chainWord s ctx 7)),
    %191 := .value (dst.add 8#64),
    %192 := .value (dst.add 16#64),
    %193 := .value (dst.add 24#64),
    %194 := .value (dst.add 32#64),
    %195 := .value (dst.add 40#64),
    %196 := .value (dst.add 48#64),
    %197 := .value (dst.add 56#64)]

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Every load, byte swap and digest store before instruction 42 executes in
the imported bb3. This theorem has no arithmetic or compression premise. -/
theorem serialization_prefix (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (ctx dst : Pointer)
    (hctx : E.read (%86) = .value ctx)
    (hchain : E.read (%151) = .value (ctx.add 128#64))
    (hcount : E.read (%152) = .value (ctx.add 127#64))
    (hdst : E.read (%85) = .value dst) (hzero : E.read (%8) = .value 0#8)
    (hc : SmallRange s.mem ctx 208) (hd : SmallRange s.mem dst 64) :
    (List.foldlM Instr.run E ((program.bb3 p).body.take 42) : EffectM (Env program.Γ)) s =
      .value (serializedEnv E s ctx dst, serializedState s ctx dst) := by
  have hcountFit : Fits s.mem (ctx.add 127#64) 8 :=
    hc.fits_add (k := 127) (count := 1) (by decide)
  have hswap (v : BitVec 64) : Operation.bswap (.value v) = .value (swapBytes v) := rfl
  have hf0 : Fits (clearCount s ctx).mem (ctx.add 128#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 128) (count := 8) (by decide)
  have hf1 : Fits (clearCount s ctx).mem (ctx.add 136#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 136) (count := 8) (by decide)
  have hg1 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (136 : Int)] = .value (ctx.add 136#64) :=
    (hc.storeAt _ _).gep (k := 136) (by decide)
  have hf2 : Fits (clearCount s ctx).mem (ctx.add 144#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 144) (count := 8) (by decide)
  have hg2 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (144 : Int)] = .value (ctx.add 144#64) :=
    (hc.storeAt _ _).gep (k := 144) (by decide)
  have hf3 : Fits (clearCount s ctx).mem (ctx.add 152#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 152) (count := 8) (by decide)
  have hg3 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (152 : Int)] = .value (ctx.add 152#64) :=
    (hc.storeAt _ _).gep (k := 152) (by decide)
  have hf4 : Fits (clearCount s ctx).mem (ctx.add 160#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 160) (count := 8) (by decide)
  have hg4 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (160 : Int)] = .value (ctx.add 160#64) :=
    (hc.storeAt _ _).gep (k := 160) (by decide)
  have hf5 : Fits (clearCount s ctx).mem (ctx.add 168#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 168) (count := 8) (by decide)
  have hg5 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (168 : Int)] = .value (ctx.add 168#64) :=
    (hc.storeAt _ _).gep (k := 168) (by decide)
  have hf6 : Fits (clearCount s ctx).mem (ctx.add 176#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 176) (count := 8) (by decide)
  have hg6 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (176 : Int)] = .value (ctx.add 176#64) :=
    (hc.storeAt _ _).gep (k := 176) (by decide)
  have hf7 : Fits (clearCount s ctx).mem (ctx.add 184#64) 64 :=
    (hc.storeAt _ _).fits_add (k := 184) (count := 8) (by decide)
  have hg7 : Operation.gepInboundsLive (clearCount s ctx).mem
      (.value ctx) [.value (184 : Int)] = .value (ctx.add 184#64) :=
    (hc.storeAt _ _).gep (k := 184) (by decide)
  have hd0 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    0 64 (hd.storeAt _ _)
  have ho0 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 0)
      (dst.add 0#64) 64 := hd0.fits_add (k := 0) (count := 8) (by decide)
  have hd1 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    1 64 (hd.storeAt _ _)
  have ho1 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 1)
      (dst.add 8#64) 64 := hd1.fits_add (k := 8) (count := 8) (by decide)
  have hp1 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 1)
      (.value dst) [.value (8 : Int)] = .value (dst.add 8#64) :=
    hd1.gep (k := 8) (by decide)
  have hd2 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    2 64 (hd.storeAt _ _)
  have ho2 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 2)
      (dst.add 16#64) 64 := hd2.fits_add (k := 16) (count := 8) (by decide)
  have hp2 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 2)
      (.value dst) [.value (16 : Int)] = .value (dst.add 16#64) :=
    hd2.gep (k := 16) (by decide)
  have hd3 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    3 64 (hd.storeAt _ _)
  have ho3 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 3)
      (dst.add 24#64) 64 := hd3.fits_add (k := 24) (count := 8) (by decide)
  have hp3 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 3)
      (.value dst) [.value (24 : Int)] = .value (dst.add 24#64) :=
    hd3.gep (k := 24) (by decide)
  have hd4 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    4 64 (hd.storeAt _ _)
  have ho4 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 4)
      (dst.add 32#64) 64 := hd4.fits_add (k := 32) (count := 8) (by decide)
  have hp4 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 4)
      (.value dst) [.value (32 : Int)] = .value (dst.add 32#64) :=
    hd4.gep (k := 32) (by decide)
  have hd5 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    5 64 (hd.storeAt _ _)
  have ho5 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 5)
      (dst.add 40#64) 64 := hd5.fits_add (k := 40) (count := 8) (by decide)
  have hp5 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 5)
      (.value dst) [.value (40 : Int)] = .value (dst.add 40#64) :=
    hd5.gep (k := 40) (by decide)
  have hd6 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    6 64 (hd.storeAt _ _)
  have ho6 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 6)
      (dst.add 48#64) 64 := hd6.fits_add (k := 48) (count := 8) (by decide)
  have hp6 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 6)
      (.value dst) [.value (48 : Int)] = .value (dst.add 48#64) :=
    hd6.gep (k := 48) (by decide)
  have hd7 := writeWords_live (clearCount s ctx).mem dst dst (chainWord s ctx)
    7 64 (hd.storeAt _ _)
  have ho7 : Fits (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 7)
      (dst.add 56#64) 64 := hd7.fits_add (k := 56) (count := 8) (by decide)
  have hp7 : Operation.gepInboundsLive
      (writeWords (clearCount s ctx).mem dst (chainWord s ctx) 7)
      (.value dst) [.value (56 : Int)] = .value (dst.add 56#64) :=
    hd7.gep (k := 56) (by decide)
  simp [clearCount, writeWords, chainWord] at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hg1 hg2 hg3 hg4 hg5 hg6 hg7 ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 hp1 hp2 hp3 hp4 hp5 hp6 hp7
  simp [program.bb3, serializedEnv, serializedState, chainWord, clearCount, writeWords,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store, Operation.load,
    UnOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_effect, mlir_env,
    GepIndex.inboundsOffset, Operation.gepInboundsIndex, Operation.GepSignedRange,
    hctx, hchain, hcount, hdst, hzero, hcountFit, hswap,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hg1, hg2, hg3, hg4, hg5, hg6, hg7, ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7, hp1, hp2, hp3, hp4, hp5, hp6, hp7, throwUBIf]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
