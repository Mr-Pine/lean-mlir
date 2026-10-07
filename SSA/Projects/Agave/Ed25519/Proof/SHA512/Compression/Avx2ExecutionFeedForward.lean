import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionTail
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFeedForwardMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionFeedForwardVectors

/-! Exact imported bb7 execution: add the eight final working words into
the chaining state, issue the two original vector stores, and branch to bb1.
The two stores are shown equal to the specification's single 512-bit update. -/

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

structure FeedForwardReady (E : Env program.Γ) (chain : Pointer) : Prop where
  chainPtr : E.read (%arg0) = .value chain
  upper : E.read (%99) = .value (chain.add 32#64)
  zero : E.read (%2) = .value 0#64
  one : E.read (%1) = .value 1#64
  two : E.read (%42) = .value 2#64
  three : E.read (%46) = .value 3#64

/-- The source adds the final words to the initial words in this order. -/
def feedForwardLow (initial final : Spec.State) : BitVec 256 :=
  pack4 (final.a + initial.a) (final.b + initial.b)
    (final.c + initial.c) (final.d + initial.d)

def feedForwardHigh (initial final : Spec.State) : BitVec 256 :=
  pack4 (final.e + initial.e) (final.f + initial.f)
    (final.g + initial.g) (final.h + initial.h)

def feedForwardState (mem : GlobalState) (chain : Pointer)
    (initial final : Spec.State) : GlobalState :=
  { mem with mem := ((mem.mem.storeAt chain (feedForwardLow initial final)).storeAt
      (chain.add 32#64) (feedForwardHigh initial final)) }

/-- The partial vector inserts retain the original poison/input lanes until
all four lanes have been overwritten. No premise about register 45 is needed. -/
def feedForwardEnv (E : Env program.Γ) (initial final : Spec.State) : Env program.Γ :=
  let v310 := Operation.insertelement (E.read (%45)) (.value final.a) (.value 0#64)
  let v311 := Operation.insertelement v310 (.value final.b) (.value 1#64)
  let v312 := Operation.insertelement v311 (.value final.c) (.value 2#64)
  let v316 := Operation.insertelement (E.read (%45)) (.value final.e) (.value 0#64)
  let v317 := Operation.insertelement v316 (.value final.f) (.value 1#64)
  let v318 := Operation.insertelement v317 (.value final.g) (.value 2#64)
  E[%309 := vec4 initial.a initial.b initial.c initial.d,
    %310 := v310, %311 := v311, %312 := v312,
    %313 := vec4 final.a final.b final.c final.d,
    %314 := vec4 (final.a + initial.a) (final.b + initial.b)
      (final.c + initial.c) (final.d + initial.d),
    %315 := vec4 initial.e initial.f initial.g initial.h,
    %316 := v316, %317 := v317, %318 := v318,
    %319 := vec4 final.e final.f final.g final.h,
    %320 := vec4 (final.e + initial.e) (final.f + initial.f)
      (final.g + initial.g) (final.h + initial.h)]

/-- Splitting at four words leaves precisely the standard native-word encoding. -/
theorem pack_halves (s : Spec.State) :
    pack4 s.e s.f s.g s.h ++ pack4 s.a s.b s.c s.d = pack s := by
  simp only [pack4, pack]
  repeat' (rw [BitVec.append_assoc]; simp only [BitVec.cast_eq])

theorem feedForward_halves (initial final : Spec.State) :
    feedForwardHigh initial final ++ feedForwardLow initial final =
      pack (Spec.feedForward initial final) := by
  simpa only [feedForwardHigh, feedForwardLow, Spec.feedForward, BitVec.add_comm] using
    pack_halves (Spec.feedForward initial final)

/-- Exact whole-memory equality, including every byte outside the chaining state. -/
theorem feedForwardState_eq (mem : GlobalState) (chain : Pointer)
    (initial final : Spec.State) (hc : SmallRange mem.mem chain 64) :
    feedForwardState mem chain initial final =
      { mem with mem := mem.mem.storeAt chain (pack (Spec.feedForward initial final)) } := by
  simp only [feedForwardState, store_pair mem.mem chain hc, feedForward_halves]

/-- Execute all instructions of the imported feed-forward block, including
its two vector stores and lifetime marker. -/
theorem feedForward_body (E : Env program.Γ) (mem : GlobalState) (chain : Pointer)
    (initial final : Spec.State) (h : FeedForwardReady E chain)
    (hf : TailFinalReady E final) (hc : SmallRange mem.mem chain 64)
    (hread : mem.mem.readAt chain 512 = pack initial) :
    List.foldlM Instr.run E program.bb7.body mem =
      .value (feedForwardEnv E initial final, feedForwardState mem chain initial final) := by
  have hlo : mem.mem.readAt chain 256 = pack4 initial.a initial.b initial.c initial.d := by
    rw [read_low256 mem.mem chain hc, hread, ← pack_halves]
    exact BitVec.extractLsb'_append_eq_right
  have hhi : mem.mem.readAt (chain.add 32#64) 256 =
      pack4 initial.e initial.f initial.g initial.h := by
    rw [read_high256 mem.mem chain hc, hread, ← pack_halves]
    exact BitVec.extractLsb'_append_eq_left
  have hfit0 : Fits mem.mem chain 256 := by
    simpa only [Pointer.add_zero] using hc.fits_add (k := 0) (count := 32) (by decide)
  have hfit1 : Fits mem.mem (chain.add 32#64) 256 :=
    hc.fits_add (k := 32) (count := 32) (by decide)
  have hd : (Range.of chain 256).Disjoint (Range.of (chain.add 32#64) 256) := by
    simpa using hc.disjoint_chunks (i := 0) (j := 1) (by decide) (by decide) (by decide)
  have hfit1' : Fits (mem.mem.storeAt chain (feedForwardLow initial final))
      (chain.add 32#64) 256 := hfit1.storeAt
  have hhi' : (mem.mem.storeAt chain (feedForwardLow initial final)).readAt
      (chain.add 32#64) 256 = pack4 initial.e initial.f initial.g initial.h := by
    rw [MemoryState.readAt_storeAt_disjoint hd, hhi]
  rcases h with ⟨hchain, hupper, hzero, hone, htwo, hthree⟩
  rcases hf with ⟨ha, hb, hc', hd', he, hf', hg, hh⟩
  change E.args 0 = .value chain at hchain
  dsimp only [feedForwardLow] at hfit1' hhi'
  have hunflat (a b c d : Word) :
      Ty.wrap (Vector.ofFn (fun i => Ty.extractVecElem 4 64 i (pack4 a b c d))) =
        vec4 a b c d := by
    simpa only [Ty.unflatten_vec] using vec4_unflatten a b c d
  simp [program.bb7, List.foldlM_cons, List.foldlM_nil, Instr.run,
    feedForwardEnv, feedForwardState, feedForwardLow, feedForwardHigh,
    hchain, hupper, hzero, hone, htwo, hthree, ha, hb, hc', hd', he, hf', hg, hh,
    hlo, hhi', hfit0, hfit1', hunflat, vec4_insert, vec4_add, vec4_flatten,
    Operation.load, Operation.store, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

@[simp] theorem feedForward_params1 : program.blockParams 1 = .cons (%86) .nil := rfl

/-- The tail's register frame transports exactly the bb7 inputs that are
not working words. The arbitrary initial vector is deliberately absent. -/
theorem FeedForwardReady.of_tailFrame {E E' : Env program.Γ} {chain : Pointer}
    (h : FeedForwardReady E chain) (hframe : TailFrame E E') : FeedForwardReady E' chain := by
  constructor
  · change E'.args 0 = .value chain
    rw [hframe.1]
    exact h.chainPtr
  · exact (hframe.2 99 (Or.inl (by decide))).trans h.upper
  · exact (hframe.2 2 (Or.inl (by decide))).trans h.zero
  · exact (hframe.2 1 (Or.inl (by decide))).trans h.one
  · exact (hframe.2 42 (Or.inl (by decide))).trans h.two
  · exact (hframe.2 46 (Or.inl (by decide))).trans h.three

/-- The emitted terminator writes bb1's actual loop parameter and preserves
the rest of the exact post-body environment. -/
theorem feedForward_block (E : Env program.Γ) (mem : GlobalState) (chain : Pointer)
    (initial final : Spec.State) (h : FeedForwardReady E chain)
    (hf : TailFinalReady E final) (hc : SmallRange mem.mem chain 64)
    (hread : mem.mem.readAt chain 512 = pack initial) :
    program.bb7.run program.blockParams E mem =
      .value (((feedForwardEnv E initial final)[%86 := .value 1#64], .inr 1),
        { mem with mem := mem.mem.storeAt chain (pack (Spec.feedForward initial final)) }) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    feedForward_body E mem chain initial final h hf hc hread, PoisonOr.value_bind]
  rw [feedForwardState_eq mem chain initial final hc]
  simp [program.bb7, Exit.run, Jump.run, feedForwardEnv, h.one,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem feedForward_runFrom (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (chain : Pointer) (initial final : Spec.State) (h : FeedForwardReady E chain)
    (hf : TailFinalReady E final) (hc : SmallRange mem.mem chain 64)
    (hread : mem.mem.readAt chain 512 = pack initial) :
    (program g).runFrom E 7 mem =
      (program g).runFrom ((feedForwardEnv E initial final)[%86 := .value 1#64]) 1
        { mem with mem := mem.mem.storeAt chain (pack (Spec.feedForward initial final)) } := by
  rw [Func.runFrom_eq]
  change (program.bb7.run program.blockParams E mem >>= fun x =>
    (program g).continue x.1.1 x.1.2 x.2) = _
  rw [feedForward_block E mem chain initial final h hf hc hread]
  rfl

/-- Every observation disjoint from the 64-byte chaining state is unchanged. -/
theorem feedForward_read_disjoint (mem : GlobalState) (chain : Pointer)
    (initial final : Spec.State) (hc : SmallRange mem.mem chain 64)
    (p : Pointer) (width : Nat)
    (hd : (Range.of chain 512).Disjoint (Range.of p width)) :
    (feedForwardState mem chain initial final).mem.readAt p width = mem.mem.readAt p width := by
  rw [feedForwardState_eq mem chain initial final hc]
  exact MemoryState.readAt_storeAt_disjoint hd _

/-- The checked tail and checked feed-forward compose to the complete
compression output once the preceding 64-round invariant is established. -/
theorem tail_feedForward (g : Globals) (E : Env program.Γ) (mem : GlobalState)
    (scratch chain : Pointer) (initial : Spec.State) (block : Agave.Ed25519.Bridge.Challenge.Bytes)
    (hs : TailSchedule mem.mem scratch (schedule block))
    (ht : TailReady E scratch 64 (roundsFrom initial (schedule block) 0 64))
    (hf : FeedForwardReady E chain) (hc : SmallRange mem.mem chain 64)
    (hread : mem.mem.readAt chain 512 = pack initial) :
    ∃ E', TailTrace mem 16 E E' ∧
      program.bb7.run program.blockParams E' mem =
        .value (((feedForwardEnv E' initial (roundsFrom initial (schedule block) 0 80))[%86 := .value 1#64], .inr 1),
          { mem with mem := mem.mem.storeAt chain (pack (compressBlock initial block)) }) ∧
      (program g).runFrom E 6 mem =
        (program g).runFrom
          ((feedForwardEnv E' initial (roundsFrom initial (schedule block) 0 80))[%86 := .value 1#64]) 1
          { mem with mem := mem.mem.storeAt chain (pack (compressBlock initial block)) } := by
  obtain ⟨E', htrace, hfinal, hframe⟩ :=
    tail_sixteen_from_prefix mem scratch (schedule block) E initial hs ht
  have hready := hf.of_tailFrame hframe
  refine ⟨E', htrace, feedForward_block E' mem chain initial _ hready hfinal hc hread, ?_⟩
  exact (htrace.runFrom g).trans
    (feedForward_runFrom g E' mem chain initial _ hready hfinal hc hread)

end Agave.Ed25519.SHA512.Execution.Avx2
