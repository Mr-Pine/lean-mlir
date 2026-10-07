import SSA.Projects.Agave.Ed25519.Bridge.FiredancerParameterizedSource

/-! Success-only contracts for the five reachable calls in one verifier invocation.
Each contract exposes the actual CFG execution and its memory footprint.  There
is no requirement on malformed contexts, unrelated transcripts, or poison runs.
-/
namespace Agave.Ed25519.Bridge
open LeanMLIR SLLVM Firedancer Firedancer.Common

/-- LLVM inbounds pointer arithmetic uses the signed object-size boundary. -/
def FiredancerBlockSmall (m : MemoryState) (id : BlockId) : Prop :=
  ∀ b, m.live? id = some b → b.length < 2^63

/-- Only the resolved SHA constant allocation needs the signed-size bound. -/
def FiredancerShaConstantsSmall (s : GlobalState) : Prop :=
  ∀ q, GlobalPtr s "fd_sha512_core_ref.K" q → FiredancerBlockSmall s.mem q.id

theorem FiredancerShaConstantsSmall.of_live?_eq {s t : GlobalState}
    {sha : Pointer} {k : BitVec (80 * 64)} (small : FiredancerShaConstantsSmall s)
    (wf : s.WF) (h : Sha512KHolds s sha k) (hg : t.globals = s.globals)
    (hl : ∀ b : BlockId, b ≠ sha.id → b.id < s.alloc.nextFreeBlock →
      t.mem.live? b = s.mem.live? b) : FiredancerShaConstantsSmall t := by
  obtain ⟨q, ⟨hp, hfit, _⟩, hne⟩ := h
  intro q' hq' b hb
  have hq : GlobalPtr s "fd_sha512_core_ref.K" q' := by
    unfold GlobalPtr at hq' ⊢
    rwa [hg] at hq'
  have heq : q' = q := Option.some.inj (hq.symm.trans hp)
  subst q'
  apply small q hp b
  rwa [hl q.id hne (lt_nextFreeBlock_of_fits wf hfit)] at hb

/-- Caller memory conditions needed by concrete inbounds SHA source loops.
Context and output allocations are private fixed-size blocks. -/
structure FiredancerReachableMemoryReady (s : GlobalState) (msg sig pk : Pointer) : Prop where
  message : FiredancerBlockSmall s.mem msg.id
  signature : FiredancerBlockSmall s.mem sig.id
  publicKey : FiredancerBlockSmall s.mem pk.id
  constants : FiredancerShaConstantsSmall s

/-- One reachable initialization. -/
def FiredancerReachableInit (programs : FiredancerShaPrograms)
    (before after : Option LiveBlock) (off : BitVec 64) : Prop :=
  ∀ (sha : Pointer) (s : GlobalState), s.WF → IsSha512Ptr s.mem sha →
    sha.offset = off → s.mem.live? sha.id = before →
    ∃ s' : GlobalState,
      StateT.run (runFunction (programs.init.denote
        (Ctxt.Valuation.singleton (.value sha)))) s = .value ([.value sha]ₕ, s') ∧
      s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals ∧
      (∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b) ∧
      s'.mem.live? sha.id = after

/-- One append, restricted to its reachable context and actual input bytes. -/
def FiredancerReachableAppend (programs : FiredancerShaPrograms)
    (k : BitVec (80 * 64)) (before after : Option LiveBlock)
    (off : BitVec 64) (input : List (BitVec 8)) : Prop :=
  ∀ (sha data : Pointer) (sz : BitVec 64) (s : GlobalState), s.WF →
    data.offset.toNat + sz.toNat ≤ 2 ^ 64 → sha.id ≠ data.id →
    Sha512KHolds s sha k → ∀ hdata : Fits s.mem data (sz.toNat * 8),
    FiredancerBlockSmall s.mem data.id → FiredancerShaConstantsSmall s →
    sha.offset = off → s.mem.live? sha.id = before →
    bytesOf (readWord hdata) = input →
    ∃ s' : GlobalState,
      StateT.run (runFunction (programs.append.denote
        (Ctxt.Valuation.ofHVector [.value sz, .value data, .value sha]ₕ))) s =
        .value ([.value sha]ₕ, s') ∧
      s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals ∧
      (∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b) ∧
      s'.mem.live? sha.id = after

/-- Finish only after the actual third append, with the verifier's fresh
64-byte output allocation. Digest correctness belongs to this concrete call,
not to an assumed equality for the whole verifier or an abstract hash oracle. -/
def FiredancerReachableFinish (programs : FiredancerShaPrograms)
    (k : BitVec (80 * 64)) (before after : Option LiveBlock)
    (off : BitVec 64) (digest : BitVec 512) : Prop :=
  ∀ (sha output : Pointer) (s : GlobalState), s.WF →
    Fits s.mem output (64 * 8) → output.offset.toNat + 64 ≤ 2 ^ 64 →
    sha.id ≠ output.id → Sha512KHolds s sha k →
    FiredancerShaConstantsSmall s → sha.offset = off →
    s.mem.live? sha.id = before →
    s.mem.live? output.id = some { length := 64, bytes := 0#_ } →
    output.offset = 0 →
    ∃ s' : GlobalState,
      StateT.run (runFunction (programs.finish.denote
        (Ctxt.Valuation.ofHVector [.value output, .value sha]ₕ))) s =
        .value ([.value output]ₕ, s') ∧
      s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals ∧
      (∀ b : BlockId, ¬(b = sha.id ∨ b = output.id) → s'.mem.live? b = s.mem.live? b) ∧
      s'.mem.live? sha.id = after ∧
      ∃ h : Fits s'.mem output (64 * 8), readWord h = digest

/-- Intermediate blocks are witnesses, not independent correctness premises:
the five fields prove executions connecting each predecessor to its successor. -/
structure FiredancerReachableCalls (programs : FiredancerShaPrograms)
    (k : BitVec (80 * 64)) (before : Option LiveBlock) (off : BitVec 64)
    (r a : BitVec 256) (message : List (BitVec 8)) (digest : BitVec 512) where
  initialized : Option LiveBlock
  afterR : Option LiveBlock
  afterA : Option LiveBlock
  afterMessage : Option LiveBlock
  finished : Option LiveBlock
  init : FiredancerReachableInit programs before initialized off
  appendR : FiredancerReachableAppend programs k initialized afterR off (bytesOf (n := 32) r)
  appendA : FiredancerReachableAppend programs k afterR afterA off (bytesOf (n := 32) a)
  appendMessage : FiredancerReachableAppend programs k afterA afterMessage off message
  finish : FiredancerReachableFinish programs k afterMessage finished off digest

end Agave.Ed25519.Bridge
