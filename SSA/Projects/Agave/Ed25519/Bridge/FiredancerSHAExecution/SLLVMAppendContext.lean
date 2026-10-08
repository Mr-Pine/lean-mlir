import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.Context
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInitContract

/-! Source-memory observations for the reachable streaming invariant. The
relation only observes the live context allocation; it contains no execution
premise and does not identify the RIR and SLLVM machine states. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
set_option autoImplicit false

/-- Total word observation; validity is separately supplied by `Fits`. -/
def sourceRead (m : MemoryState) (p : Pointer) (w : Nat) : BitVec w :=
  match m.live? p.id with
  | some b => b.bytes.extractLsb' p.offsetInBits w
  | none => 0

def sourceReadBytes (m : MemoryState) (p : Pointer) (n : Nat) : List (BitVec 8) :=
  List.ofFn fun i : Fin n => sourceRead m (p.withOffset (BitVec.ofNat 64 i.val)) 8

def sourceReadState (m : MemoryState) (p : Pointer) : State :=
  ⟨sourceRead m (p.withOffset 128#64) 64, sourceRead m (p.withOffset 136#64) 64,
   sourceRead m (p.withOffset 144#64) 64, sourceRead m (p.withOffset 152#64) 64,
   sourceRead m (p.withOffset 160#64) 64, sourceRead m (p.withOffset 168#64) 64,
   sourceRead m (p.withOffset 176#64) 64, sourceRead m (p.withOffset 184#64) 64⟩

structure ContextRepresents (m : MemoryState) (context : Pointer)
    (completed pending : List (BitVec 8)) : Prop where
  live : Fits m context (224 * 8)
  noWrap : context.offset.toNat + 224 < 2 ^ 63
  completedWhole : completed.length % 128 = 0
  pendingBound : pending.length < 128
  pendingBytes : sourceReadBytes m context pending.length = pending
  pendingCount : sourceRead m (context.withOffset 200#64) 64 = BitVec.ofNat 64 pending.length
  chaining : sourceReadState m context = unpack (Spec.run initialWords completed)
  bitCount : sourceRead m (context.withOffset 216#64) 64 ++
      sourceRead m (context.withOffset 208#64) 64 =
    BitVec.ofNat 128 (8 * (completed.length + pending.length))

theorem sourceRead_of_live_eq {m n : MemoryState} {p : Pointer} {w : Nat}
    (h : m.live? p.id = n.live? p.id) : sourceRead m p w = sourceRead n p w := by
  simp only [sourceRead, h]

/-- A whole-block frame is sufficient to preserve every stream observation. -/
theorem ContextRepresents.of_live_eq {m n : MemoryState} {p : Pointer}
    {completed pending : List (BitVec 8)} (hp : ContextRepresents m p completed pending)
    (h : m.live? p.id = n.live? p.id) : ContextRepresents n p completed pending := by
  have hw (off : BitVec 64) (w : Nat) :
      sourceRead m (p.withOffset off) w = sourceRead n (p.withOffset off) w :=
    sourceRead_of_live_eq h
  refine ⟨fits_of_live?_eq h.symm hp.live, hp.noWrap, hp.completedWhole,
    hp.pendingBound, ?_, ?_, ?_, ?_⟩
  · simpa only [sourceReadBytes, ← hw] using hp.pendingBytes
  · simpa only [← hw] using hp.pendingCount
  · simpa only [sourceReadState, ← hw] using hp.chaining
  · simpa only [← hw] using hp.bitCount

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
