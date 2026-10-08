import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceCore
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.InitializerLink
import SSA.Projects.Firedancer.Common.Spec.SHA
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! Shared observable interface for the actual imported scalar SLLVM core.
This module defines readiness and the desired conclusion; it does not assume
that the core satisfies the conclusion. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
open LeanMLIR SLLVM Firedancer

/-- Addressable bytes in an ordinary allocation below the signed-pointer bound.
This supplies all nonwrapping addresses used by the source loops. -/
def SmallRange (m : MemoryState) (p : Pointer) (bytes : Nat) : Prop :=
  ∃ b, m.live? p.id = some b ∧ b.length < 2^63 ∧ p.offset.toNat + bytes ≤ b.length

/-- A total byte observation, with zero only for a missing/dead allocation. -/
def readBits (m : MemoryState) (p : Pointer) (width : Nat) : BitVec width :=
  (readWord? p width m).getD 0

def readBytes (m : MemoryState) (p : Pointer) (bytes : Nat) : List (BitVec 8) :=
  Firedancer.Common.bytesOf (readBits m p (bytes * 8))

/-- Byte-range disjointness permits a shared allocation, as required when the
streaming wrappers compress their context's own pending buffer. -/
def Disjoint (p : Pointer) (np : Nat) (q : Pointer) (nq : Nat) : Prop :=
  p.id ≠ q.id ∨ p.offset.toNat + np ≤ q.offset.toNat ∨
    q.offset.toNat + nq ≤ p.offset.toNat

structure Ready (before : GlobalState) (kp chain data : Pointer) (count : BitVec 64) : Prop where
  wf : before.WF
  chainRange : SmallRange before.mem chain 64
  dataRange : SmallRange before.mem data (128 * count.toNat)
  constantsRange : SmallRange before.mem kp 640
  positive : 0 < count.toNat
  constantsPtr : GlobalPtr before "fd_sha512_core_ref.K" kp
  constantsValue : readBits before.mem kp 5120 = constantsBytes
  constantsSeparate : chain.id ≠ kp.id
  inputDisjoint : Disjoint chain 64 data (128 * count.toNat)

/-- Exact caller-visible chaining-state replacement. No private stack identity
or final ring contents are observable at the call boundary. -/
def result (before : GlobalState) (chain data : Pointer) (count : BitVec 64) : BitVec 512 :=
  Agave.Ed25519.SHA512.Spec.run (readBits before.mem chain 512)
    (readBytes before.mem data (128 * count.toNat))

/-- The desired actual-call theorem, including return and the complete live
memory frame. This is a proposition to prove, never an axiom. -/
def Executes (before : GlobalState) (chain data : Pointer) (count : BitVec 64) : Prop :=
  ∃ after : GlobalState,
    StateT.run (runFunction (core.denote
      (Ctxt.Valuation.ofHVector [.value count, .value data, .value chain]ₕ))) before =
      .value (.nil, after) ∧
    after.WF ∧ after.alloc = before.alloc ∧ after.globals = before.globals ∧
    ∀ b, after.mem.live? b = (before.mem.splice chain (result before chain data count)).live? b

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource.Core
