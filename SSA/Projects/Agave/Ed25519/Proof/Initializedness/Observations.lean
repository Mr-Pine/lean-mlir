import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.PaddingMemory
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram

/-! Concrete-value independence at two actual machine-proof cutpoints.
These theorems do not equip RIR with LLVM undef/poison memory semantics and do
not assert a whole-verifier initializedness invariant. In particular, the
challenge's original memcpy does copy an unwritten buffer tail. -/
namespace Agave.Ed25519.Initializedness
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution
open Agave.Ed25519.Bridge.Challenge

/-- A full explicit write makes a subsequent same-range observation independent
of the previous concrete contents of either live allocation. -/
theorem full_overwrite_read_eq (m₁ m₂ : MemoryState) (p₁ p₂ : Pointer) (bits : Nat)
    (h₁ : Fits m₁ p₁ bits) (h₂ : Fits m₂ p₂ bits) (value : BitVec bits) :
    (m₁.storeAt p₁ value).readAt p₁ bits = (m₂.storeAt p₂ value).readAt p₂ bits := by
  rw [MemoryState.readAt_storeAt_self h₁, MemoryState.readAt_storeAt_self h₂]

/-- The original challenge copies 127 bytes after its two 32-byte input
copies. This instruction-level certificate does not replace those bytes with
zero or strengthen the source to an initialized memcpy. -/
theorem challenge_tail_copy (g : Agave.Ed25519.Verifier.Execution.Challenge.Globals) :
    (Agave.Ed25519.Verifier.Execution.Challenge.program.bb0 g).body[29]? = some (.memcpy (%18) (%17) (%2)) := by rfl

theorem challenge_first_copy (g : Agave.Ed25519.Verifier.Execution.Challenge.Globals) :
    (Agave.Ed25519.Verifier.Execution.Challenge.program.bb0 g).body[24]? = some (.memcpy (%17) (%arg2) (%1)) := by rfl

theorem challenge_second_copy (g : Agave.Ed25519.Verifier.Execution.Challenge.Globals) :
    (Agave.Ed25519.Verifier.Execution.Challenge.program.bb0 g).body[28]? = some (.memcpy (%20) (%arg1) (%1)) := by rfl

/-- The two defined input spans do not cover the copied 63-byte tail. -/
theorem challenge_tail_not_written (byte : Nat) (hlo : 64 ≤ byte) (hhi : byte < 127) :
    ¬ (byte < 32 ∨ (32 ≤ byte ∧ byte < 64)) := by omega

/-- The actual finalizer's padding stores inspect only the pending prefix.
Any unused source tail and any previous destination bytes may differ. -/
theorem padding_ignores_unused_bytes (m₁ m₂ : MemoryState)
    (src₁ src₂ buffer₁ buffer₂ : Pointer) (n : Nat) (hn : n < 128)
    (hs₁ : SmallRange m₁ src₁ n) (hs₂ : SmallRange m₂ src₂ n)
    (hb₁ : SmallRange m₁ buffer₁ 128) (hb₂ : SmallRange m₂ buffer₂ 128)
    (hne₁ : buffer₁.id ≠ src₁.id) (hne₂ : buffer₂.id ≠ src₂.id)
    (hprefix : Challenge.readBytes m₁ src₁ n = Challenge.readBytes m₂ src₂ n) :
    Challenge.readBytes (SHA512Finalization.padBuffer m₁ src₁ buffer₁ n) buffer₁ 128 =
      Challenge.readBytes (SHA512Finalization.padBuffer m₂ src₂ buffer₂ n) buffer₂ 128 := by
  rw [SHA512Finalization.padBuffer_bytes m₁ src₁ buffer₁ n hn hs₁ hb₁ hne₁,
    SHA512Finalization.padBuffer_bytes m₂ src₂ buffer₂ n hn hs₂ hb₂ hne₂, hprefix]

end Agave.Ed25519.Initializedness
