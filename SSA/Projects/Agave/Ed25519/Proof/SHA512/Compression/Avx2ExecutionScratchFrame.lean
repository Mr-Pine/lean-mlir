import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairStep

/-! Memory frames for composing the thirty-two concrete scratch stores.
All disjoint reads and all existing live ranges are retained. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Spec

/-- A scratch-only update preserves the allocator, every read outside the
128-byte scratch range, and every previously live small range. -/
structure ScratchFrame (scratch : Pointer) (before after : GlobalState) : Prop where
  alloc : after.alloc = before.alloc
  read : ∀ (p : Pointer) (w : Nat),
    (Range.of scratch 1024).Disjoint (Range.of p w) →
      after.mem.readAt p w = before.mem.readAt p w
  live : ∀ {p : Pointer} {bytes : Nat},
    SmallRange before.mem p bytes → SmallRange after.mem p bytes

theorem ScratchFrame.refl (scratch : Pointer) (mem : GlobalState) :
    ScratchFrame scratch mem mem :=
  ⟨rfl, fun _ _ _ => rfl, fun h => h⟩

theorem ScratchFrame.trans {scratch : Pointer} {mem₀ mem₁ mem₂ : GlobalState}
    (h₀ : ScratchFrame scratch mem₀ mem₁) (h₁ : ScratchFrame scratch mem₁ mem₂) :
    ScratchFrame scratch mem₀ mem₂ :=
  ⟨h₁.alloc.trans h₀.alloc,
    fun p w hd => (h₁.read p w hd).trans (h₀.read p w hd),
    fun h => h₁.live (h₀.live h)⟩

/-- The exact 128-bit bb5 store has the full scratch frame property. -/
theorem pairStoreState_frame (mem : GlobalState) (scratch : Pointer) (j : Nat)
    (lo hi : Word) (hs : SmallRange mem.mem scratch 128) (hj : j < 8) :
    ScratchFrame scratch mem (pairStoreState mem scratch j lo hi) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro p w hd
    exact pairStoreState_read_disjoint mem scratch p j lo hi w hs hj hd
  · intro p bytes hp
    exact hp.storeAt (scratch.add (BitVec.ofNat 64 (16*j))) (hi ++ lo)

/-- The standard-schedule specialization has the same concrete memory frame. -/
theorem pairSpecMem_frame (mem : GlobalState) (scratch : Pointer) (r j : Nat)
    (block : Bytes) (hs : SmallRange mem.mem scratch 128) (hj : j < 8) :
    ScratchFrame scratch mem (pairSpecMem mem scratch r j block) :=
  pairStoreState_frame mem scratch j (scheduleKW (schedule block) (r+16))
    (scheduleKW (schedule block) (r+17)) hs hj

end Agave.Ed25519.SHA512.Execution.Avx2
