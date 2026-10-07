import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.InitializerLink
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.DispatchExecutionEntry
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionEntry

/-! The data/readiness linkage reaches actual imported CFG steps: the loaded
cold sentinel selects the dispatcher initializer branch, and the challenge
entry copies the imported standard IV into its newly allocated SHA context.
No initializer or compression call result is assumed by either entry step. -/

namespace Agave.Ed25519.SHA512.Execution.Dispatch
open LeanMLIR.RIR
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

/-- Bind both emitted source global addresses to the actual installed data. -/
def sourceGlobals (g : ShaSourceGlobals) : Globals :=
  ⟨g.compression.cachePtr, g.compression.constantsPtr⟩

/-- Exact execution of the imported dispatcher entry after source loading:
the cache byte is 255, so block 1 is the next original CFG block. -/
theorem installed_dispatch_entry (p : Primitives) (s : GlobalState) (E : Env program.Γ) :
    (program p (sourceGlobals (installedShaGlobals s))).runFrom E 0 (installShaSource s) =
      (program p (sourceGlobals (installedShaGlobals s))).runFrom
        (dispatchEntryEnv E (sourceGlobals (installedShaGlobals s)) 255) 1
        (installShaSource s) := by
  have h := (installShaSource_ready s).compression
  have hr := (installShaSource_cold_cache s).readAt
  exact dispatch_entry_runFrom p _ E _ 255 h.constants_range h.cache_range hr

end Agave.Ed25519.SHA512.Execution.Dispatch

namespace Agave.Ed25519.Verifier.Execution.Challenge
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open SHA512Finalization

/-- Source loading supplies the actual challenge entry's IV range and byte
premises. The existing imported execution theorem initializes the SHA context
and records its first length branch. -/
theorem entry_block_of_source_ready (p : Primitives) (g : ShaSourceGlobals)
    (sha : Sha512Model) (E : Env program.Γ) (s : GlobalState) (rptr aptr : Pointer)
    (r a : BitVec 256) (n : BitVec 64)
    (hR : E.read (%arg2) = .value rptr) (hA : E.read (%arg1) = .value aptr)
    (hn : E.read (%arg4) = .value n) (hwf : s.WF)
    (hr : SmallRange s.mem rptr 32) (ha : SmallRange s.mem aptr 32)
    (hrbytes : s.mem.readAt rptr 256 = r) (habytes : s.mem.readAt aptr 256 = a)
    (hglobals : ShaSourceReady g s) :
    (program p ⟨g.ivPtr⟩).runFrom E 0 s =
      (program p ⟨g.ivPtr⟩).runFrom (entryEnv E ⟨g.ivPtr⟩ s n)
        (if n.toNat < 64 then 2 else 1) (entryState s r a) ∧
      ShaSourceReady g (entryState s r a) := by
  exact ⟨entry_block p ⟨g.ivPtr⟩ sha E s rptr aptr r a n hR hA hn hwf
    hr ha hrbytes habytes hglobals.iv_entry.1 hglobals.iv_entry.2,
    hglobals.of_frame s.alloc.nextFreeBlock (entry_frame s hwf r a)⟩

end Agave.Ed25519.Verifier.Execution.Challenge
