/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerPacking
import SSA.Projects.Agave.LatticeHash.Blake3Reference

namespace AgaveLatticeHash.MLIR.CallerMemory

/-- The retained-memory batch result is the fold of independent portable
2048-byte LtHash results. Short-message and padding requirements are derived
from physical staging, so no opaque long-message hash occurs in this boundary.
An actual batch readback theorem can rewrite its result with this equality. -/
theorem physicalUpdate_eq_portableLtHash (n : Nat) (hn : 0 < n)
    (perm : AgaveLattice.Matrix) (hp : AgaveLattice.IsTranspose n perm)
    (p : AgavePhysicalStaging.Store) (s : AgaveStaging.Impl)
    (hr : AgavePhysicalStaging.Represents p s) (hfull : p.count = n)
    (hs : AgaveStaging.PendingOK s) (a : AgaveStaging.Value) :
    let ms : Fin n → AgaveConcrete.Message := fun lane =>
      AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hfull) lane)
    AgavePhysicalStaging.physicalUpdate n hn perm p a =
      (List.finRange n).foldl (fun z lane => AgaveStaging.plus z
        ((AgaveBlake3Reference.portableLtHash (ms lane)).getD AgaveStaging.zero)) a := by
  let ms : Fin n → AgaveConcrete.Message := fun lane =>
    AgaveConcrete.toBytes (AgaveConcrete.messagesOf s.pending (hr.count.symm.trans hfull) lane)
  obtain ⟨hl, hm, hstage⟩ := represented_messages n p s hr hfull hs
  have hlengths : (fun lane : Fin n => AgavePhysicalStaging.lengthAt p lane.val) =
      (fun lane => (ms lane).length) := funext hl
  change AgavePhysicalStaging.physicalUpdate n hn perm p a = _
  unfold AgavePhysicalStaging.physicalUpdate
  rw [hlengths, AgavePhysicalStaging.retainedUpdate_eq_canonical hn hp ms _ hm hstage,
    AgaveBlake3Reference.simdUpdate_eq_portableReference hn hp ms hm a]

end AgaveLatticeHash.MLIR.CallerMemory
