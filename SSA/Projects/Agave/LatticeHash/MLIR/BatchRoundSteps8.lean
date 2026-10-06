/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundBranches
import SSA.Projects.Agave.LatticeHash.MLIR.RoundCore

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound BatchRounds
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A complete round of the actual inlined batch block, reusing the checked
standalone instruction proof through the structural alpha-renaming. -/
theorem block8_20_round {α : Type}
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α)
    (V : Input8_20.Valuation) (A : agave_compress_pre_8.cfgCtx.Valuation)
    (msg sched : Pointer) (hA : RoundEnv8 A msg sched) (s : GlobalState)
    (r : Fin 7) (v m : State (Vector Word 8))
    (hV : V.comap rename8_20 =
      Ctxt.Valuation.ofHVector (headerAt8 (BitVec.ofNat 64 r.val) v).args.reverse ++ A)
    (hsi : ∀ i, Fits s.mem (schedulePtr sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.cfgBlock_20.denote V >>= fun z => K z.2) s =
      StateT.run (K (.inr (adapt8_20 V
        (if r.val = 6 then exitAt8 (roundFn gVectors v m r)
         else headerAt8 (BitVec.ofNat 64 (r.val+1)) (roundFn gVectors v m r))))) s := by
  rw [block8_20_transport, hV]
  exact round8_cont_run (fun z => K (z.map id (adapt8_20 V)))
    A msg sched hA s r v m hsi hsv hmi hmv

/-- A complete round of the actual inlined batch block, reusing the checked
standalone instruction proof through the structural alpha-renaming. -/
theorem block8_23_round {α : Type}
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α)
    (V : Input8_23.Valuation) (A : agave_compress_pre_8.cfgCtx.Valuation)
    (msg sched : Pointer) (hA : RoundEnv8 A msg sched) (s : GlobalState)
    (r : Fin 7) (v m : State (Vector Word 8))
    (hV : V.comap rename8_23 =
      Ctxt.Valuation.ofHVector (headerAt8 (BitVec.ofNat 64 r.val) v).args.reverse ++ A)
    (hsi : ∀ i, Fits s.mem (schedulePtr sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr8 msg i) 256)
    (hmv : ∀ i, readWord? (messagePtr8 msg i) 256 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_8.cfgBlock_23.denote V >>= fun z => K z.2) s =
      StateT.run (K (.inr (adapt8_23 V
        (if r.val = 6 then exitAt8 (roundFn gVectors v m r)
         else headerAt8 (BitVec.ofNat 64 (r.val+1)) (roundFn gVectors v m r))))) s := by
  rw [block8_23_transport, hV]
  exact round8_cont_run (fun z => K (z.map id (adapt8_23 V)))
    A msg sched hA s r v m hsi hsv hmi hmv

end AgaveLatticeHash.MLIR.BatchRoundBranches
