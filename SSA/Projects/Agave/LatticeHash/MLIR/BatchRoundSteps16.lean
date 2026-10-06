/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundBranches16
import SSA.Projects.Agave.LatticeHash.MLIR.RoundCore16

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionRound BatchRounds
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

/-- A complete round of the actual inlined batch block, reusing the checked
standalone instruction proof through the structural alpha-renaming. -/
theorem block16_7_round {α : Type}
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α)
    (V : Input16_7.Valuation) (A : agave_compress_pre_16.cfgCtx.Valuation)
    (msg sched : Pointer) (hA : RoundEnv16 A msg sched) (s : GlobalState)
    (r : Fin 7) (v m : State (Vector Word 16))
    (hV : V.comap rename16_7 =
      Ctxt.Valuation.ofHVector (headerAt16 (BitVec.ofNat 64 r.val) v).args.reverse ++ A)
    (hsi : ∀ i, Fits s.mem (schedulePtr16 sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr16 sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_16.cfgBlock_7.denote V >>= fun z => K z.2) s =
      StateT.run (K (.inr (adapt16_7 V
        (if r.val = 6 then exitAt16 (roundFn gVectors v m r)
         else headerAt16 (BitVec.ofNat 64 (r.val+1)) (roundFn gVectors v m r))))) s := by
  rw [block16_7_transport, hV]
  exact round16_cont_run (fun z => K (z.map id (adapt16_7 V)))
    A msg sched hA s r v m hsi hsv hmi hmv

/-- A complete round of the actual inlined batch block, reusing the checked
standalone instruction proof through the structural alpha-renaming. -/
theorem block16_10_round {α : Type}
    (K : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α)
    (V : Input16_10.Valuation) (A : agave_compress_pre_16.cfgCtx.Valuation)
    (msg sched : Pointer) (hA : RoundEnv16 A msg sched) (s : GlobalState)
    (r : Fin 7) (v m : State (Vector Word 16))
    (hV : V.comap rename16_10 =
      Ctxt.Valuation.ofHVector (headerAt16 (BitVec.ofNat 64 r.val) v).args.reverse ++ A)
    (hsi : ∀ i, Fits s.mem (schedulePtr16 sched r i) 64)
    (hsv : ∀ i, readWord? (schedulePtr16 sched r i) 64 s.mem =
      some (BitVec.ofNat 64 (schedule r i).val))
    (hmi : ∀ i, Fits s.mem (messagePtr16 msg i) 512)
    (hmv : ∀ i, readWord? (messagePtr16 msg i) 512 s.mem = some (packBits (m i))) :
    StateT.run (agave_batch_16.cfgBlock_10.denote V >>= fun z => K z.2) s =
      StateT.run (K (.inr (adapt16_10 V
        (if r.val = 6 then exitAt16 (roundFn gVectors v m r)
         else headerAt16 (BitVec.ofNat 64 (r.val+1)) (roundFn gVectors v m r))))) s := by
  rw [block16_10_transport, hV]
  exact round16_cont_run (fun z => K (z.map id (adapt16_10 V)))
    A msg sched hA s r v m hsi hsv hmi hmv

end AgaveLatticeHash.MLIR.BatchRoundBranches
