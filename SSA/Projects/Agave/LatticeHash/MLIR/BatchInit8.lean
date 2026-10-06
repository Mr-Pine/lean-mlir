/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.ByteSelect

namespace AgaveLatticeHash.MLIR.BatchInit8
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input19 := blockInput agave_batch_8.cfgBlock_19

/-- Reinterpret one packed CV register exactly as the compiled vector bitcast. -/
def unpackCV (x : Vector (PoisonOr (BitVec 64)) 4) : Vector (PoisonOr (BitVec 32)) 8 :=
  SLLVM.bitcast (.vector 4 (.bitvec (.concrete 64))) (.vector 8 (.bitvec (.concrete 32))) x

/-- The machine-vector representation recovers the original eight CV lanes. -/
theorem unpackCV_pack (v : Fin 8 → BitVec 32) :
    unpackCV ((packCV8 v).map PoisonOr.value) =
      (Vector.ofFn v).map PoisonOr.value := by
  unfold unpackCV
  have hd : LLVM.Ty.Defined (.vector 4 (.bitvec (.concrete 64)))
      ((packCV8 v).map PoisonOr.value) := by
    intro i
    show LLVM.Ty.ofBitvec (((packCV8 v).map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _
  rw [bitcast_of_defined hd]
  change LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 32)))
    (packBits (n := 4) (w := 64) (packCV8 v)) = _
  rw [BatchUpdate.packBits_packCV8]
  exact unflatten_packBits _

/-- The actual nonroot initialization successor: the eight unpacked CV
registers, IV, counter, length and flags, followed by all live caller values. -/
def next19 (V : Input19.Valuation) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨20, rfl,
    V ⟨78, rfl⟩ ::ₕ
    unpackCV (V ⟨5, rfl⟩) ::ₕ unpackCV (V ⟨6, rfl⟩) ::ₕ
    unpackCV (V ⟨7, rfl⟩) ::ₕ unpackCV (V ⟨8, rfl⟩) ::ₕ
    unpackCV (V ⟨9, rfl⟩) ::ₕ unpackCV (V ⟨10, rfl⟩) ::ₕ
    unpackCV (V ⟨11, rfl⟩) ::ₕ unpackCV (V ⟨12, rfl⟩) ::ₕ
    V ⟨61, rfl⟩ ::ₕ V ⟨60, rfl⟩ ::ₕ V ⟨59, rfl⟩ ::ₕ V ⟨58, rfl⟩ ::ₕ
    V ⟨74, rfl⟩ ::ₕ V ⟨74, rfl⟩ ::ₕ V ⟨0, rfl⟩ ::ₕ V ⟨1, rfl⟩ ::ₕ
    V ⟨12, rfl⟩ ::ₕ V ⟨11, rfl⟩ ::ₕ V ⟨10, rfl⟩ ::ₕ V ⟨9, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ V ⟨7, rfl⟩ ::ₕ V ⟨6, rfl⟩ ::ₕ V ⟨5, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ V ⟨3, rfl⟩ ::ₕ V ⟨2, rfl⟩ ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Execute every actual CV bitcast and the branch, preserving memory and
allowing an arbitrary effectful continuation into round block20. -/
theorem block19_continue {α : Type} (V : Input19.Valuation) (s : GlobalState)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_19.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next19 V))) s := by
  denote_step_all v
  denote_eval v 0 7
  rw [hv7, hv6, hv5, hv4, hv3, hv2, hv1, hv0]
  simp only [BlockCom.denote_term, Terminator.denote_br, Target.denote]
  rfl

end AgaveLatticeHash.MLIR.BatchInit8
