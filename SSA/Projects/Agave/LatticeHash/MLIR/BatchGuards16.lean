/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.MLIR.DenoteStep

namespace AgaveLatticeHash.MLIR.BatchGuards16
open LeanMLIR SLLVM
open InstCombine (LLVM)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev Input1 := blockInput agave_batch_16.cfgBlock_1

/-- The successful combined bounds check forwards the exact live state and
all sixteen source pointers to the checked transpose/load block. -/
def next1 (V : Input1.Valuation) : SuccArgs agave_batch_16.cfgSigs :=
  ⟨2, rfl, V ⟨59, rfl⟩ ::ₕ
    V ⟨58, rfl⟩ ::ₕ
    V ⟨57, rfl⟩ ::ₕ
    V ⟨56, rfl⟩ ::ₕ
    V ⟨55, rfl⟩ ::ₕ
    V ⟨54, rfl⟩ ::ₕ
    V ⟨53, rfl⟩ ::ₕ
    V ⟨52, rfl⟩ ::ₕ
    V ⟨51, rfl⟩ ::ₕ
    V ⟨50, rfl⟩ ::ₕ
    V ⟨49, rfl⟩ ::ₕ
    V ⟨48, rfl⟩ ::ₕ
    V ⟨47, rfl⟩ ::ₕ
    V ⟨46, rfl⟩ ::ₕ
    V ⟨45, rfl⟩ ::ₕ
    V ⟨44, rfl⟩ ::ₕ
    V ⟨43, rfl⟩ ::ₕ
    V ⟨42, rfl⟩ ::ₕ
    V ⟨41, rfl⟩ ::ₕ
    V ⟨40, rfl⟩ ::ₕ
    V ⟨39, rfl⟩ ::ₕ
    V ⟨38, rfl⟩ ::ₕ
    V ⟨37, rfl⟩ ::ₕ
    V ⟨36, rfl⟩ ::ₕ
    V ⟨35, rfl⟩ ::ₕ
    V ⟨34, rfl⟩ ::ₕ
    V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨15, rfl⟩ ::ₕ
    V ⟨14, rfl⟩ ::ₕ
    V ⟨13, rfl⟩ ::ₕ
    V ⟨12, rfl⟩ ::ₕ
    V ⟨11, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    V ⟨5, rfl⟩ ::ₕ
    V ⟨4, rfl⟩ ::ₕ
    V ⟨3, rfl⟩ ::ₕ
    V ⟨2, rfl⟩ ::ₕ
    V ⟨1, rfl⟩ ::ₕ
    V ⟨0, rfl⟩ ::ₕ .nil⟩

structure Env1 (V : Input1.Valuation) (offsets : Vector (BitVec 64) 15) : Prop where
  offset0 : V ⟨57, rfl⟩ = .value offsets[0]
  offset1 : V ⟨56, rfl⟩ = .value offsets[1]
  offset2 : V ⟨55, rfl⟩ = .value offsets[2]
  offset3 : V ⟨54, rfl⟩ = .value offsets[3]
  offset4 : V ⟨53, rfl⟩ = .value offsets[4]
  offset5 : V ⟨52, rfl⟩ = .value offsets[5]
  offset6 : V ⟨51, rfl⟩ = .value offsets[6]
  offset7 : V ⟨50, rfl⟩ = .value offsets[7]
  offset8 : V ⟨49, rfl⟩ = .value offsets[8]
  offset9 : V ⟨48, rfl⟩ = .value offsets[9]
  offset10 : V ⟨47, rfl⟩ = .value offsets[10]
  offset11 : V ⟨46, rfl⟩ = .value offsets[11]
  offset12 : V ⟨45, rfl⟩ = .value offsets[12]
  offset13 : V ⟨44, rfl⟩ = .value offsets[13]
  offset14 : V ⟨43, rfl⟩ = .value offsets[14]
  limit : V ⟨146, rfl⟩ = .value 1027#64

private theorem clearGuard (off : BitVec 64) (hb : off.toNat ≤ 960) :
    LLVM.icmp .ugt (.value off) (.value 1027#64) = .value 0#1 := by
  have hn : ¬1027 < off.toNat := by omega
  simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- None of the fifteen combined lane checks can take the panic edge when
all lane offsets satisfy the outer-loop bound. Memory is unchanged. -/
theorem block1_continue {α : Type} (V : Input1.Valuation) (s : GlobalState)
    (offsets : Vector (BitVec 64) 15) (hV : Env1 V offsets)
    (hb : ∀ i : Fin 15, offsets[i].toNat ≤ 960)
    (k : (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕
      SuccArgs agave_batch_16.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_16.cfgBlock_1.denote V >>= fun r => k r.2) s =
      StateT.run (k (.inr (next1 V))) s := by
  denote_step_all v
  denote_eval v 0 28
  have e0 : v0 = PoisonOr.value 0#1 := by
    rw [hv0, hV.offset0, hV.limit]
    exact clearGuard _ (hb 0)
  subst e0
  have e1 : v1 = PoisonOr.value 0#1 := by
    rw [hv1, hV.offset1, hV.limit]
    exact clearGuard _ (hb 1)
  subst e1
  have e2 : v2 = PoisonOr.value 0#1 := by
    rw [hv2, hV.offset2, hV.limit]
    exact clearGuard _ (hb 2)
  subst e2
  have e3 : v3 = PoisonOr.value 0#1 := by
    rw [hv3, hV.offset3, hV.limit]
    exact clearGuard _ (hb 3)
  subst e3
  have e4 : v4 = PoisonOr.value 0#1 := by
    rw [hv4, hV.offset4, hV.limit]
    exact clearGuard _ (hb 4)
  subst e4
  have e5 : v5 = PoisonOr.value 0#1 := by
    rw [hv5, hV.offset5, hV.limit]
    exact clearGuard _ (hb 5)
  subst e5
  have e6 : v6 = PoisonOr.value 0#1 := by
    rw [hv6, hV.offset6, hV.limit]
    exact clearGuard _ (hb 6)
  subst e6
  have e7 : v7 = PoisonOr.value 0#1 := by
    rw [hv7, hV.offset7, hV.limit]
    exact clearGuard _ (hb 7)
  subst e7
  have e8 : v8 = PoisonOr.value 0#1 := by
    rw [hv8, hV.offset8, hV.limit]
    exact clearGuard _ (hb 8)
  subst e8
  have e9 : v9 = PoisonOr.value 0#1 := by
    rw [hv9, hV.offset9, hV.limit]
    exact clearGuard _ (hb 9)
  subst e9
  have e10 : v10 = PoisonOr.value 0#1 := by
    rw [hv10, hV.offset10, hV.limit]
    exact clearGuard _ (hb 10)
  subst e10
  have e11 : v11 = PoisonOr.value 0#1 := by
    rw [hv11, hV.offset11, hV.limit]
    exact clearGuard _ (hb 11)
  subst e11
  have e12 : v12 = PoisonOr.value 0#1 := by
    rw [hv12, hV.offset12, hV.limit]
    exact clearGuard _ (hb 12)
  subst e12
  have e13 : v13 = PoisonOr.value 0#1 := by
    rw [hv13, hV.offset13, hV.limit]
    exact clearGuard _ (hb 13)
  subst e13
  have e14 : v14 = PoisonOr.value 0#1 := by
    rw [hv14, hV.offset14, hV.limit]
    exact clearGuard _ (hb 14)
  subst e14
  have e15 : v15 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv15
  subst e15
  have e16 : v16 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv16
  subst e16
  have e17 : v17 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv17
  subst e17
  have e18 : v18 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv18
  subst e18
  have e19 : v19 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv19
  subst e19
  have e20 : v20 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv20
  subst e20
  have e21 : v21 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv21
  subst e21
  have e22 : v22 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv22
  subst e22
  have e23 : v23 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv23
  subst e23
  have e24 : v24 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv24
  subst e24
  have e25 : v25 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv25
  subst e25
  have e26 : v26 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv26
  subst e26
  have e27 : v27 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv27
  subst e27
  have e28 : v28 = PoisonOr.value 0#1 := by
    simpa [LLVM.or, LLVM.or?] using hv28
  subst e28
  clear hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  simp only [next1]
  rfl

end AgaveLatticeHash.MLIR.BatchGuards16
