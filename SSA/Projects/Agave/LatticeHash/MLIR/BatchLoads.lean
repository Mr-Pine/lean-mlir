/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Firedancer.Proof.Tactics

namespace AgaveLatticeHash.MLIR.BatchLoads
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)

private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
private abbrev blockOutput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γout

def rowPtr (p : Pointer) (word : BitVec 64) := p.withOffset (word * 4)

abbrev Input10 := blockInput agave_batch_8.cfgBlock_10
noncomputable def next10 (V : Input10.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨11, rfl, V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    row.map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Execute the actual source bb11: initialized bytes determine the load;
the next-lane bound excludes its panic edge. All incoming SSA values survive. -/
theorem block10_continue {α : Type} (V : Input10.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨128, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨14, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨13, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨81, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_10).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_10.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next10 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 10
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 0 10
  have e : v2 = PoisonOr.value 0#1 := by
    rw [hv2, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input11 := blockInput agave_batch_8.cfgBlock_11
noncomputable def next11 (V : Input11.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨12, rfl, V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    row.map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Execute the actual source bb12: initialized bytes determine the load;
the next-lane bound excludes its panic edge. All incoming SSA values survive. -/
theorem block11_continue {α : Type} (V : Input11.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨13, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨12, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨82, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_11).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_11.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next11 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 10
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 0 10
  have e : v2 = PoisonOr.value 0#1 := by
    rw [hv2, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input12 := blockInput agave_batch_8.cfgBlock_12
noncomputable def next12 (V : Input12.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨13, rfl, V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    row.map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Execute the actual source bb13: initialized bytes determine the load;
the next-lane bound excludes its panic edge. All incoming SSA values survive. -/
theorem block12_continue {α : Type} (V : Input12.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨12, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨11, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨83, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_12).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_12.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next12 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 10
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 0 10
  have e : v2 = PoisonOr.value 0#1 := by
    rw [hv2, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input13 := blockInput agave_batch_8.cfgBlock_13
noncomputable def next13 (V : Input13.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨14, rfl, V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    row.map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Execute the actual source bb14: initialized bytes determine the load;
the next-lane bound excludes its panic edge. All incoming SSA values survive. -/
theorem block13_continue {α : Type} (V : Input13.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨11, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨10, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨84, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_13).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_13.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next13 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 10
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 0 10
  have e : v2 = PoisonOr.value 0#1 := by
    rw [hv2, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input14 := blockInput agave_batch_8.cfgBlock_14
noncomputable def next14 (V : Input14.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨15, rfl, V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    row.map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Execute the actual source bb15: initialized bytes determine the load;
the next-lane bound excludes its panic edge. All incoming SSA values survive. -/
theorem block14_continue {α : Type} (V : Input14.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨10, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨9, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨85, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_14).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_14.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next14 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 10
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 0 10
  have e : v2 = PoisonOr.value 0#1 := by
    rw [hv2, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input15 := blockInput agave_batch_8.cfgBlock_15
noncomputable def next15 (V : Input15.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨16, rfl, V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    row.map PoisonOr.value ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Execute the actual source bb16: initialized bytes determine the load;
the next-lane bound excludes its panic edge. All incoming SSA values survive. -/
theorem block15_continue {α : Type} (V : Input15.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨52, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨9, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨8, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨86, rfl⟩ = PoisonOr.value 1027#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_15).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_15.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next15 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 10
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 0 10
  have e : v2 = PoisonOr.value 0#1 := by
    rw [hv2, ho, hl]
    have hn : ¬1027 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input2 := blockInput agave_batch_8.cfgBlock_2
noncomputable def bump2 (V : Input2.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨21, rfl⟩) (V ⟨87, rfl⟩) {nsw := true, nuw := true}
noncomputable def next2 (V : Input2.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨3, rfl, V ⟨35, rfl⟩ ::ₕ
    V ⟨34, rfl⟩ ::ₕ
    V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    row.map PoisonOr.value ::ₕ
    bump2 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb3, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block2_continue {α : Type} (V : Input2.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨135, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨22, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨86, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_2).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_2.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump2 V ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next2 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 0
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    change v0 = gep (V ⟨135, rfl⟩) 4 0 (V ⟨0, rfl⟩) at hv0
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 2 3
  have ea : v2 = bump2 V := hv2
  subst ea
  have e : v3 = PoisonOr.value 0#1 := by
    rw [hv3, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input3 := blockInput agave_batch_8.cfgBlock_3
noncomputable def bump3 (V : Input3.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨20, rfl⟩) (V ⟨86, rfl⟩) {nsw := true, nuw := true}
noncomputable def next3 (V : Input3.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨4, rfl, V ⟨34, rfl⟩ ::ₕ
    V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    row.map PoisonOr.value ::ₕ
    bump3 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb4, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block3_continue {α : Type} (V : Input3.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨57, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨21, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨85, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_3).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_3.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump3 V ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next3 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 0
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    change v0 = gep (V ⟨57, rfl⟩) 4 0 (V ⟨0, rfl⟩) at hv0
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 2 3
  have ea : v2 = bump3 V := hv2
  subst ea
  have e : v3 = PoisonOr.value 0#1 := by
    rw [hv3, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input4 := blockInput agave_batch_8.cfgBlock_4
noncomputable def bump4 (V : Input4.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨19, rfl⟩) (V ⟨85, rfl⟩) {nsw := true, nuw := true}
noncomputable def next4 (V : Input4.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨5, rfl, V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    row.map PoisonOr.value ::ₕ
    bump4 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb5, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block4_continue {α : Type} (V : Input4.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨55, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨20, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨84, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_4).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_4.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump4 V ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next4 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 0
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    change v0 = gep (V ⟨55, rfl⟩) 4 0 (V ⟨0, rfl⟩) at hv0
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 2 3
  have ea : v2 = bump4 V := hv2
  subst ea
  have e : v3 = PoisonOr.value 0#1 := by
    rw [hv3, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input5 := blockInput agave_batch_8.cfgBlock_5
noncomputable def bump5 (V : Input5.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨18, rfl⟩) (V ⟨84, rfl⟩) {nsw := true, nuw := true}
noncomputable def next5 (V : Input5.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨6, rfl, V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    row.map PoisonOr.value ::ₕ
    bump5 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb6, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block5_continue {α : Type} (V : Input5.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨53, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨19, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨83, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_5).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_5.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump5 V ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next5 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 0
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    change v0 = gep (V ⟨53, rfl⟩) 4 0 (V ⟨0, rfl⟩) at hv0
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 2 3
  have ea : v2 = bump5 V := hv2
  subst ea
  have e : v3 = PoisonOr.value 0#1 := by
    rw [hv3, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input6 := blockInput agave_batch_8.cfgBlock_6
noncomputable def bump6 (V : Input6.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨17, rfl⟩) (V ⟨83, rfl⟩) {nsw := true, nuw := true}
noncomputable def next6 (V : Input6.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨7, rfl, V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
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
    row.map PoisonOr.value ::ₕ
    bump6 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb7, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block6_continue {α : Type} (V : Input6.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨51, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨18, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨82, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_6).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_6.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump6 V ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next6 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 0
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    change v0 = gep (V ⟨51, rfl⟩) 4 0 (V ⟨0, rfl⟩) at hv0
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 2 3
  have ea : v2 = bump6 V := hv2
  subst ea
  have e : v3 = PoisonOr.value 0#1 := by
    rw [hv3, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input7 := blockInput agave_batch_8.cfgBlock_7
noncomputable def bump7 (V : Input7.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨16, rfl⟩) (V ⟨82, rfl⟩) {nsw := true, nuw := true}
noncomputable def next7 (V : Input7.Valuation) (row : Vector (BitVec 32) 8) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨8, rfl, V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
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
    row.map PoisonOr.value ::ₕ
    bump7 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb8, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block7_continue {α : Type} (V : Input7.Valuation) (s : GlobalState)
    (p : Pointer) (word off : BitVec 64) (row : Vector (BitVec 32) 8)
    (hp : V ⟨49, rfl⟩ = PoisonOr.value p)
    (hi : V ⟨0, rfl⟩ = PoisonOr.value word)
    (ho : V ⟨17, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨81, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (hf : Fits s.mem (rowPtr p word) 256)
    (hr : readWord? (rowPtr p word) 256 s.mem = some (packBits row))
    (k : (blockOutput agave_batch_8.cfgBlock_7).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_7.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump7 V ::ᵥ row.map PoisonOr.value ::ᵥ
        PoisonOr.value (rowPtr p word) ::ᵥ V, .inr (next7 V row))) s := by
  denote_step_all v 0
  denote_eval v 0 0
  have e0 : v0 = PoisonOr.value (rowPtr p word) := by
    change v0 = gep (V ⟨49, rfl⟩) 4 0 (V ⟨0, rfl⟩) at hv0
    rw [hv0, hp, hi]
    simp [gep, ptradd, rowPtr, Pointer.withOffset, LLVM.add, LLVM.mul,
      LLVM.const?, LLVM.add?, LLVM.mul?]
  subst e0
  clear hv0
  peel_load_vector row, (rowPtr p word), hf, hr, s
  denote_step_all v
  denote_eval v 2 3
  have ea : v2 = bump7 V := hv2
  subst ea
  have e : v3 = PoisonOr.value 0#1 := by
    rw [hv3, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

abbrev Input8 := blockInput agave_batch_8.cfgBlock_8
noncomputable def bump8 (V : Input8.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨15, rfl⟩) (V ⟨81, rfl⟩) {nsw := true, nuw := true}
noncomputable def next8 (V : Input8.Valuation)  :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨9, rfl, V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨21, rfl⟩ ::ₕ
    V ⟨20, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
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
    V ⟨0, rfl⟩ ::ₕ
    bump8 V ::ₕ .nil⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Exact execution of source bb9, with its next-lane guard derived from
the bounded offset invariant and all surviving phi values retained. -/
theorem block8_continue {α : Type} (V : Input8.Valuation) (s : GlobalState)
    (off : BitVec 64)
    (ho : V ⟨16, rfl⟩ = PoisonOr.value off)
    (hl : V ⟨80, rfl⟩ = PoisonOr.value 995#64)
    (hb : off.toNat ≤ 960)
    (k : (blockOutput agave_batch_8.cfgBlock_8).Valuation ×
      (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) → EffectM α) :
    StateT.run (agave_batch_8.cfgBlock_8.denote V >>= k) s =
      StateT.run (k (PoisonOr.value 0#1 ::ᵥ bump8 V ::ᵥ V, .inr (next8 V))) s := by
  denote_step_all v
  denote_eval v 0 1
  have ea : v0 = bump8 V := hv0
  subst ea
  have e : v1 = PoisonOr.value 0#1 := by
    rw [hv1, ho, hl]
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  subst e
  simp only [BlockCom.denote, Terminator.denote, Target.denote]
  rfl

/-- A word-indexed AVX2 row fits within one 1024-byte input lane slot. -/
theorem rowPtr_fits {s : GlobalState} {p : Pointer} (hp : Fits s.mem p 8192)
    (word : BitVec 64) (hw : word.toNat ≤ 248) :
    Fits s.mem (rowPtr p word) 256 := by
  have ho : (word * 4).toNat ≤ 992 := by
    simp only [BitVec.toNat_mul] at *
    have hm := Nat.mod_le (word.toNat * 4) (2 ^ 64)
    norm_num at hm ⊢
    omega
  exact Firedancer.Fits.mono (remainingFits s.mem p hp (word * 4) (by omega)) (by omega)

/-- Both half-row reads fit at any bounded loop offset, including stalled
lanes at their final block. No branch-success premise is needed. -/
theorem rowPtr_fits_halves {s : GlobalState} {p : Pointer} (hp : Fits s.mem p 8192)
    (offset half : Nat) (hoff : offset ≤ 960) (hh : half ≤ 1) :
    Fits s.mem (rowPtr p (BitVec.ofNat 64 (offset / 4 + 8 * half))) 256 := by
  apply rowPtr_fits hp
  simp only [BitVec.toNat_ofNat]
  have hb : offset / 4 + 8 * half ≤ 248 := by omega
  have := Nat.mod_le (offset / 4 + 8 * half) (2 ^ 64)
  omega

/-- The emitted word-address GEP is the expected byte address for aligned
block offsets. -/
theorem rowPtr_halves (p : Pointer) (offset half : Nat) (hoff : offset % 4 = 0) :
    rowPtr p (BitVec.ofNat 64 (offset / 4 + 8 * half)) =
      p.withOffset (BitVec.ofNat 64 (offset + 32 * half)) := by
  unfold rowPtr
  congr 1
  have hn : (offset / 4 + 8 * half) * 4 = offset + 32 * half := by omega
  rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_mul, hn]

/-- Both `nsw` and `nuw` flags on the second-half word offset are satisfied
by the loop invariant. -/
theorem addEight_safe (word : BitVec 64) (hw : word.toNat ≤ 240) :
    LLVM.add (.value word) (.value 8#64) {nsw := true, nuw := true} =
      PoisonOr.value (word + 8) := by
  have hi : word.toInt = (word.toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : word.saddOverflow 8#64 = false := by
    simp only [BitVec.saddOverflow, hi]
    norm_num
    omega
  have hu : word.uaddOverflow 8#64 = false := by
    simp only [BitVec.uaddOverflow]
    norm_num
    omega
  simp [LLVM.add, LLVM.add?, hs, hu]

@[simp] theorem next2_idx (V : Input2.Valuation) (row : Vector (BitVec 32) 8) :
    (next2 V row).idx = 3 := rfl

@[simp] theorem next3_idx (V : Input3.Valuation) (row : Vector (BitVec 32) 8) :
    (next3 V row).idx = 4 := rfl

@[simp] theorem next4_idx (V : Input4.Valuation) (row : Vector (BitVec 32) 8) :
    (next4 V row).idx = 5 := rfl

@[simp] theorem next5_idx (V : Input5.Valuation) (row : Vector (BitVec 32) 8) :
    (next5 V row).idx = 6 := rfl

@[simp] theorem next6_idx (V : Input6.Valuation) (row : Vector (BitVec 32) 8) :
    (next6 V row).idx = 7 := rfl

@[simp] theorem next7_idx (V : Input7.Valuation) (row : Vector (BitVec 32) 8) :
    (next7 V row).idx = 8 := rfl

@[simp] theorem next8_idx (V : Input8.Valuation) :
    (next8 V).idx = 9 := rfl

@[simp] theorem next10_idx (V : Input10.Valuation) (row : Vector (BitVec 32) 8) :
    (next10 V row).idx = 11 := rfl

@[simp] theorem next11_idx (V : Input11.Valuation) (row : Vector (BitVec 32) 8) :
    (next11 V row).idx = 12 := rfl

@[simp] theorem next12_idx (V : Input12.Valuation) (row : Vector (BitVec 32) 8) :
    (next12 V row).idx = 13 := rfl

@[simp] theorem next13_idx (V : Input13.Valuation) (row : Vector (BitVec 32) 8) :
    (next13 V row).idx = 14 := rfl

@[simp] theorem next14_idx (V : Input14.Valuation) (row : Vector (BitVec 32) 8) :
    (next14 V row).idx = 15 := rfl

@[simp] theorem next15_idx (V : Input15.Valuation) (row : Vector (BitVec 32) 8) :
    (next15 V row).idx = 16 := rfl

end AgaveLatticeHash.MLIR.BatchLoads
