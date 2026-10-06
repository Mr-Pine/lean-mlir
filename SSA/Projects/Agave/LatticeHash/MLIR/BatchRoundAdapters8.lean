/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_8

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section

private abbrev input {Γ Δ : Ctxt SLLVM.Ty} {rs ss} (_ : BlockCom Γ Δ rs ss) := Γ

abbrev Input8_20 := input agave_batch_8.cfgBlock_20
def extras8_20 (V : Input8_20.Valuation) :
    HVector TyDenote.toType [SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 4 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 1))] :=
  (V ⟨10, rfl⟩ ::ₕ
   V ⟨9, rfl⟩ ::ₕ
   V ⟨8, rfl⟩ ::ₕ
   V ⟨7, rfl⟩ ::ₕ
   V ⟨6, rfl⟩ ::ₕ
   V ⟨5, rfl⟩ ::ₕ
   V ⟨4, rfl⟩ ::ₕ
   V ⟨3, rfl⟩ ::ₕ
   V ⟨2, rfl⟩ ::ₕ
   V ⟨1, rfl⟩ ::ₕ
   V ⟨0, rfl⟩ ::ₕ .nil)

/-- Adapt the standalone round successor while preserving the caller's threaded values. -/
def adapt8_20 (V : Input8_20.Valuation)
    (t : SuccArgs agave_compress_pre_8.cfgSigs) : SuccArgs agave_batch_8.cfgSigs := by
  rcases t with ⟨idx, hi, args⟩
  rename_i ts
  cases idx with
  | zero =>
    have ht := Option.some.inj hi
    subst ts
    exact ⟨20, rfl, args.append (extras8_20 V)⟩
  | succ idx =>
    cases idx with
    | zero =>
      have ht := Option.some.inj hi
      subst ts
      exact ⟨21, rfl, (extras8_20 V).append args⟩
    | succ idx => simp [agave_compress_pre_8.cfgSigs] at hi

abbrev Input8_23 := input agave_batch_8.cfgBlock_23
def extras8_23 (V : Input8_23.Valuation) :
    HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.arith (.vector 8 (.bitvec 32)), SLLVM.Ty.ptr, SLLVM.Ty.bitvec 64] :=
  (V ⟨19, rfl⟩ ::ₕ
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
   V ⟨0, rfl⟩ ::ₕ .nil)

/-- Adapt the standalone round successor while preserving the caller's threaded values. -/
def adapt8_23 (V : Input8_23.Valuation)
    (t : SuccArgs agave_compress_pre_8.cfgSigs) : SuccArgs agave_batch_8.cfgSigs := by
  rcases t with ⟨idx, hi, args⟩
  rename_i ts
  cases idx with
  | zero =>
    have ht := Option.some.inj hi
    subst ts
    exact ⟨23, rfl, args.append (extras8_23 V)⟩
  | succ idx =>
    cases idx with
    | zero =>
      have ht := Option.some.inj hi
      subst ts
      exact ⟨24, rfl, (extras8_23 V).append args⟩
    | succ idx => simp [agave_compress_pre_8.cfgSigs] at hi

@[simp] theorem adapt8_20_loop (V : Input8_20.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_8.cfgSigs[0]) :
    adapt8_20 V ⟨0, rfl, args⟩ = ⟨20, rfl, args.append (extras8_20 V)⟩ := rfl

@[simp] theorem adapt8_20_exit (V : Input8_20.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_8.cfgSigs[1]) :
    adapt8_20 V ⟨1, rfl, args⟩ = ⟨21, rfl, (extras8_20 V).append args⟩ := rfl

@[simp] theorem adapt8_23_loop (V : Input8_23.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_8.cfgSigs[0]) :
    adapt8_23 V ⟨0, rfl, args⟩ = ⟨23, rfl, args.append (extras8_23 V)⟩ := rfl

@[simp] theorem adapt8_23_exit (V : Input8_23.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_8.cfgSigs[1]) :
    adapt8_23 V ⟨1, rfl, args⟩ = ⟨24, rfl, (extras8_23 V).append args⟩ := rfl

end
end AgaveLatticeHash.MLIR.BatchRoundBranches
