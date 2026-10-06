/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_16

namespace AgaveLatticeHash.MLIR.BatchRoundBranches
open LeanMLIR SLLVM
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
noncomputable section

private abbrev input {Γ Δ : Ctxt SLLVM.Ty} {rs ss} (_ : BlockCom Γ Δ rs ss) := Γ

abbrev Input16_7 := input agave_batch_16.cfgBlock_7
def extras16_7 (V : Input16_7.Valuation) :
    HVector TyDenote.toType [SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.arith (.vector 8 (.bitvec 64)), SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.bitvec 64, SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 8))] :=
  (V ⟨26, rfl⟩ ::ₕ
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
   V ⟨0, rfl⟩ ::ₕ .nil)

/-- Adapt the standalone round successor while preserving every threaded caller value. -/
def adapt16_7 (V : Input16_7.Valuation)
    (t : SuccArgs agave_compress_pre_16.cfgSigs) : SuccArgs agave_batch_16.cfgSigs := by
  rcases t with ⟨idx, hi, args⟩
  rename_i ts
  cases idx with
  | zero =>
    have ht := Option.some.inj hi
    subst ts
    exact ⟨7, rfl, args.append (extras16_7 V)⟩
  | succ idx =>
    cases idx with
    | zero =>
      have ht := Option.some.inj hi
      subst ts
      exact ⟨8, rfl, (extras16_7 V).append args⟩
    | succ idx => simp [agave_compress_pre_16.cfgSigs] at hi

abbrev Input16_10 := input agave_batch_16.cfgBlock_10
def extras16_10 (V : Input16_10.Valuation) :
    HVector TyDenote.toType [SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.arith (.vector 16 (.bitvec 32)), SLLVM.Ty.bitvec 64] :=
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

/-- Adapt the standalone round successor while preserving every threaded caller value. -/
def adapt16_10 (V : Input16_10.Valuation)
    (t : SuccArgs agave_compress_pre_16.cfgSigs) : SuccArgs agave_batch_16.cfgSigs := by
  rcases t with ⟨idx, hi, args⟩
  rename_i ts
  cases idx with
  | zero =>
    have ht := Option.some.inj hi
    subst ts
    exact ⟨10, rfl, args.append (extras16_10 V)⟩
  | succ idx =>
    cases idx with
    | zero =>
      have ht := Option.some.inj hi
      subst ts
      exact ⟨11, rfl, (extras16_10 V).append args⟩
    | succ idx => simp [agave_compress_pre_16.cfgSigs] at hi

@[simp] theorem adapt16_7_loop (V : Input16_7.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_16.cfgSigs[0]) :
    adapt16_7 V ⟨0, rfl, args⟩ = ⟨7, rfl, args.append (extras16_7 V)⟩ := rfl

@[simp] theorem adapt16_7_exit (V : Input16_7.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_16.cfgSigs[1]) :
    adapt16_7 V ⟨1, rfl, args⟩ = ⟨8, rfl, (extras16_7 V).append args⟩ := rfl

@[simp] theorem adapt16_10_loop (V : Input16_10.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_16.cfgSigs[0]) :
    adapt16_10 V ⟨0, rfl, args⟩ = ⟨10, rfl, args.append (extras16_10 V)⟩ := rfl

@[simp] theorem adapt16_10_exit (V : Input16_10.Valuation)
    (args : HVector TyDenote.toType agave_compress_pre_16.cfgSigs[1]) :
    adapt16_10 V ⟨1, rfl, args⟩ = ⟨11, rfl, (extras16_10 V).append args⟩ := rfl

end
end AgaveLatticeHash.MLIR.BatchRoundBranches
