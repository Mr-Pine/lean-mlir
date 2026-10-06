/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_8
import SSA.Projects.Agave.LatticeHash.MLIR.agave_compress_pre_16
import SSA.Projects.Agave.LatticeHash.MLIR.PrefixTransport

/-! The four inlined BLAKE3 round bodies are the standalone compression round
under typed SSA substitutions. Each certificate compares all 179 lifted
instructions (178 result-producing operations and the no-alias marker).
Unused standalone ambient bindings may share a type-correct target binding;
the structural equality checks every operand that the body actually uses. -/

namespace AgaveLatticeHash.MLIR.BatchRounds
open LeanMLIR SLLVM
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private abbrev input {Γ Δ : Ctxt SLLVM.Ty} {rs ss} (_ : BlockCom Γ Δ rs ss) := Γ

structure Split (Γ Ω : Ctxt SLLVM.Ty) (rs : List SLLVM.Ty)
    (ss : List (List SLLVM.Ty)) where
  middle : Ctxt SLLVM.Ty
  pre : BlockPrefix Γ middle
  tail : BlockCom middle Ω rs ss

def split : (b : BlockCom Γ Ω rs ss) → Split Γ Ω rs ss
  | .var e b => let d := split b; ⟨d.middle, .var e d.pre, d.tail⟩
  | b => ⟨_, .nil, b⟩

theorem split_append (b : BlockCom Γ Ω rs ss) :
    (split b).pre.append (split b).tail = b := by
  match b with
  | .var e b => simp only [split, BlockPrefix.append]; rw [split_append b]
  | .term _ => rfl
  | .call _ _ _ _ _ => rfl

/-- Compose a structural prefix certificate with a relation on the actual tails. -/
theorem split_continue {Γ Ω Γ' Ω' : Ctxt SLLVM.Ty} {rs ss rs' ss'}
    (src : BlockCom Γ Ω rs ss) (dst : BlockCom Γ' Ω' rs' ss')
    (f : Γ.Hom Γ') (g : (split src).middle.Hom (split dst).middle)
    (h : BlockPrefix.Renamed f (split src).pre (split dst).pre g)
    {α : Type} (V : Γ'.Valuation)
    (k : (HVector TyDenote.toType rs' ⊕ SuccArgs ss') → EffectM α)
    (K : Γ'.Valuation → (HVector TyDenote.toType rs ⊕ SuccArgs ss) → EffectM α)
    (htail : ∀ W : (split dst).middle.Valuation,
      ((split dst).tail.denote W >>= fun r => k r.2) =
      ((split src).tail.denote (W.comap g) >>=
        fun r => K (W.comap (split dst).pre.contextHom) r.2)) :
    (dst.denote V >>= fun r => k r.2) =
      (src.denote (V.comap f) >>= fun r => K V r.2) := by
  conv_lhs => rw [← split_append dst, BlockPrefix.denote_append, bind_assoc]
  conv_rhs => rw [← split_append src, BlockPrefix.denote_append, bind_assoc]
  simp_rw [htail]
  exact h.denote_bind_with_context V (fun W U =>
    (split src).tail.denote W >>= fun r => K U r.2)

/-- Compose literal decompositions of the actual source and target blocks. -/
theorem parts_continue {Γ Ω Γ' Ω' : Ctxt SLLVM.Ty} {rs ss rs' ss'}
    (src : BlockCom Γ Ω rs ss) (dst : BlockCom Γ' Ω' rs' ss')
    (ps : Split Γ Ω rs ss) (qs : Split Γ' Ω' rs' ss')
    (hs : ps.pre.append ps.tail = src) (hq : qs.pre.append qs.tail = dst)
    (f : Γ.Hom Γ') (g : ps.middle.Hom qs.middle)
    (h : BlockPrefix.Renamed f ps.pre qs.pre g)
    {α : Type} (V : Γ'.Valuation)
    (k : (HVector TyDenote.toType rs' ⊕ SuccArgs ss') → EffectM α)
    (K : Γ'.Valuation → (HVector TyDenote.toType rs ⊕ SuccArgs ss) → EffectM α)
    (htail : ∀ W : qs.middle.Valuation,
      (qs.tail.denote W >>= fun r => k r.2) =
      (ps.tail.denote (W.comap g) >>=
        fun r => K (W.comap qs.pre.contextHom) r.2)) :
    (dst.denote V >>= fun r => k r.2) =
      (src.denote (V.comap f) >>= fun r => K V r.2) := by
  rw [← hq, ← hs, BlockPrefix.denote_append, BlockPrefix.denote_append]
  simp only [bind_assoc]
  simp_rw [htail]
  exact h.denote_bind_with_context V (fun W U => ps.tail.denote W >>= fun r => K U r.2)

open Lean Meta Elab Term in
/-- Read the constructor spine of an actual lifted block. The generated prefix
and terminal remain ordinary kernel-checked expressions. -/
elab "splitBlock% " b:term : term => do
  let actual ← elabTerm b none
  let rec peel (fuel : Nat) (b : Lean.Expr) : TermElabM (Lean.Expr × Lean.Expr) := do
    let fuel + 1 := fuel | throwError "block too long"
    let b ← whnf b
    let args := b.getAppArgs
    if b.isAppOf ``BlockCom.var then
      let (p, t) ← peel fuel args.back!
      let p ← mkAppM ``BlockPrefix.var #[args[args.size - 2]!, p]
      return (p, t)
    else if b.isAppOf ``BlockCom.term then
      let bt ← whnf (← inferType b)
      return (mkApp (Lean.mkConst ``BlockPrefix.nil) bt.getAppArgs[0]!, b)
    else
      throwError "splitBlock% requires a straight-line var/term block"
  let (p, t) ← peel 1000 actual
  let bt ← whnf (← inferType t)
  mkAppM ``Split.mk #[bt.getAppArgs[0]!, p, t]

open Lean Meta Elab Term in
elab "inputAt% " b:term " at " n:num : term => do
  let actual ← elabTerm b none
  let rec skip (n : Nat) (b : Lean.Expr) : TermElabM Lean.Expr := do
    match n with
    | 0 => return b
    | n+1 => skip n (← whnf b).getAppArgs.back!
  let rest ← skip n.getNat actual
  return (← whnf (← inferType rest)).getAppArgs[0]!

open Lean Meta Elab Term in
elab "appendMap% " b:term " into " target:term " using " f:term
    " skip " skipN:num " count " countN:num : term => do
  let actual ← elabTerm b none
  let target ← elabTerm target none
  let initial ← elabTerm f none
  let ty := Lean.mkConst ``SLLVMTy
  let rec skip (n : Nat) (b : Lean.Expr) : TermElabM Lean.Expr := do
    match n with
    | 0 => return b
    | n+1 => skip n (← whnf b).getAppArgs.back!
  let rec extend (fuel : Nat) (b target f : Lean.Expr) : TermElabM Lean.Expr := do
    match fuel with
    | 0 => return f
    | fuel+1 =>
      let b ← whnf b
      let target ← whnf target
      let args := b.getAppArgs
      let targetArgs := target.getAppArgs
      unless b.isAppOf ``BlockCom.var do throwError "not a variable instruction"
      let ζ := mkApp2 (Lean.mkConst ``Ctxt.ofList) ty args[1]!
      let f' := mkAppN (Lean.mkConst ``Ctxt.Hom.append) #[ty, args[0]!, targetArgs[0]!, ζ, f]
      extend fuel args.back! targetArgs.back! f'
  extend countN.getNat (← skip skipN.getNat actual) (← skip skipN.getNat target) initial

abbrev Source8 := input agave_compress_pre_8.cfgBlock_0
def sourceParts8 := splitBlock% agave_compress_pre_8.cfgBlock_0

abbrev Input8_20 := input agave_batch_8.cfgBlock_20
def parts8_20 := splitBlock% agave_batch_8.cfgBlock_20
def vars8_20 : HVector Input8_20.Var Source8.toList :=
  (⟨11, rfl⟩ ::ₕ
   ⟨12, rfl⟩ ::ₕ
   ⟨13, rfl⟩ ::ₕ
   ⟨14, rfl⟩ ::ₕ
   ⟨15, rfl⟩ ::ₕ
   ⟨16, rfl⟩ ::ₕ
   ⟨17, rfl⟩ ::ₕ
   ⟨18, rfl⟩ ::ₕ
   ⟨19, rfl⟩ ::ₕ
   ⟨20, rfl⟩ ::ₕ
   ⟨21, rfl⟩ ::ₕ
   ⟨22, rfl⟩ ::ₕ
   ⟨23, rfl⟩ ::ₕ
   ⟨24, rfl⟩ ::ₕ
   ⟨25, rfl⟩ ::ₕ
   ⟨26, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨81, rfl⟩ ::ₕ
   ⟨57, rfl⟩ ::ₕ
   ⟨58, rfl⟩ ::ₕ
   ⟨59, rfl⟩ ::ₕ
   ⟨60, rfl⟩ ::ₕ
   ⟨61, rfl⟩ ::ₕ
   ⟨62, rfl⟩ ::ₕ
   ⟨63, rfl⟩ ::ₕ
   ⟨64, rfl⟩ ::ₕ
   ⟨65, rfl⟩ ::ₕ
   ⟨66, rfl⟩ ::ₕ
   ⟨67, rfl⟩ ::ₕ
   ⟨68, rfl⟩ ::ₕ
   ⟨69, rfl⟩ ::ₕ
   ⟨70, rfl⟩ ::ₕ
   ⟨71, rfl⟩ ::ₕ
   ⟨79, rfl⟩ ::ₕ
   ⟨72, rfl⟩ ::ₕ
   ⟨86, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨114, rfl⟩ ::ₕ
   ⟨115, rfl⟩ ::ₕ
   ⟨116, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨52, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ .nil)
def rename8_20 : Source8.Hom Input8_20 := fun _ v => (vars8_20)[v]
abbrev prefix8_20 := parts8_20.pre

abbrev Input8_23 := input agave_batch_8.cfgBlock_23
def parts8_23 := splitBlock% agave_batch_8.cfgBlock_23
def vars8_23 : HVector Input8_23.Var Source8.toList :=
  (⟨20, rfl⟩ ::ₕ
   ⟨21, rfl⟩ ::ₕ
   ⟨22, rfl⟩ ::ₕ
   ⟨23, rfl⟩ ::ₕ
   ⟨24, rfl⟩ ::ₕ
   ⟨25, rfl⟩ ::ₕ
   ⟨26, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨30, rfl⟩ ::ₕ
   ⟨31, rfl⟩ ::ₕ
   ⟨32, rfl⟩ ::ₕ
   ⟨33, rfl⟩ ::ₕ
   ⟨34, rfl⟩ ::ₕ
   ⟨35, rfl⟩ ::ₕ
   ⟨36, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨90, rfl⟩ ::ₕ
   ⟨66, rfl⟩ ::ₕ
   ⟨67, rfl⟩ ::ₕ
   ⟨68, rfl⟩ ::ₕ
   ⟨69, rfl⟩ ::ₕ
   ⟨70, rfl⟩ ::ₕ
   ⟨71, rfl⟩ ::ₕ
   ⟨72, rfl⟩ ::ₕ
   ⟨73, rfl⟩ ::ₕ
   ⟨74, rfl⟩ ::ₕ
   ⟨75, rfl⟩ ::ₕ
   ⟨76, rfl⟩ ::ₕ
   ⟨77, rfl⟩ ::ₕ
   ⟨78, rfl⟩ ::ₕ
   ⟨79, rfl⟩ ::ₕ
   ⟨80, rfl⟩ ::ₕ
   ⟨88, rfl⟩ ::ₕ
   ⟨81, rfl⟩ ::ₕ
   ⟨95, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨123, rfl⟩ ::ₕ
   ⟨124, rfl⟩ ::ₕ
   ⟨125, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨60, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ .nil)
def rename8_23 : Source8.Hom Input8_23 := fun _ v => (vars8_23)[v]
abbrev prefix8_23 := parts8_23.pre

abbrev sourcePrefix8 := sourceParts8.pre
abbrev Source16 := input agave_compress_pre_16.cfgBlock_0
def sourceParts16 := splitBlock% agave_compress_pre_16.cfgBlock_0

abbrev Input16_7 := input agave_batch_16.cfgBlock_7
def parts16_7 := splitBlock% agave_batch_16.cfgBlock_7
def vars16_7 : HVector Input16_7.Var Source16.toList :=
  (⟨27, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨30, rfl⟩ ::ₕ
   ⟨31, rfl⟩ ::ₕ
   ⟨32, rfl⟩ ::ₕ
   ⟨33, rfl⟩ ::ₕ
   ⟨34, rfl⟩ ::ₕ
   ⟨35, rfl⟩ ::ₕ
   ⟨36, rfl⟩ ::ₕ
   ⟨37, rfl⟩ ::ₕ
   ⟨38, rfl⟩ ::ₕ
   ⟨39, rfl⟩ ::ₕ
   ⟨40, rfl⟩ ::ₕ
   ⟨41, rfl⟩ ::ₕ
   ⟨42, rfl⟩ ::ₕ
   ⟨43, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨107, rfl⟩ ::ₕ
   ⟨108, rfl⟩ ::ₕ
   ⟨109, rfl⟩ ::ₕ
   ⟨110, rfl⟩ ::ₕ
   ⟨111, rfl⟩ ::ₕ
   ⟨112, rfl⟩ ::ₕ
   ⟨113, rfl⟩ ::ₕ
   ⟨114, rfl⟩ ::ₕ
   ⟨115, rfl⟩ ::ₕ
   ⟨116, rfl⟩ ::ₕ
   ⟨117, rfl⟩ ::ₕ
   ⟨118, rfl⟩ ::ₕ
   ⟨119, rfl⟩ ::ₕ
   ⟨120, rfl⟩ ::ₕ
   ⟨121, rfl⟩ ::ₕ
   ⟨122, rfl⟩ ::ₕ
   ⟨123, rfl⟩ ::ₕ
   ⟨124, rfl⟩ ::ₕ
   ⟨125, rfl⟩ ::ₕ
   ⟨126, rfl⟩ ::ₕ
   ⟨127, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨162, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨78, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ .nil)
def rename16_7 : Source16.Hom Input16_7 := fun _ v => (vars16_7)[v]
abbrev prefix16_7 := parts16_7.pre

abbrev Input16_10 := input agave_batch_16.cfgBlock_10
def parts16_10 := splitBlock% agave_batch_16.cfgBlock_10
def vars16_10 : HVector Input16_10.Var Source16.toList :=
  (⟨11, rfl⟩ ::ₕ
   ⟨12, rfl⟩ ::ₕ
   ⟨13, rfl⟩ ::ₕ
   ⟨14, rfl⟩ ::ₕ
   ⟨15, rfl⟩ ::ₕ
   ⟨16, rfl⟩ ::ₕ
   ⟨17, rfl⟩ ::ₕ
   ⟨18, rfl⟩ ::ₕ
   ⟨19, rfl⟩ ::ₕ
   ⟨20, rfl⟩ ::ₕ
   ⟨21, rfl⟩ ::ₕ
   ⟨22, rfl⟩ ::ₕ
   ⟨23, rfl⟩ ::ₕ
   ⟨24, rfl⟩ ::ₕ
   ⟨25, rfl⟩ ::ₕ
   ⟨26, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨91, rfl⟩ ::ₕ
   ⟨92, rfl⟩ ::ₕ
   ⟨93, rfl⟩ ::ₕ
   ⟨94, rfl⟩ ::ₕ
   ⟨95, rfl⟩ ::ₕ
   ⟨96, rfl⟩ ::ₕ
   ⟨97, rfl⟩ ::ₕ
   ⟨98, rfl⟩ ::ₕ
   ⟨99, rfl⟩ ::ₕ
   ⟨100, rfl⟩ ::ₕ
   ⟨101, rfl⟩ ::ₕ
   ⟨102, rfl⟩ ::ₕ
   ⟨103, rfl⟩ ::ₕ
   ⟨104, rfl⟩ ::ₕ
   ⟨105, rfl⟩ ::ₕ
   ⟨106, rfl⟩ ::ₕ
   ⟨107, rfl⟩ ::ₕ
   ⟨108, rfl⟩ ::ₕ
   ⟨109, rfl⟩ ::ₕ
   ⟨110, rfl⟩ ::ₕ
   ⟨111, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨0, rfl⟩ ::ₕ
   ⟨146, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨61, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ .nil)
def rename16_10 : Source16.Hom Input16_10 := fun _ v => (vars16_10)[v]
abbrev prefix16_10 := parts16_10.pre

abbrev sourcePrefix16 := sourceParts16.pre



def map8_20_16 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 16).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 16) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using rename8_20 skip 0 count 16

def map8_20_32 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 32).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 32) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_16 skip 16 count 16

def map8_20_48 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 48).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 48) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_32 skip 32 count 16

def map8_20_64 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 64).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 64) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_48 skip 48 count 16

def map8_20_80 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 80).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 80) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_64 skip 64 count 16

def map8_20_96 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 96).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 96) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_80 skip 80 count 16

def map8_20_112 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 112).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 112) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_96 skip 96 count 16

def map8_20_128 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 128).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 128) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_112 skip 112 count 16

def map8_20_144 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 144).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 144) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_128 skip 128 count 16

def map8_20_160 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 160).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 160) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_144 skip 144 count 16

def map8_20_176 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 176).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 176) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_160 skip 160 count 16

def map8_20_179 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 179).Hom
    (inputAt% agave_batch_8.cfgBlock_20 at 179) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_20 using map8_20_176 skip 176 count 3

abbrev finalMap8_20 := map8_20_179

def map8_23_16 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 16).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 16) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using rename8_23 skip 0 count 16

def map8_23_32 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 32).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 32) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_16 skip 16 count 16

def map8_23_48 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 48).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 48) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_32 skip 32 count 16

def map8_23_64 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 64).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 64) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_48 skip 48 count 16

def map8_23_80 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 80).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 80) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_64 skip 64 count 16

def map8_23_96 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 96).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 96) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_80 skip 80 count 16

def map8_23_112 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 112).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 112) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_96 skip 96 count 16

def map8_23_128 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 128).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 128) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_112 skip 112 count 16

def map8_23_144 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 144).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 144) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_128 skip 128 count 16

def map8_23_160 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 160).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 160) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_144 skip 144 count 16

def map8_23_176 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 176).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 176) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_160 skip 160 count 16

def map8_23_179 : (inputAt% agave_compress_pre_8.cfgBlock_0 at 179).Hom
    (inputAt% agave_batch_8.cfgBlock_23 at 179) :=
  appendMap% agave_compress_pre_8.cfgBlock_0 into agave_batch_8.cfgBlock_23 using map8_23_176 skip 176 count 3

abbrev finalMap8_23 := map8_23_179

def map16_7_16 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 16).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 16) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using rename16_7 skip 0 count 16

def map16_7_32 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 32).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 32) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_16 skip 16 count 16

def map16_7_48 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 48).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 48) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_32 skip 32 count 16

def map16_7_64 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 64).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 64) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_48 skip 48 count 16

def map16_7_80 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 80).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 80) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_64 skip 64 count 16

def map16_7_96 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 96).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 96) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_80 skip 80 count 16

def map16_7_112 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 112).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 112) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_96 skip 96 count 16

def map16_7_128 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 128).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 128) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_112 skip 112 count 16

def map16_7_144 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 144).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 144) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_128 skip 128 count 16

def map16_7_160 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 160).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 160) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_144 skip 144 count 16

def map16_7_176 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 176).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 176) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_160 skip 160 count 16

def map16_7_179 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 179).Hom
    (inputAt% agave_batch_16.cfgBlock_7 at 179) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_7 using map16_7_176 skip 176 count 3

abbrev finalMap16_7 := map16_7_179

def map16_10_16 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 16).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 16) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using rename16_10 skip 0 count 16

def map16_10_32 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 32).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 32) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_16 skip 16 count 16

def map16_10_48 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 48).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 48) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_32 skip 32 count 16

def map16_10_64 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 64).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 64) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_48 skip 48 count 16

def map16_10_80 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 80).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 80) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_64 skip 64 count 16

def map16_10_96 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 96).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 96) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_80 skip 80 count 16

def map16_10_112 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 112).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 112) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_96 skip 96 count 16

def map16_10_128 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 128).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 128) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_112 skip 112 count 16

def map16_10_144 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 144).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 144) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_128 skip 128 count 16

def map16_10_160 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 160).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 160) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_144 skip 144 count 16

def map16_10_176 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 176).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 176) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_160 skip 160 count 16

def map16_10_179 : (inputAt% agave_compress_pre_16.cfgBlock_0 at 179).Hom
    (inputAt% agave_batch_16.cfgBlock_10 at 179) :=
  appendMap% agave_compress_pre_16.cfgBlock_0 into agave_batch_16.cfgBlock_10 using map16_10_176 skip 176 count 3

abbrev finalMap16_10 := map16_10_179

theorem sourceParts8_append : sourceParts8.pre.append sourceParts8.tail =
    agave_compress_pre_8.cfgBlock_0 := by rfl

theorem sourceParts16_append : sourceParts16.pre.append sourceParts16.tail =
    agave_compress_pre_16.cfgBlock_0 := by rfl

theorem parts8_20_append : parts8_20.pre.append parts8_20.tail =
    agave_batch_8.cfgBlock_20 := by rfl

theorem parts8_23_append : parts8_23.pre.append parts8_23.tail =
    agave_batch_8.cfgBlock_23 := by rfl

theorem parts16_7_append : parts16_7.pre.append parts16_7.tail =
    agave_batch_16.cfgBlock_7 := by rfl

theorem parts16_10_append : parts16_10.pre.append parts16_10.tail =
    agave_batch_16.cfgBlock_10 := by rfl

end
end AgaveLatticeHash.MLIR.BatchRounds
