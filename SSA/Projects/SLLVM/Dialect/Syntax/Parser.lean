/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Qq

import LeanMLIR.MLIRSyntax
import SSA.Projects.SLLVM.Dialect.Basic

namespace LeanMLIR.SLLVM

-- open Qq Lean Meta Elab.Term Elab Command
open InstCombine (LLVM)
open MLIR
open MLIR.AST

private abbrev ReaderM := MLIR.AST.ReaderM SLLVM

/-- The `LLVM.Ty` (i.e. `SLLVM.Ty.arith`) counterpart of an MLIR type. Split
out of `mkTy` because vectors recurse through their element type, which is again
an arithmetic type, never `!ptr`. -/
def mkArithTy : MLIRType 0 → ExceptM SLLVM LLVM.Ty
  | .int .Signless w => return .bitvec w.toConcrete
  -- A fixed-length 1-D vector, as in the LLVM dialect: scalable or
  -- multi-dimensional vectors have no counterpart in `LLVM.Ty`.
  | .vector [length] [] elemTy => return .vector length (← mkArithTy elemTy)
  | t => throw <| .unsupportedType (some t)

/-- `!ptr` is SLLVM's own spelling; `!llvm.ptr` is what `mlir-translate
--import-llvm` emits, and is the only one that appears in lifted code. -/
def mkTy : MLIRType 0 → ExceptM SLLVM SLLVM.Ty
  | .undefined "ptr" | .undefined "llvm.ptr" => return Ty.ptr
  | t => Ty.arith <$> mkArithTy t

instance : TransformTy SLLVM 0 where
  mkTy := mkTy


def getOutputWidth (opStx : MLIR.AST.Op 0) :
    Except TransformError Nat := do
  match opStx.res with
  | res::[] =>
    match res.2 with
    | .int _ (.concrete w) => pure w
    | _ => throw <| .generic s!"The operation {opStx.name} must output an integer type"
  | _ => throw <| .generic s!"The operation {opStx.name} must have a single output"

/-- The declared result type of a single-result operation, as an arithmetic
(`LLVM.Ty`) type. Unlike `getOutputWidth` this keeps the whole type, which
poison needs since it exists at vector types too. -/
def getOutputArithTy (opStx : MLIR.AST.Op 0) :
    ExceptM SLLVM LLVM.Ty := do
  match opStx.res with
  | res::[] => mkArithTy res.2
  | _ => throw <| .generic s!"The operation {opStx.name} must have a single output"

/-- The declared result type of a single-result operation, as a full
`SLLVM.Ty`. `getOutputArithTy` gives only the arithmetic half, which a call's
result type need not be. -/
def getOutputTy (opStx : MLIR.AST.Op 0) : ExceptM SLLVM SLLVM.Ty := do
  match opStx.res with
  | res::[] => mkTy res.2
  | _ => throw <| .generic s!"The operation {opStx.name} must have a single output"

/-- The declared type of the `i`-th operand of an operation. -/
def getArgArithTy (opStx : MLIR.AST.Op 0) (i : Nat) :
    ExceptM SLLVM LLVM.Ty := do
  match opStx.args[i]? with
  | some (_, t) => mkArithTy t
  | none => throw <| .generic s!"{opStx.name}: expected at least {i + 1} operand(s)"

/-- The arithmetic type of an already-parsed operand. Unlike `getArgArithTy`
this reads the type off the context variable rather than off the syntax, which
is what `llvm.store` needs: its stored value may be of any arithmetic type. -/
def argArithTy {Γ : Ctxt SLLVM.Ty} (opName : String) : (Σ t, Γ.Var t) → ReaderM LLVM.Ty
  | ⟨Ty.arith t, _⟩ => return t
  | ⟨t, _⟩ => throw <| .generic s!"{opName}: expected an arithmetic operand, but found: {t}"

/-- `llvm.load`/`llvm.store` carry an `ordering` attribute; `0` is
`not_atomic`, and atomics are not modelled. `alignment`, `tbaa` and
`nontemporal` are accepted and ignored -- this memory model has no alignment
constraints and no alias-metadata semantics. -/
def checkNotAtomic (opStx : MLIR.AST.Op 0) : ReaderM Unit :=
  match opStx.getAttr? "ordering" with
  | none => return ()
  | some (.int 0 _) => return ()
  | some _ => throw <| .generic s!"{opStx.name}: atomic accesses are not modelled \
      (expected `ordering = 0`, i.e. non-atomic)"

/-- The integers inside a `dense<…>` attribute: either a single value (the
splat form) or one per lane. -/
def denseInts : MLIR.AST.AttrValue 0 → ExceptM SLLVM (List Int)
  | .int v _ => return [v]
  | .list xs => xs.mapM fun
      | .int v _ => pure v
      | _ => throw <| .generic "llvm.mlir.constant: dense elements must be integers"
  | _ => throw <| .generic
      "llvm.mlir.constant: expected an integer or a list of integers inside `dense<…>`"

/-- The integers of an `array<…>` attribute, as `llvm.shufflevector` writes its
mask. -/
def arrayInts (opStx : MLIR.AST.Op 0) (attr : String) :
    ExceptM SLLVM (List Int) := do
  let some (.array _ els) := opStx.getAttr? attr
    | throw <| .generic s!"{opStx.name}: expected an `array<…>` attribute `{attr}`"
  els.mapM fun
    | .int v _ => pure v
    | _ => throw <| .generic s!"{opStx.name}: `{attr}` must hold integers"

/-- The lane count of a `vector<n x i64>` result, which is the shape the AVX-512
IFMA intrinsics have. -/
def getVectorLaneCount (opStx : MLIR.AST.Op 0) (op : String) :
    ExceptM SLLVM Nat := do
  let .vector l (.bitvec 64) ← getOutputArithTy opStx
    | throw <| .generic s!"{op}: expected a `vector<n x i64>` result"
  return l

/-- Given a variable of arbitrary type, return its width.

This relies on the fact that `bitvec _` is the only type currently modelled.
In future, this might start throwing errors, if the type is not a bitvec.
-/
def getIntWidth {Γ : Ctxt SLLVM.Ty} : (Σ t, Γ.Var t) → ReaderM Nat
  | ⟨Ty.bitvec w, _⟩ => return w
  | ⟨t, _⟩ => throw <| .generic s!"Expected type `bitvec _`, but found: {t}"

def parseOverflowFlags (op : AST.Op 0) : ReaderM LLVM.NoWrapFlags :=
  match op.getAttr? "overflowFlags" with
  | .none => return {}
  | .some y => match y with
    | .opaque_ "llvm.overflow" "nsw" => return ⟨true, false⟩
    | .opaque_ "llvm.overflow" "nuw" => return ⟨false, true⟩
    | .opaque_ "llvm.overflow" "none" => return ⟨false, false⟩
    | .list [.opaque_ "llvm.overflow" "nuw", .opaque_ "llvm.overflow" "nsw"]
    | .list [.opaque_ "llvm.overflow" "nsw", .opaque_ "llvm.overflow" "nuw"] =>
        return ⟨true, true⟩
    | .opaque_ "llvm.overflow" s => throw <| .generic s!"The overflow flag {s} not allowed. \
        We currently support nsw (no signed wrap) and nuw (no unsigned wrap)"
    | _ => throw <| .generic s!"Unrecognised overflow flag found: {MLIR.AST.docAttrVal y}. \
        We currently support nsw (no signed wrap) and nuw (no unsigned wrap)"

instance : DialectParse SLLVM 0 where
  isValidReturn Γ opStx := return opStx.name == "llvm.return"

  mkExpr (Γ : Ctxt SLLVM.Ty) (opStx : MLIR.AST.Op 0)
      (regions : List (MLIR.AST.ParsedRegion SLLVM)) := do
  let args ← opStx.parseArgs Γ

  /- `binW` is the (lazily computed) width, assuming a binary operation -/
  let binW := do
  -- ^^ NOTE: `binW` is bound with := rather than ← on purpose, to ensure laziness
    let args ← args.assumeArity 2
    getIntWidth args[0]

  /- `unW` is the (lazily computed) width, assuming an unary operation -/
  let unW := do
    let args ← args.assumeArity 1
    getIntWidth args[0]

  let getOutputWidth := getOutputWidth opStx

  let mkExprOf := opStx.mkExprOf (args? := args) Γ

  /- LLVM's binary arithmetic is elementwise on vectors, so the same op name
     builds either the scalar or the lane-wise operation depending on what its
     operands are. Note that this is only used for the *pure* binary operations;
     divisions and remainders keep their scalar, impure SLLVM treatment. -/
  let mkBinary (bop : InstCombine.MOp.BinaryOp) :
      ReaderM (Σ eff returnTy, Expr SLLVM Γ eff returnTy) := do
    let args ← args.assumeArity 2
    match args[0].1 with
    | Ty.bitvec w => mkExprOf <| Op.arith (.binary w bop)
    | Ty.arith (.vector l (.bitvec (.concrete w))) => mkExprOf <| Op.vectorBinary l w bop
    | t => throw <| .generic s!"llvm.{bop}: expected bitvector or vector operands, found {t}"

  match opStx.name with
    -- new SLLVM operations
    | "ptr.add" => mkExprOf <| .ptradd
    | "ptr.load" => mkExprOf <| .load (← getOutputArithTy opStx)
    | "ptr.store" => do
        let args ← args.assumeArity 2
        mkExprOf <| .store (← argArithTy opStx.name args[1])
    -- The same two operations under the names MLIR actually emits. Note the
    -- operand order: MLIR writes `llvm.store (value, ptr)` where SLLVM's
    -- signature is `(ptr, value)`, so the operands are swapped back here.
    | "llvm.load" => do
        checkNotAtomic opStx
        mkExprOf <| .load (← getOutputArithTy opStx)
    | "llvm.store" => do
        checkNotAtomic opStx
        let args ← args.assumeArity 2
        let t ← argArithTy opStx.name args[0]
        opStx.mkExprOf (args? := some (Op.ParsedArgs.ofList [args[1], args[0]])) Γ <| .store t
    | "ptr.alloca" =>
        let t ← opStx.getTypeAttr "elem_type"
        let .int _ w := t
          | throw <| .generic s!"Expected value of attribute `elem_type` to be an integer type"
        mkExprOf <| .alloca w.toConcrete
    -- The same operation as MLIR emits it: `llvm.alloca %count x T`, with any
    -- arithmetic element type. `Op.alloca` allocates a *single* element, so
    -- the count operand is dropped -- for the scalar locals the compiler
    -- emits it is always the constant 1, and nothing else is expressible.
    | "llvm.alloca" =>
        let t ← mkArithTy (← opStx.getTypeAttr "elem_type")
        opStx.mkExprOf (args? := some (Op.ParsedArgs.ofList [])) Γ
          <| .alloca (LLVM.Ty.width t)
    -- Stack-coloring metadata: no semantics here, but part of the artifact, so
    -- they parse (and denote to nothing) rather than having to be stripped.
    | "llvm.intr.lifetime.start" => mkExprOf <| SLLVMOp.lifetime true
    | "llvm.intr.lifetime.end"   => mkExprOf <| SLLVMOp.lifetime false
    -- Ternary Operations
    | "llvm.select" =>
        let args ← args.assumeArity 3
        let w ← getIntWidth args[1]
        mkExprOf <| Op.select w
    -- Binary Operations
    | "llvm.and"      => mkBinary .and
    | "llvm.or"       => mkBinary (.or ⟨opStx.hasAttr "isDisjoint"⟩)
    | "llvm.xor"      => mkBinary .xor
    | "llvm.urem"     => mkExprOf <| Op.urem (← binW)
    | "llvm.srem"     => mkExprOf <| Op.srem (← binW)
    | "llvm.lshr"     => mkBinary (.lshr ⟨opStx.hasAttr "isExact"⟩)
    | "llvm.ashr"     => mkBinary (.ashr ⟨opStx.hasAttr "isExact"⟩)
    | "llvm.sdiv"     => mkExprOf <| Op.sdiv (← binW) ⟨opStx.hasAttr "isExact"⟩
    | "llvm.udiv"     => mkExprOf <| Op.udiv (← binW) ⟨opStx.hasAttr "isExact"⟩
    | "llvm.shl"      => mkBinary (.shl (← parseOverflowFlags opStx))
    | "llvm.add"      => mkBinary (.add (← parseOverflowFlags opStx))
    | "llvm.mul"      => mkBinary (.mul (← parseOverflowFlags opStx))
    | "llvm.sub"      => mkBinary (.sub (← parseOverflowFlags opStx))
    | "llvm.icmp.eq"  => mkExprOf <| Op.icmp .eq (← binW)
    | "llvm.icmp.ne"  => mkExprOf <| Op.icmp .ne (← binW)
    | "llvm.icmp.ugt" => mkExprOf <| Op.icmp .ugt (← binW)
    | "llvm.icmp.uge" => mkExprOf <| Op.icmp .uge (← binW)
    | "llvm.icmp.ult" => mkExprOf <| Op.icmp .ult (← binW)
    | "llvm.icmp.ule" => mkExprOf <| Op.icmp .ule (← binW)
    | "llvm.icmp.sgt" => mkExprOf <| Op.icmp .sgt (← binW)
    | "llvm.icmp.sge" => mkExprOf <| Op.icmp .sge (← binW)
    | "llvm.icmp.slt" => mkExprOf <| Op.icmp .slt (← binW)
    | "llvm.icmp.sle" => mkExprOf <| Op.icmp .sle (← binW)
    -- ... and the generic form, which is the only one MLIR itself emits: the
    -- op is always named `llvm.icmp` and the condition code rides in an
    -- attribute.  `ofMLIRPredicate?` is where the numbering is documented.
    | "llvm.icmp" =>
      let ⟨n, _⟩ ← opStx.getIntAttr "predicate"
      let some c := LLVM.IntPred.ofMLIRPredicate? n
        | throw <| .generic s!"llvm.icmp: unsupported predicate {n}"
      mkExprOf <| Op.icmp c (← binW)
    -- Unary Operations
    | "llvm.not"    => mkExprOf <| Op.not (← unW)
    | "llvm.neg"    => mkExprOf <| Op.neg (← unW)
    | "llvm.copy"   => mkExprOf <| Op.copy (← unW)
    | "llvm.freeze" => mkExprOf <| Op.freeze (← unW)
    | "llvm.zext"   => mkExprOf <| Op.zext (← unW) (← getOutputWidth) ⟨ opStx.hasAttr "nonNeg" ⟩
    | "llvm.sext"   => mkExprOf <| Op.sext (← unW) (← getOutputWidth)
    | "llvm.trunc"  => mkExprOf <| Op.trunc (← unW) (← getOutputWidth) (← parseOverflowFlags opStx)
    -- Poison
    | "llvm.mlir.poison" =>
      mkExprOf <| Op.poison (← getOutputArithTy opStx)
    -- NOTE: LLVM's `undef` is weaker than `poison` (it may take a different
    -- value at each use); modelling it as poison is the usual simplification.
    | "llvm.mlir.undef" =>
      mkExprOf <| Op.poison (← getOutputArithTy opStx)
    -- Constant
    -- NOTE: dispatch on the *result* type rather than the attribute's type: the
    -- two must agree in MLIR, but only the former is what `mkExprOf` will use.
    | "llvm.mlir.constant" => do
      match ← getOutputArithTy opStx with
      | LLVM.Ty.bitvec w =>
        let ⟨val, _⟩ ← opStx.getIntAttr "value"
        mkExprOf <| Op.const w val
      | t =>
        let some (.dense v _) := opStx.getAttr? "value"
          | throw <| .generic
              "llvm.mlir.constant: a non-scalar constant needs a `dense<…>` value"
        mkExprOf <| Op.constDense t (← denseInts v)
    -- Vector operations
    | "llvm.insertelement" =>
      let .vector l elem ← getOutputArithTy opStx
        | throw <| .generic "llvm.insertelement: result must be a vector"
      let .bitvec (.concrete idxW) ← getArgArithTy opStx 2
        | throw <| .generic "llvm.insertelement: index must be an integer"
      mkExprOf <| Op.insertelement elem l idxW
    | "llvm.extractelement" =>
      let .vector l elem ← getArgArithTy opStx 0
        | throw <| .generic "llvm.extractelement: operand must be a vector"
      let .bitvec (.concrete idxW) ← getArgArithTy opStx 1
        | throw <| .generic "llvm.extractelement: index must be an integer"
      mkExprOf <| Op.extractelement elem l idxW
    | "llvm.shufflevector" =>
      let .vector l elem ← getArgArithTy opStx 0
        | throw <| .generic "llvm.shufflevector: operands must be vectors"
      mkExprOf <| Op.shufflevector elem l (← arrayInts opStx "mask")
    -- AVX-512 IFMA, as the x86vector dialect spells it
    | "x86vector.avx512.intr.vpmadd52l.uq.512" =>
      mkExprOf <| Op.vpmadd52 false (← getVectorLaneCount opStx opStx.name)
    | "x86vector.avx512.intr.vpmadd52h.uq.512" =>
      mkExprOf <| Op.vpmadd52 true (← getVectorLaneCount opStx opStx.name)
    | "x86vector.avx512.intr.vpermi2var.q.512" =>
      mkExprOf <| Op.vpermi2var (← getVectorLaneCount opStx opStx.name)
    -- ... and as a direct call to the LLVM intrinsic, which is how the same
    -- source lowers when the x86vector dialect is not used.
    | "llvm.call" =>
      let some (.symbol callee) := opStx.getAttr? "callee"
        | throw <| .generic "llvm.call: expected a `callee` symbol attribute"
      match callee with
      | "x86_avx512_vpmadd52l_uq_512" =>
        mkExprOf <| Op.vpmadd52 false (← getVectorLaneCount opStx callee)
      | "x86_avx512_vpmadd52h_uq_512" =>
        mkExprOf <| Op.vpmadd52 true (← getVectorLaneCount opStx callee)
      | "x86_avx512_vpermi2var_q_512" =>
        mkExprOf <| Op.vpermi2var (← getVectorLaneCount opStx callee)
      | _ =>
        -- Any other callee is an ordinary call: its body is the region, which
        -- the elaborator bound to the symbol before the transform ran.
        let some region := regions[0]?
          | throw <| .unsupportedOp s!"llvm.call to {callee}: the callee's body \
              is not bound. Supply it with `with @{callee} := …`."
        let ⟨Γr, effR, tyR, com⟩ := region
        -- The result list, not a single result: a void call (`-> ()`) has
        -- none, which is the shape of a callee returning through pointer
        -- out-parameters.
        let retTys ← opStx.res.mapM (fun r => mkTy r.2)
        let argTys := args.types
        -- Reversed: block arguments enter a `Ctxt` in reverse declaration
        -- order, so a callee declared `^bb0(%a, %b)` has context `[b, a]`.
        if hΓ : Γr = Ctxt.ofList argTys.reverse then
          if hty : tyR = retTys then
            let com : Com SLLVM (Ctxt.ofList argTys.reverse) effR retTys :=
              hty ▸ hΓ ▸ com
            return ⟨effR, retTys, Expr.mk
              (op := SLLVMOp.call callee argTys retTys effR)
              (ty_eq := rfl)
              (eff_le := EffectKind.le_refl _)
              (args := args.toHVector)
              (regArgs := Regions.cons com Regions.nil)⟩
          else
            throw <| .generic s!"llvm.call to {callee}: the callee returns \
              {repr tyR}, but the call site expects {repr retTys}"
        else
          throw <| .generic s!"llvm.call to {callee}: the callee takes \
              {repr Γr}, but the call site passes {repr argTys}"
    -- Fallback
    | opName => throw <| .unsupportedOp opName

/-! ## Binding a call's callee

MLIR's `llvm.call` names a symbol and carries no inline region, so the callee's
body has to be attached to the operation before the (pure) transform runs. That
happens here, on the evaluated AST: region antiquotations do not elaborate, so
this cannot be done at the syntax level. -/

open MLIR.AST in
/-- Attach each bound region to the `llvm.call`s that name it.

Only calls that do not already carry a region are rewritten, so an inline
region always wins over a binding. Recurses into nested regions, so a call
inside a callee can be bound too. -/
private partial def bindCallees (table : List (String × Region 0)) (reg : Region 0) :
    Region 0 :=
  { reg with ops := reg.ops.map goOp }
where
  goOp (op : Op 0) : Op 0 :=
    let op := { op with regions := op.regions.map (bindCallees table) }
    if op.name != "llvm.call" || !op.regions.isEmpty then op
    else match op.getAttr? "callee" with
      | some (.symbol callee) =>
          match table.lookup callee with
          | some r => { op with regions := [r] }
          | none   => op
      | _ => op

open MLIR.AST in
/-- The one semantic assumption the `llvm.alloca` parse arm makes, checked:
`Op.alloca` allocates a single element, so every `llvm.alloca`'s count operand
must be visibly the constant 1. Checked on the region AST because the count is
an SSA operand -- `mkExpr` sees one operation at a time and cannot follow it
to its defining constant. Each region is its own scope: a bound callee's `%0`
is not its caller's. -/
private partial def allocaCountsAreOne (reg : Region 0) : Except String Unit := do
  let _ ← reg.ops.foldlM (init := ([] : List SSAVal)) fun ones op => do
    op.regions.forM allocaCountsAreOne
    if op.name == "llvm.mlir.constant" then
      match op.getAttr? "value", op.res with
      | some (.int 1 _), [(name, _)] => return name :: ones
      | _, _ => return ones
    else if op.name == "llvm.alloca" then
      match op.args with
      | (count, _) :: _ =>
          if ones.contains count then return ones
          else throw s!"llvm.alloca: the count operand %{SSAValToString count} is \
              not the constant 1, which is the only count Op.alloca can represent"
      | [] => return ones
    else
      return ones

/-- A `with` binding: `@name := ‹term : MLIR.AST.Region 0›`. -/
syntax sllvmCallee := "@" ident " := " term

open Lean Elab Term Qq in
/-- Evaluate a bound term to the AST region it denotes. -/
private def elabRegionTerm (t : Term) : TermElabM (MLIR.AST.Region 0) := do
  let e ← elabTermEnsuringTypeQ t q(MLIR.AST.Region 0)
  synthesizeSyntheticMVarsNoPostponing
  SSA.evalExprOfTypeRegion 0 (← instantiateMVars e)

open Lean Elab Term in
private def elabCalleeTable (bs : Array (TSyntax ``sllvmCallee)) :
    TermElabM (List (String × MLIR.AST.Region 0)) :=
  bs.toList.mapM fun b => do
    match b with
    | `(sllvmCallee| @$name:ident := $t) =>
        return (name.getId.toString, ← elabRegionTerm t)
    | _ => throwUnsupportedSyntax

elab "[sllvm| " reg:mlir_region "]" : term =>
  SSA.elabIntoCom' reg SLLVM (check := allocaCountsAreOne)

/-- `[sllvm| ‹region› with @f := fRegion]` binds the bodies of the symbols the
region's `llvm.call`s name, where `fRegion : MLIR.AST.Region 0` -- as
`[mlir_region| … ]` produces. MLIR's `llvm.call` carries no inline region, so
this is how a lifted call site gets its callee. -/
elab "[sllvm| " reg:mlir_region " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCalleeTable bs.getElems
  SSA.elabIntoCom' reg SLLVM (pre := bindCallees table) (check := allocaCountsAreOne)

/-- `[sllvm| … ]` from an already-built `MLIR.AST.Region 0`, so a region can be
written once and used both as a `Com` and as a callee binding. -/
elab "[sllvm_of| " t:term "]" : term => do
  SSA.elabIntoCom'OfRegion (← elabRegionTerm t) SLLVM (check := allocaCountsAreOne)

/-- `[sllvm_of| r with @f := fRegion]`: `[sllvm_of| r]` with callee bindings,
for a lifted region that both *is* a callee and *has* callees of its own. -/
elab "[sllvm_of| " t:term " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCalleeTable bs.getElems
  SSA.elabIntoCom'OfRegion (bindCallees table (← elabRegionTerm t)) SLLVM
    (check := allocaCountsAreOne)
