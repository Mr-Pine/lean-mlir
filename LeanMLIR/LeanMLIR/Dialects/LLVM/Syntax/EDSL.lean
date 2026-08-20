/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.MLIRSyntax
import LeanMLIR.Dialects.LLVM.Basic

import Qq

open Qq Lean Meta Elab.Term Elab Command
open InstCombine (LLVM MetaLLVM MOp Width)

open MLIR

namespace InstcombineTransformDialect
open AST (Op TransformError)
private abbrev ReaderM (φ) := AST.ReaderM (MetaLLVM φ)

def mkTy : MLIR.AST.MLIRType φ → MLIR.AST.ExceptM (MetaLLVM φ) ((MetaLLVM φ).Ty)
  | MLIR.AST.MLIRType.int MLIR.AST.Signedness.Signless w => return .bitvec w
  -- A fixed-length 1-D vector. Scalable dimensions have no counterpart in `MTy`
  -- (there is no `vscale`), and multi-dimensional vectors would have to nest,
  -- so both fall through to `unsupportedType` below.
  | MLIR.AST.MLIRType.vector [length] [] elemTy => do
      return .vector length (← mkTy elemTy)
  | t => throw <| .unsupportedType (some t)

instance instTransformTy : AST.TransformTy (MetaLLVM φ) φ := { mkTy }
instance : AST.TransformTy (LLVM) 0 := { mkTy }

def getOutputWidth (opStx : MLIR.AST.Op φ) (op : String) :
    Except TransformError (Width φ) := do
  match opStx.res with
  | res::[] =>
    match res.2 with
    | .int _ w => pure w
    | _ => throw <| .generic s!"The operation {op} must output an integer type"
  | _ => throw <| .generic s!"The operation {op} must have a single output"

/-- The declared result type of a single-result operation. Unlike
`getOutputWidth` this keeps the whole type, which poison needs since it exists
at vector types too. -/
def getOutputTy (opStx : MLIR.AST.Op φ) (op : String) :
    MLIR.AST.ExceptM (MetaLLVM φ) ((MetaLLVM φ).Ty) := do
  match opStx.res with
  | res::[] => mkTy res.2
  | _ => throw <| .generic s!"The operation {op} must have a single output"

/-- The integers inside a `dense<…>` attribute: either a single value (the
splat form) or one per lane. -/
def denseInts : MLIR.AST.AttrValue φ → MLIR.AST.ExceptM (MetaLLVM φ) (List Int)
  | .int v _ => return [v]
  | .list xs => xs.mapM fun
      | .int v _ => pure v
      | _ => throw <| .generic "llvm.mlir.constant: dense elements must be integers"
  | _ => throw <| .generic
      "llvm.mlir.constant: expected an integer or a list of integers inside `dense<…>`"

/-- The declared type of the `i`-th operand of an operation. -/
def getArgTy (opStx : MLIR.AST.Op φ) (op : String) (i : Nat) :
    MLIR.AST.ExceptM (MetaLLVM φ) ((MetaLLVM φ).Ty) := do
  match opStx.args[i]? with
  | some (_, t) => mkTy t
  | none => throw <| .generic s!"{op}: expected at least {i + 1} operand(s)"

/-- The integers of an `array<…>` attribute, as `llvm.shufflevector` writes its
mask. -/
def arrayInts (opStx : MLIR.AST.Op φ) (op attr : String) :
    MLIR.AST.ExceptM (MetaLLVM φ) (List Int) := do
  let some (.array _ els) := opStx.getAttr? attr
    | throw <| .generic s!"{op}: expected an `array<…>` attribute `{attr}`"
  els.mapM fun
    | .int v _ => pure v
    | _ => throw <| .generic s!"{op}: `{attr}` must hold integers"

/-- The lane count of a `vector<n x i64>` result, which is the shape the AVX-512
IFMA intrinsics have. -/
def getVectorLaneCount (opStx : MLIR.AST.Op φ) (op : String) :
    MLIR.AST.ExceptM (MetaLLVM φ) Nat := do
  let .vector l (.bitvec (.concrete 64)) ← getOutputTy opStx op
    | throw <| .generic s!"{op}: expected a `vector<n x i64>` result"
  return l

/-- Given a variable of arbitrary type, return its width.

Now that `vector` is also modelled, this throws for any non-bitvec type.
-/
def getVarWidth {Γ : Ctxt (MetaLLVM φ).Ty} : (Σ t, Γ.Var t) → ReaderM φ (Width φ)
  | ⟨.bitvec w, _⟩ => return w
  | ⟨_, _⟩ => throw <| .generic "expected an operand of bitvector type"

def parseOverflowFlags (op : AST.Op φ) : ReaderM φ LLVM.NoWrapFlags := do
  match op.getAttr? "overflowFlags" with
  | .none => return {}
  | .some y => match y with
    | .opaque_ "llvm.overflow" "nsw" => return ⟨true, false⟩
    | .opaque_ "llvm.overflow" "nuw" => return ⟨false, true⟩
    | .opaque_ "llvm.overflow" "none" => return ⟨false, false⟩
    | .list [.opaque_ "llvm.overflow" "nuw", .opaque_ "llvm.overflow" "nsw"]
    | .list [.opaque_ "llvm.overflow" "nsw", .opaque_ "llvm.overflow" "nuw"] =>
        return ⟨true, true⟩
    | _ =>
      -- Parse oveflowFlags passed as integer attribute
          let ⟨n, _ ⟩ ← op.getIntAttr "overflowFlags"
          match n with
          | 0 => return { nsw := false, nuw := false}
          | 1 => return { nsw := true, nuw := false}
          | 2 => return { nsw := false, nuw := true}
          | 3 => return { nsw := true, nuw := true}
          | s => throw <| .generic s!"The overflow flag with predicate {s} is not allowed. \
            We currently support nsw (no signed wrap) and nuw (no unsigned wrap)"
/-- The `predicate` attribute of a generic-form `llvm.icmp`. The mapping itself
is `LLVM.IntPred.ofMLIRPredicate?`, which documents why MLIR's numbering is not
this inductive's. -/
def parseIcmpPredicate (n : Int) : AST.ReaderM (MetaLLVM φ) (LLVM.IntPred) := do
  match LLVM.IntPred.ofMLIRPredicate? n with
  | some c => return c
  | none => throw <| .generic s!"The icmp predicate {n} is not supported"

open InstCombine.MOp in
def mkExpr (Γ : Ctxt (MetaLLVM φ).Ty) (opStx : MLIR.AST.Op φ) :
    AST.ReaderM (MetaLLVM φ) (Σ eff ty, Expr (MetaLLVM φ) Γ eff ty) := do
  let args ← opStx.parseArgs Γ

  /- `binW` is the (lazily computed) width, assuming a binary operation -/
  let binW : AST.ReaderM (MetaLLVM φ) (Width φ) := do
  -- ^^ NOTE: `binW` is bound with := rather than ← on purpose, to ensure laziness
    let args ← args.assumeArity 2
    getVarWidth args[0]

  /- `unW` is the (lazily computed) width, assuming an unary operation -/
  let unW := do
    let args ← args.assumeArity 1
    getVarWidth args[0]

  let mkExprOf := opStx.mkExprOf (args? := args) Γ

  /- LLVM's binary arithmetic is elementwise on vectors, so the same op name
     builds either the scalar or the lane-wise operation depending on what its
     operands are. -/
  let mkBinary (bop : InstCombine.MOp.BinaryOp) := do
    let args ← args.assumeArity 2
    match args[0].1 with
    | .bitvec w => mkExprOf <| MOp.binary w bop
    | .vector l (.bitvec w) => mkExprOf <| MOp.vectorBinary l w bop
    | _ =>
      throw <| .generic s!"llvm.{bop}: expected bitvector or vector operands"

  match opStx.name with
    -- Ternary Operations
    | "llvm.select" =>
        let args ← args.assumeArity 3
        let w ← getVarWidth args[1]
        mkExprOf <| select w
    -- Binary Operations
    | "llvm.and"      => mkBinary .and
    | "llvm.or"       => mkBinary (.or ⟨opStx.hasAttr "isDisjoint"⟩)
    | "llvm.xor"      => mkBinary .xor
    | "llvm.urem"     => mkBinary .urem
    | "llvm.srem"     => mkBinary .srem
    | "llvm.lshr"     => mkBinary (.lshr ⟨opStx.hasAttr "isExact"⟩)
    | "llvm.ashr"     => mkBinary (.ashr ⟨opStx.hasAttr "isExact"⟩)
    | "llvm.sdiv"     => mkBinary (.sdiv ⟨opStx.hasAttr "isExact"⟩)
    | "llvm.udiv"     => mkBinary (.udiv ⟨opStx.hasAttr "isExact"⟩)
    | "llvm.shl"      => mkBinary (.shl (← parseOverflowFlags opStx))
    | "llvm.add"      => mkBinary (.add (← parseOverflowFlags opStx))
    | "llvm.mul"      => mkBinary (.mul (← parseOverflowFlags opStx))
    | "llvm.sub"      => mkBinary (.sub (← parseOverflowFlags opStx))
    | "llvm.icmp.eq"  => mkExprOf <| icmp .eq (← binW)
    | "llvm.icmp.ne"  => mkExprOf <| icmp .ne (← binW)
    | "llvm.icmp.ugt" => mkExprOf <| icmp .ugt (← binW)
    | "llvm.icmp.uge" => mkExprOf <| icmp .uge (← binW)
    | "llvm.icmp.ult" => mkExprOf <| icmp .ult (← binW)
    | "llvm.icmp.ule" => mkExprOf <| icmp .ule (← binW)
    | "llvm.icmp.sgt" => mkExprOf <| icmp .sgt (← binW)
    | "llvm.icmp.sge" => mkExprOf <| icmp .sge (← binW)
    | "llvm.icmp.slt" => mkExprOf <| icmp .slt (← binW)
    | "llvm.icmp.sle" => mkExprOf <| icmp .sle (← binW)
     -- Alternative representation of icmp instructions like in MLIR generic syntax
    | "llvm.icmp" =>
      let ⟨n, ty⟩ ← opStx.getIntAttr "predicate"
      mkExprOf <| icmp (← parseIcmpPredicate n) (← binW)
    -- Unary Operations
    | "llvm.not"    => mkExprOf <| .not (← unW)
    | "llvm.neg"    => mkExprOf <| neg (← unW)
    | "llvm.copy"   => mkExprOf <| copy (← unW)
    | "llvm.freeze" => mkExprOf <| freeze (← unW)
    | "llvm.zext"   => mkExprOf <| zext (← unW) (← getOutputWidth opStx "zext") ⟨ opStx.hasAttr "nonNeg" ⟩
    | "llvm.sext"   => mkExprOf <| sext (← unW) (← getOutputWidth opStx "sext")
    | "llvm.trunc"  => mkExprOf <| trunc (← unW) (← getOutputWidth opStx "trunc") (← parseOverflowFlags opStx)
    -- Poison
    | "llvm.mlir.poison" =>
      mkExprOf <| MOp.poison (← getOutputTy opStx "llvm.mlir.poison")
    -- NOTE: LLVM's `undef` is weaker than `poison` (it may take a different
    -- value at each use); modelling it as poison is the usual simplification.
    | "llvm.mlir.undef" =>
      mkExprOf <| MOp.poison (← getOutputTy opStx "llvm.mlir.undef")
    -- Constant
    -- NOTE: dispatch on the *result* type rather than the attribute's type: the
    -- two must agree in MLIR, but only the former is what `mkExprOf` will use.
    | "llvm.mlir.constant" =>
      match ← getOutputTy opStx "llvm.mlir.constant" with
      | .bitvec w =>
        let ⟨val, _⟩ ← opStx.getIntAttr "value"
        mkExprOf <| const w val
      | t =>
        let some (.dense v _) := opStx.getAttr? "value"
          | throw <| .generic
              "llvm.mlir.constant: a non-scalar constant needs a `dense<…>` value"
        mkExprOf <| MOp.constDense t (← denseInts v)
    -- Vector operations
    | "llvm.insertelement" =>
      let .vector l elem ← getOutputTy opStx "llvm.insertelement"
        | throw <| .generic "llvm.insertelement: result must be a vector"
      let .bitvec idxW ← getArgTy opStx "llvm.insertelement" 2
        | throw <| .generic "llvm.insertelement: index must be an integer"
      mkExprOf <| MOp.insertelement elem l idxW
    | "llvm.extractelement" =>
      let .vector l elem ← getArgTy opStx "llvm.extractelement" 0
        | throw <| .generic "llvm.extractelement: operand must be a vector"
      let .bitvec idxW ← getArgTy opStx "llvm.extractelement" 1
        | throw <| .generic "llvm.extractelement: index must be an integer"
      mkExprOf <| MOp.extractelement elem l idxW
    | "llvm.shufflevector" =>
      let .vector l elem ← getArgTy opStx "llvm.shufflevector" 0
        | throw <| .generic "llvm.shufflevector: operands must be vectors"
      mkExprOf <| MOp.shufflevector elem l (← arrayInts opStx "llvm.shufflevector" "mask")
    -- AVX-512 IFMA, as the x86vector dialect spells it
    | "x86vector.avx512.intr.vpmadd52l.uq.512" =>
      mkExprOf <| MOp.vpmadd52 false (← getVectorLaneCount opStx opStx.name)
    | "x86vector.avx512.intr.vpmadd52h.uq.512" =>
      mkExprOf <| MOp.vpmadd52 true (← getVectorLaneCount opStx opStx.name)
    | "x86vector.avx512.intr.vpermi2var.q.512" =>
      mkExprOf <| MOp.vpermi2var (← getVectorLaneCount opStx opStx.name)
    -- ... and as a direct call to the LLVM intrinsic, which is how the same
    -- source lowers when the x86vector dialect is not used.
    | "llvm.call" =>
      let some (.symbol callee) := opStx.getAttr? "callee"
        | throw <| .generic "llvm.call: expected a `callee` symbol attribute"
      match callee with
      | "x86_avx512_vpmadd52l_uq_512" =>
        mkExprOf <| MOp.vpmadd52 false (← getVectorLaneCount opStx callee)
      | "x86_avx512_vpmadd52h_uq_512" =>
        mkExprOf <| MOp.vpmadd52 true (← getVectorLaneCount opStx callee)
      | "x86_avx512_vpermi2var_q_512" =>
        mkExprOf <| MOp.vpermi2var (← getVectorLaneCount opStx callee)
      | _ => throw <| .unsupportedOp s!"llvm.call to {callee}"
    -- Fallback
    | opName => throw <| .unsupportedOp opName

instance : AST.TransformExpr (MetaLLVM φ) φ :=
  { mkExpr := fun Γ opStx _regions => mkExpr Γ opStx }
instance : AST.TransformExpr LLVM 0 :=
  { mkExpr := fun Γ opStx _regions => mkExpr Γ opStx }

def mkReturn (Γ : Ctxt (MetaLLVM φ).Ty) (opStx : MLIR.AST.Op φ) :
    MLIR.AST.ReaderM (MetaLLVM φ) (Σ eff ty, Com (MetaLLVM φ) Γ eff ty) := do
  if opStx.name ≠ "llvm.return" then
    throw <| .unsupportedOp s!"Tried to build return out of non-return statement {opStx.name}"
  else
    let args ← (← opStx.parseArgs Γ).assumeArity 1
    let ⟨ty, v⟩ := args[0]
    return ⟨.pure, [ty], Com.ret v⟩

instance : AST.TransformReturn (MetaLLVM φ) φ := { mkReturn }
instance : AST.TransformReturn LLVM 0 := { mkReturn }

/-!
  ## Instantiation
  Finally, we show how to instantiate a family of programs to a concrete program
-/

open InstCombine LLVM Qq in
/-- Instantiate the width metavariables of a `MetaLLVM φ` type, producing the
`Expr` of the corresponding concrete `LLVM` type. Split out of `instantiate`
below because vectors make it recursive. -/
private def MetaLLVM.instantiateTy (vals : Vector Expr φ) : MTy φ → Expr
  | .bitvec w => mkApp (mkConst ``Ty.bitvec) <| w.metaInstantiate vals
  | .vector l e => mkApp2 (mkConst ``Ty.vector) (toExpr l) (instantiateTy vals e)

open InstCombine LLVM Qq in
def MetaLLVM.instantiate (vals : Vector Expr φ) : DialectMetaMorphism (MetaLLVM φ) q(LLVM) where
  mapTy := MetaLLVM.instantiateTy vals
  mapOp :=
    fun
    | .binary w binOp =>
      let w := w.metaInstantiate vals
      mkApp2 (mkConst ``Op.binary) w (toExpr binOp)
    | .unary w unOp =>
      let w := w.metaInstantiate vals

      /- NOTE: `Op` contructors expect a `Nat` argument to indicate the width,
          but `MOp.UnaryOp` constructors expect `ConcreteOrMVar Nat 0`.
          Hence, we define `mapWidth` to construct the latter
      -/
      let mapWidth (w : ConcreteOrMVar Nat φ) : Q(ConcreteOrMVar Nat 0) :=
        let w : Q(Nat) := w.metaInstantiate vals
        q(.concrete $w)
      open MOp (UnaryOp) in
      let unOp : Q(UnaryOp 0) := match unOp with
        | .neg => q(.neg)
        | .not => q(.not)
        | .copy => q(.copy)
        | .freeze => q(.freeze)
        | .trunc w' flags => q(.trunc $(mapWidth w') $flags)
        | .zext w' nneg => q(.zext $(mapWidth w') $nneg)
        | .sext w' => q(.sext $(mapWidth w'))
      mkApp2 (mkConst ``Op.unary) w unOp
    | .select w =>
      let w : Q(Nat) := w.metaInstantiate vals
      mkApp (mkConst ``Op.select) w
    | .icmp c w =>
      let w := w.metaInstantiate vals
      let c := toExpr c
      mkApp2 (mkConst ``Op.icmp) c w
    | .poison t =>
      mkApp (mkConst ``Op.poison) (MetaLLVM.instantiateTy vals t)
    | .constDense t elems =>
      mkApp2 (mkConst ``Op.constDense) (MetaLLVM.instantiateTy vals t) (toExpr elems)
    | .insertelement e l w =>
      mkApp3 (mkConst ``Op.insertelement) (MetaLLVM.instantiateTy vals e) (toExpr l)
        (w.metaInstantiate vals)
    | .extractelement e l w =>
      mkApp3 (mkConst ``Op.extractelement) (MetaLLVM.instantiateTy vals e) (toExpr l)
        (w.metaInstantiate vals)
    | .shufflevector e l mask =>
      mkApp3 (mkConst ``Op.shufflevector) (MetaLLVM.instantiateTy vals e) (toExpr l)
        (toExpr mask)
    | .vpmadd52 hi l =>
      mkApp2 (mkConst ``Op.vpmadd52) (toExpr hi) (toExpr l)
    | .vpermi2var l =>
      mkApp (mkConst ``Op.vpermi2var) (toExpr l)
    | .vectorBinary l w bop =>
      mkApp3 (mkConst ``Op.vectorBinary) (toExpr l) (w.metaInstantiate vals) (toExpr bop)
    | .const w val =>
      let w := w.metaInstantiate vals
      let val := toExpr val
      mkApp2 (mkConst ``Op.const) w val

end InstcombineTransformDialect


open SSA InstcombineTransformDialect InstCombine in
elab "[llvm(" mvars:term,* ")| " reg:mlir_region "]" : term => do
  withTraceNode `LeanMLIR.Elab (pure m!"{exceptEmoji ·} elaborate LLVM program") <| do

  let φ : Nat := mvars.getElems.size
  let ⟨_, _, _, mcom⟩ ← SSA.elabIntoComObj reg (MetaLLVM φ)

  let res ← mcom.metaMap <| MetaLLVM.instantiate <| ←do
    let mvars : Vector _ φ := ⟨mvars.getElems, rfl⟩
    mvars.mapM fun (stx : Term) =>
      elabTermEnsuringType stx (mkConst ``Nat)

  trace[LeanMLIR.Elab] "elaborated expression: {res}"
  return res

macro "[llvm| " reg:mlir_region "]" : term => `([llvm()| $reg])
