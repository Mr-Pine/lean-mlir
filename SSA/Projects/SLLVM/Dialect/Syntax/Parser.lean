/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Qq

public import LeanMLIR.MLIRSyntax
public import SSA.Projects.SLLVM.Dialect.Basic
-- the `[sllvm| ..]` elaborators are `meta`
public meta import LeanMLIR.MLIRSyntax
public meta import SSA.Projects.SLLVM.Dialect.Basic

@[expose] public section

namespace LeanMLIR.SLLVM

-- open Qq Lean Meta Elab.Term Elab Command
open InstCombine (LLVM)
open MLIR
open MLIR.AST


/-! ### LLVM aggregate types and their layout

`!llvm.struct<"…", (…)>` / `!llvm.array<n x t>` reach the AST as the verbatim
text of the type (inside `MLIRType.undefined`); `getelementptr` needs their
layout, so the text is decoded here. Default data layout, no packed structs.
-/

/-- An LLVM aggregate element type, as `getelementptr`'s `elem_type` spells
it. -/
inductive AggTy where
  | int (bits : Nat)
  | ptr
  | struct (fields : List AggTy)
  | array (n : Nat) (elem : AggTy)
  | vector (n : Nat) (elem : AggTy)
  deriving Repr

def takeAggNat (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none else some ((String.ofList ds).toNat!, cs.dropWhile Char.isDigit)

def dropWs (cs : List Char) : List Char :=
  cs.dropWhile (· == ' ')

mutual
/-- Decode one aggregate type from the head of `cs`. -/
partial def parseAggTy : List Char → Option (AggTy × List Char)
  | 'i' :: cs => (takeAggNat cs).map fun (w, rest) => (.int w, rest)
  | 'p' :: 't' :: 'r' :: cs => some (.ptr, cs)
  | 'a' :: 'r' :: 'r' :: 'a' :: 'y' :: '<' :: cs => do
    let (n, cs) ← takeAggNat (dropWs cs)
    let 'x' :: cs := dropWs cs | none
    let (t, cs) ← parseAggTy (dropWs cs)
    let '>' :: cs := dropWs cs | none
    return (.array n t, cs)
  | 'v' :: 'e' :: 'c' :: 't' :: 'o' :: 'r' :: '<' :: cs => do
    let (n, cs) ← takeAggNat (dropWs cs)
    let 'x' :: cs := dropWs cs | none
    let (t, cs) ← parseAggTy (dropWs cs)
    let '>' :: cs := dropWs cs | none
    return (.vector n t, cs)
  | 's' :: 't' :: 'r' :: 'u' :: 'c' :: 't' :: '<' :: cs => do
    -- optional `"name", `
    let cs := dropWs cs
    let cs ←
      match cs with
      | '"' :: cs =>
        let cs := cs.dropWhile (· != '"')
        let '"' :: cs := cs | none
        let ',' :: cs := dropWs cs | none
        pure (dropWs cs)
      | _ =>
        pure cs
    let '(' :: cs := cs | none
    let (fields, cs) ← parseAggFields (dropWs cs) []
    let '>' :: cs := dropWs cs | none
    return (.struct fields, cs)
  | _ => none
/-- `t (`, ` t)* `)`` -/
partial def parseAggFields (cs : List Char) (acc : List AggTy) : Option (List AggTy × List Char) :=
  do
  let (t, cs) ← parseAggTy cs
  match dropWs cs with
  | ',' :: cs =>
    parseAggFields (dropWs cs) (t :: acc)
  | ')' :: cs =>
    return ((t :: acc).reverse, cs)
  | _ =>
    none
end

/-- Round `off` up to a multiple of `a`. -/
def alignTo (off a : Nat) : Nat :=
  ((off + a - 1) / a) * a

/-- `(size, alignment)` in bytes, per LLVM's default data layout. An array
element's stride is its padded size; a struct is laid out sequentially with
padding, then padded to its own alignment. -/
partial def AggTy.sizeAlign : AggTy → ExceptM SLLVM (Nat × Nat)
  | .int bits =>
      let sz := (bits + 7) / 8
      if sz == 1 || sz == 2 || sz == 4 || sz == 8 || sz == 16 then return (sz, sz)
    else throw <| .generic s!"llvm.getelementptr: unsupported integer size i{bits}"
  | .ptr => return (8, 8)
  | .array n t => do
    let (s, a) ← t.sizeAlign
    return (n * alignTo s a, a)
  -- Vectors are unpadded, and their alignment is the size rounded up to a
  -- power of two (LLVM's default layout), not the element's.
  | .vector n t => do
    let (s, _) ← t.sizeAlign
    let sz := n * s
    return (sz, Nat.nextPowerOfTwo sz)
  | .struct fields => do
    let (off, al) ←
      fields.foldlM (init := (0, 1)) fun (off, al) f => do
          let (s, a) ← f.sizeAlign
          return (alignTo off a + s, max al a)
    return (alignTo off al, al)

/-- Byte offset of field `k` of a struct, `k`-scaled stride within an array. -/
partial def AggTy.constIndexOffset (k : Nat) : AggTy → ExceptM SLLVM (Nat × AggTy)
  | .struct fields => do
    if h : k < fields.length then
      -- end of the k-field prefix, then align up to field k's alignment
      let off ←
        (fields.take k).foldlM (init := 0) fun off f => do
            let (s, a) ← f.sizeAlign
            return alignTo off a + s
      let fld := fields[k]
      let (_, a) ← fld.sizeAlign
      return (alignTo off a, fld)
    else
      throw <| .generic s!"llvm.getelementptr: struct field index {k} out of range"
  | .array n t => do
    unless k < n do
      throw <| .generic s!"llvm.getelementptr: array index {k} out of range"
    let (s, a) ← t.sizeAlign
    return (k * alignTo s a, t)
  | .vector n t => do
    unless k < n do
      throw <| .generic s!"llvm.getelementptr: vector index {k} out of range"
    let (s, _) ← t.sizeAlign
    return (k * s, t)
  | t => throw <| .generic s!"llvm.getelementptr: cannot index into {repr t}"

/-- The aggregate an `!llvm.…` type text denotes, or `none` when the text is
not an aggregate. Only `struct<…>` and `array<…>` qualify: `!llvm.ptr` also
decodes as an `AggTy`, but it is `Ty.ptr`, not a register aggregate. -/
def aggTyOfText? (s : String) : Option AggTy :=
  if s.startsWith "llvm.struct<" || s.startsWith "llvm.array<" then
    match parseAggTy (s.toList.drop "llvm.".length) with
    | some (t, []) => some t
    | _ => none
  else none

/-- The number of bits an aggregate occupies, i.e. its padded size. -/
def AggTy.widthBits (t : AggTy) : ExceptM SLLVM Nat := do
  let (sz, al) ← t.sizeAlign
  return 8 * alignTo sz al

/-- The `LLVM.Ty` (i.e. `SLLVM.Ty.arith`) counterpart of an MLIR type. Split
out of `mkTy` because vectors recurse through their element type, which is again
an arithmetic type, never `!ptr`. -/
def mkArithTy : MLIRType 0 → ExceptM SLLVM LLVM.Ty
  | .int .Signless w => return .bitvec w.toConcrete
  -- A fixed-length 1-D vector, as in the LLVM dialect: scalable or
  -- multi-dimensional vectors have no counterpart in `LLVM.Ty`.
  | .vector [length] [] elemTy => return .vector length (← mkArithTy elemTy)
  -- An aggregate held in a register (`!llvm.array<5 x i64>`,
  -- `!llvm.struct<…>`) becomes LLVM's own flat layout: a bitvector of the
  -- aggregate's padded size, lowest-addressed field in the low bits. That
  -- makes `insertvalue` a bit splice and a store of the aggregate a store of
  -- exactly the bytes LLVM would write. What it cannot express is per-field
  -- poison -- see `SLLVM.insertvalue`, which is conservative about it.
  | .undefined s =>
    match aggTyOfText? s with
    | some t => .bitvec <$> t.widthBits
    | none => throw <| .unsupportedType (some (MLIRType.undefined (φ := 0) s))
  | t => throw <| .unsupportedType (some t)

/-- `!ptr` is SLLVM's own spelling; `!llvm.ptr` is what `mlir-translate
--import-llvm` emits, and is the only one that appears in lifted code. -/
def mkTy : MLIRType 0 → ExceptM SLLVM SLLVM.Ty
  | .undefined "ptr" | .undefined "llvm.ptr" => return Ty.ptr
  | t => Ty.arith <$> mkArithTy t

instance : TransformTy SLLVM 0 where
  mkTy := mkTy

def getOutputWidth (opStx : MLIR.AST.Op 0) : Except TransformError Nat := do
  match opStx.res with
  | res :: [] =>
    match res.2 with
    | .int _ (.concrete w) =>
      pure w
    | _ =>
      throw <| .generic s!"The operation {opStx.name} must output an integer type"
  | _ =>
    throw <| .generic s!"The operation {opStx.name} must have a single output"

/-- The declared result type of a single-result operation, as an arithmetic
(`LLVM.Ty`) type. Unlike `getOutputWidth` this keeps the whole type, which
poison needs since it exists at vector types too. -/
def getOutputArithTy (opStx : MLIR.AST.Op 0) : ExceptM SLLVM LLVM.Ty := do
  match opStx.res with
  | res :: [] =>
    mkArithTy res.2
  | _ =>
    throw <| .generic s!"The operation {opStx.name} must have a single output"

/-- The declared result type of a single-result operation, as a full
`SLLVM.Ty`. `getOutputArithTy` gives only the arithmetic half, which a call's
result type need not be. -/
def getOutputTy (opStx : MLIR.AST.Op 0) : ExceptM SLLVM SLLVM.Ty := do
  match opStx.res with
  | res :: [] =>
    mkTy res.2
  | _ =>
    throw <| .generic s!"The operation {opStx.name} must have a single output"

/-- The declared type of the `i`-th operand of an operation. -/
def getArgArithTy (opStx : MLIR.AST.Op 0) (i : Nat) : ExceptM SLLVM LLVM.Ty := do
  match opStx.args[i]? with
  | some (_, t) =>
    mkArithTy t
  | none =>
    throw <| .generic s!"{opStx.name}: expected at least {i + 1} operand(s)"

/-- The arithmetic type of an already-parsed operand. Unlike `getArgArithTy`
this reads the type off the context variable rather than off the syntax, which
is what `llvm.store` needs: its stored value may be of any arithmetic type. -/
def argArithTy {Γ : Ctxt SLLVM.Ty} (opName : String) : (Σ t, Γ.Var t) → MLIR.AST.ReaderM SLLVM LLVM.Ty
  | ⟨Ty.arith t, _⟩ => return t
  | ⟨t, _⟩ => throw <| .generic s!"{opName}: expected an arithmetic operand, but found: {t}"

/-- `llvm.load`/`llvm.store` carry an `ordering` attribute; `0` is
`not_atomic`, and atomics are not modelled. `alignment`, `tbaa` and
`nontemporal` are accepted and ignored -- this memory model has no alignment
constraints and no alias-metadata semantics. -/
def checkNotAtomic (opStx : MLIR.AST.Op 0) : MLIR.AST.ReaderM SLLVM Unit :=
  match opStx.getAttr? "ordering" with
  | none => return ()
  | some (.int 0 _) => return ()
  | some _ =>
    throw <|
      .generic
        s!"{opStx.name}: atomic accesses are not modelled \
      (expected `ordering = 0`, i.e. non-atomic)"

/-- The integers inside a `dense<…>` attribute: either a single value (the
splat form) or one per lane. -/
def denseInts : MLIR.AST.AttrValue 0 → ExceptM SLLVM (List Int)
  | .int v _ => return [v]
  | .list xs =>
    xs.mapM fun
      | .int v _ => pure v
      | _ => throw <| .generic "llvm.mlir.constant: dense elements must be integers"
  | _ =>
    throw <|
      .generic "llvm.mlir.constant: expected an integer or a list of integers inside `dense<…>`"

/-- The aggregate type of a single-result operation, when its result is one. -/
def getOutputAggTy? (opStx : MLIR.AST.Op 0) : Option AggTy :=
  match opStx.res with
  | [(_, .undefined s)] => aggTyOfText? s
  | _ => none

/-- The flat value of a constant aggregate, as one `w`-bit integer: lane `0` in
the low bits, matching `LLVM.Ty.flattenBV`.

Only unpadded `array<n x iW>` is supported -- the shape `mlir-translate` emits
for a constant `uint64_t[n]` initialiser. A padded array, or a struct, would
have to say what its padding bits hold, and `Op.const` has no way to say
"undef" for part of a value. -/
def constAggInt (opStx : MLIR.AST.Op 0) (agg : AggTy) (w : Nat) :
    ExceptM SLLVM Int := do
  let some (.dense v _) := opStx.getAttr? "value"
    | throw <| .generic
        "llvm.mlir.constant: an aggregate constant needs a `dense<…>` value"
  let .array n (.int laneW) := agg
    | throw <| .generic "llvm.mlir.constant: only `array<n x iN>` aggregate \
        constants are supported"
  unless laneW * n == w do
    throw <| .generic s!"llvm.mlir.constant: a padded `array<{n} x i{laneW}>` \
      constant is not supported"
  -- `dense<c>` is the splat form: one element standing for every lane.
  let lanes ← match ← denseInts v with
    | [c] => pure (List.replicate n c)
    | lanes => pure lanes
  unless lanes.length == n do
    throw <| .generic s!"llvm.mlir.constant: {lanes.length} dense elements for an \
      `array<{n} x i{laneW}>` constant"
  return lanes.foldr (fun x acc => acc <<< laneW + x.emod (2 ^ laneW)) 0

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
def getIntWidth {Γ : Ctxt SLLVM.Ty} : (Σ t, Γ.Var t) → MLIR.AST.ReaderM SLLVM Nat
  | ⟨Ty.bitvec w, _⟩ => return w
  | ⟨t, _⟩ => throw <| .generic s!"Expected type `bitvec _`, but found: {t}"

def parseOverflowFlags (op : AST.Op 0) : MLIR.AST.ReaderM SLLVM LLVM.NoWrapFlags :=
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
      MLIR.AST.ReaderM SLLVM (Σ eff returnTy, Expr SLLVM Γ eff returnTy) := do
    let args ← args.assumeArity 2
    match args[0].1 with
    | Ty.bitvec w => mkExprOf <| Op.arith (.binary w bop)
    | Ty.arith (.vector l (.bitvec (.concrete w))) => mkExprOf <| Op.vectorBinary l w bop
    | t => throw <| .generic s!"llvm.{bop}: expected bitvector or vector operands, found {t}"

  match opStx.name with
    -- new SLLVM operations
    | "ptr.add" => mkExprOf <| .ptradd
    -- Constant indices sum to byte offsets and each `-2147483648` sentinel takes
    -- a dynamic operand, giving `gepConst`, `gep` or `gep2` by sentinel count.
    -- `inbounds` is ignored (see `SLLVM.gep`).
    | "llvm.getelementptr" => do
        let idxs ← arrayInts opStx "rawConstantIndices"
        let t ← opStx.getTypeAttr "elem_type"
        let aggTy ← match t with
          | .int _ w => pure (AggTy.int w.toConcrete)
          | .undefined s =>
              match parseAggTy (s.toList.drop "llvm.".length) with
              | some (t, []) => pure t
              | _ => throw <| .generic s!"llvm.getelementptr: cannot decode \
                  `elem_type = !{s}`"
          | t => throw <| .generic s!"llvm.getelementptr: unsupported `elem_type` {repr t}"
        let (elemSize, elemAlign) ← aggTy.sizeAlign
        -- `(ty, strides, offsets, cur)`: the type being indexed, one stride per
        -- sentinel, the offsets each later sentinel closes, the open offset.
        let init : Option AggTy × List Nat × List Nat × Nat := (none, [], [], 0)
        let (_, strides, offsets, cur) ← idxs.foldlM (init := init) fun (ty?, ss, os, cur) k => do
          -- the stride and the element type this index steps over
          let (stride, next) ← match ty? with
            | none => pure (alignTo elemSize elemAlign, aggTy)
            | some (.array _ e) => do
                let (s, a) ← e.sizeAlign
                pure (alignTo s a, e)
            | some (.vector _ e) => do
                let (s, _) ← e.sizeAlign
                pure (s, e)
            | some ty =>
                if k == -2147483648 then
                  throw <| .generic s!"llvm.getelementptr: a dynamic index must \
                    index an array or vector, not {repr ty}"
                else pure (0, ty)
          if k == -2147483648 then
            let (os, cur) := if ss.isEmpty then (os, cur) else (os ++ [cur], 0)
            return (some next, ss ++ [stride], os, cur)
          unless k ≥ 0 do
            throw <| .generic s!"llvm.getelementptr: negative constant index {k}"
          match ty? with
          | none => return (some next, ss, os, cur + k.toNat * stride)
          | some ty =>
              let (step, next) ← ty.constIndexOffset k.toNat
              return (some next, ss, os, cur + step)
        match strides, offsets ++ [cur] with
        | [], [off] =>
            let _ ← args.assumeArity 1
            mkExprOf <| SLLVMOp.gepConst off
        | [stride], [off] =>
            let _ ← args.assumeArity 2
            mkExprOf <| SLLVMOp.gep stride off
        | [stride₀, stride₁], [off₀, off₁] =>
            let _ ← args.assumeArity 3
            mkExprOf <| SLLVMOp.gep2 stride₀ off₀ stride₁ off₁
        | _, _ => throw <| .generic "llvm.getelementptr: more than two dynamic indices"
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
    -- Aggregate element types (`fd_f25519_t r[1]` and friends) allocate a
    -- block of the aggregate's padded size: memory is flat bytes here, so
    -- the layout is all an aggregate alloca needs.
    | "llvm.alloca" => do
        let tStx ← opStx.getTypeAttr "elem_type"
        let w ← match tStx with
          | .undefined s =>
              match aggTyOfText? s with
              | some t => (AggTy.widthBits t : ExceptM SLLVM _)
              | none => throw <| .generic s!"llvm.alloca: unsupported \
                  `elem_type` !{s}"
          | t => do pure (LLVM.Ty.width (← mkArithTy t))
        opStx.mkExprOf (args? := some (Op.ParsedArgs.ofList [])) Γ
          <| .alloca w
    -- `llvm.intr.memset(ptr, i8, i64)`. `isVolatile` is accepted and ignored,
    -- as alignment is throughout.
    | "llvm.intr.memset" => do
        let _ ← args.assumeArity 3
        mkExprOf <| SLLVMOp.memset
    | "llvm.intr.memcpy" => do
        let _ ← args.assumeArity 3
        mkExprOf <| SLLVMOp.memcpy
    -- A reinterpretation of the operand's flat bits; the two types must have
    -- the same width, which MLIR checks and `SLLVM.bitcast` re-establishes.
    | "llvm.bitcast" => do
        let args ← args.assumeArity 1
        mkExprOf <| SLLVMOp.bitcast (← argArithTy opStx.name args[0])
          (← getOutputArithTy opStx)
    -- A global's address, read out of the state's symbol table. The
    -- initialiser is not bound here: the table is keyed by name, so what the
    -- global holds is a spec-level hypothesis, not something the program
    -- carries. See `SLLVM.addressof`.
    | "llvm.mlir.addressof" => do
        let some (.symbol g) := opStx.getAttr? "global_name"
          | throw <| .generic "llvm.mlir.addressof: expected a `global_name` \
              symbol attribute"
        opStx.mkExprOf (args? := some (Op.ParsedArgs.ofList [])) Γ <| SLLVMOp.addressof g
    -- `llvm.mlir.zero`: the zero value of the result type. At `!llvm.ptr` that
    -- is the null pointer, which is its own operation; at an arithmetic type it
    -- is just the constant 0.
    | "llvm.mlir.zero" => do
        match ← getOutputTy opStx with
        | .ptr => opStx.mkExprOf (args? := some (Op.ParsedArgs.ofList [])) Γ <| SLLVMOp.nullptr
        | .arith (LLVM.Ty.bitvec w) => mkExprOf <| Op.const w 0
        | _ => throw <| .generic "llvm.mlir.zero: only `!llvm.ptr` and integer \
            result types are supported"
    -- Stack-coloring metadata: no semantics here, but part of the artifact, so
    -- they parse (and denote to nothing) rather than having to be stripped.
    -- `llvm.intr.fshl(hi, lo, amount)`, all three at the same integer type.
    | "llvm.intr.fshl" => do
        let args ← args.assumeArity 3
        mkExprOf <| SLLVMOp.fshl (← getIntWidth args[0])
    | "llvm.intr.fshr" => do
        let args ← args.assumeArity 3
        mkExprOf <| SLLVMOp.fshr (← getIntWidth args[0])
    | "llvm.intr.bswap" => do
        let args ← args.assumeArity 1
        mkExprOf <| SLLVMOp.bswap (← getIntWidth args[0])
    | "llvm.intr.smin" => do
        let args ← args.assumeArity 2
        mkExprOf <| SLLVMOp.smin (← getIntWidth args[0])
    | "llvm.intr.lifetime.start" => mkExprOf <| SLLVMOp.lifetime true
    | "llvm.intr.lifetime.end"   => mkExprOf <| SLLVMOp.lifetime false
    -- Ternary Operations
    | "llvm.select" => do
        let args ← args.assumeArity 3
        match args[1] with
        | ⟨Ty.arith (.vector l (.bitvec (.concrete w))), _⟩ => mkExprOf <| SLLVMOp.vselect l w
        | ⟨Ty.ptr, _⟩ => mkExprOf <| SLLVMOp.ptrselect
        | _ => mkExprOf <| Op.select (← getIntWidth args[1])
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
    | "llvm.icmp" => do
      let ⟨n, _⟩ ← opStx.getIntAttr "predicate"
      let some c := LLVM.IntPred.ofMLIRPredicate? n
        | throw <| .generic s!"llvm.icmp: unsupported predicate {n}"
      -- at `!llvm.ptr` it is `ptricmp`; the operand type is what tells them apart
      match (← args.assumeArity 2)[0] with
      | ⟨Ty.ptr, _⟩ => match c with
        | .eq => mkExprOf <| SLLVMOp.ptricmp true
        | .ne => mkExprOf <| SLLVMOp.ptricmp false
        | _ => throw <| .generic "llvm.icmp at `!llvm.ptr`: only `eq` and `ne` \
            are supported"
      | ⟨Ty.arith (.vector l (.bitvec (.concrete w))), _⟩ =>
          mkExprOf <| SLLVMOp.vicmp l w c
      | _ => mkExprOf <| Op.icmp c (← binW)
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
        -- A constant *aggregate* (`dense<[…]> : tensor<5xi64>` at
        -- `!llvm.array<5 x i64>`) reaches here as a bitvector too, since
        -- `mkArithTy` flattens aggregates. Its lanes pack into one `w`-bit
        -- constant, lane 0 in the low bits, which is the same layout
        -- `LLVM.Ty.flattenBV` gives a vector.
        match getOutputAggTy? opStx with
        | some agg => mkExprOf <| Op.const w (← constAggInt opStx agg w)
        | none =>
          let ⟨val, _⟩ ← opStx.getIntAttr "value"
          mkExprOf <| Op.const w val
      | t =>
        let some (.dense v _) := opStx.getAttr? "value"
          | throw <| .generic
              "llvm.mlir.constant: a non-scalar constant needs a `dense<…>` value"
        mkExprOf <| Op.constDense t (← denseInts v)
    -- `llvm.insertvalue` at a constant `position`. Aggregate registers are
    -- their flat layout, so the position walks the aggregate type down to a
    -- byte offset and the operation is a splice of the field's bits.
    -- `extractvalue` is not modelled; nothing in the artifacts reads a field
    -- back out of a register.
    | "llvm.insertvalue" => do
        let args ← args.assumeArity 2
        let aggW ← getIntWidth args[0]
        -- The field may be any arithmetic type, not just a `bitvec`: an
        -- AVX-512 `struct.fd_f25519` holds a `vector<8xi64>`.
        -- `fieldArithTy` is the *operand's* type; `fieldTy` below is the field
        -- the position walk selects out of the aggregate. They must agree in
        -- width, which is what the check further down enforces.
        let fieldArithTy ← argArithTy "llvm.insertvalue" args[1]
        let fieldW := InstCombine.LLVM.Ty.width fieldArithTy
        let some (_, aggStx) := opStx.args[0]?
          | throw <| .generic "llvm.insertvalue: expected at least 1 operand"
        let .undefined s := aggStx
          | throw <| .generic "llvm.insertvalue: the aggregate operand must have an \
              `!llvm.…` aggregate type"
        let some agg := aggTyOfText? s
          | throw <| .generic s!"llvm.insertvalue: cannot decode aggregate type !{s}"
        let (offset, fieldTy) ← (← arrayInts opStx "position").foldlM
            (init := ((0 : Nat), agg)) fun (off, ty) k => do
          unless k ≥ 0 do
            throw <| .generic s!"llvm.insertvalue: negative position index {k}"
          let (step, ty) ← ty.constIndexOffset k.toNat
          return (off + step, ty)
        -- The field must be exactly the bits the position selects: a narrower
        -- one would leave the padding it does not cover unaccounted for.
        let fieldTyW ← match fieldTy with
          | .int bits => pure bits
          | t => t.widthBits
        unless fieldTyW == fieldW && 8 * offset + fieldW ≤ aggW do
          throw <| .generic s!"llvm.insertvalue: a {fieldW}-bit operand does not fit \
            the {fieldTyW}-bit field at byte offset {offset} of a {aggW}-bit aggregate"
        mkExprOf <| SLLVMOp.insertvalue aggW (8 * offset) fieldArithTy
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
region always wins over a binding. Recurses into nested regions (a bound
callee's own calls need their bodies too) and into a multi-block region's
tail blocks. -/
partial def bindCallees (table : List (String × Region 0)) (reg : Region 0) :
    Region 0 :=
  { reg with
    ops := reg.ops.map goOp
    blocks := reg.blocks.map fun b => { b with ops := b.ops.map goOp } }
where
  goOp (op : Op 0) : Op 0 :=
    let op := { op with regions := op.regions.map (bindCallees table) }
    if op.name != "llvm.call" || !op.regions.isEmpty then op
    else match op.getAttr? "callee" with
      | some (.symbol callee) =>
          match table.lookup callee with
          | some r => { op with regions := [bindCallees table r] }
          | none   => op
      | _ => op

/-- `AggTy`, back as `getelementptr`'s `elem_type` spells it. Struct names are
not kept by `AggTy`, so they are dropped -- `parseAggTy` treats them as
optional, and only the layout is ever read. -/
partial def AggTy.print : AggTy → String
  | .int w => s!"i{w}"
  | .ptr => "ptr"
  | .array n t => s!"array<{n} x {t.print}>"
  | .vector n t => s!"vector<{n}x{t.print}>"
  | .struct fields => "struct<(" ++ String.intercalate ", " (fields.map print) ++ ")>"

def _root_.MLIR.AST.AttrDict.set (d : AttrDict 0) (key : String) (v : AttrValue 0) :
    AttrDict 0 :=
  match d with
  | .mk entries => .mk <| entries.map fun
      | .mk k old => .mk k (if k == key then v else old)

open MLIR.AST in
/-- Fold away a gep's leading zero index.

GCC spells `x->limb[k]` as a gep with *two* dynamic index operands
(`rawConstantIndices = array<i32: -2147483648, -2147483648>`): a leading `0`
into the pointee and the limb index, both SSA values. `SLLVMOp.gep` carries
exactly one dynamic index, so the shape is normalised here, on the AST: a gep
of `array<n x t>` whose leading operand is visibly the constant `0` is
`ptradd` by `sizeof t · i`, i.e. the single-index gep of `t` that the parse
arm already accepts. Anything else -- a leading index that is not a visible
zero, a non-array element type -- is left for the parse arm to reject. Each
region is its own scope; only entry-block constants are collected, which is
where MLIR hoists them. -/
partial def foldGepZeroIndex (reg : Region 0) : Region 0 :=
  let zeros := reg.ops.filterMap fun op =>
    if op.name == "llvm.mlir.constant" then
      match op.getAttr? "value", op.res with
      | some (.int 0 _), [(name, _)] => some name
      | _, _ => none
    else none
  { reg with
    ops := reg.ops.map (goOp zeros)
    blocks := reg.blocks.map fun b => { b with ops := b.ops.map (goOp zeros) } }
where
  sentinel : Int := -2147483648
  goOp (zeros : List SSAVal) (op : Op 0) : Op 0 :=
    let op := { op with regions := op.regions.map foldGepZeroIndex }
    if op.name != "llvm.getelementptr" then op
    else match op.getAttr? "rawConstantIndices", op.args, op.getAttr? "elem_type" with
      | some (.array ity (.int s₀ _ :: .int s₁ t₁ :: rest)),
        p :: (idx₀, _) :: idxs,
        some (.type (.undefined tyText)) =>
          if s₀ == sentinel && s₁ == sentinel && zeros.contains idx₀ then
            match parseAggTy (tyText.toList.drop "llvm.".length) with
            | some (.array _ elem, []) =>
                let elemAttr : AttrValue 0 := match elem with
                  | .int w => .type (MLIRType.int .Signless w)
                  | t => .type (.undefined ("llvm." ++ t.print))
                { op with
                  args := p :: idxs
                  attrs := op.attrs
                    |>.set "elem_type" elemAttr
                    |>.set "rawConstantIndices" (.array ity (.int s₁ t₁ :: rest)) }
            | _ => op
          else op
      | _, _, _ => op

open MLIR.AST in
/-- The one semantic assumption the `llvm.alloca` parse arm makes, checked:
`Op.alloca` allocates a single element, so every `llvm.alloca`'s count operand
must be visibly the constant 1. Checked on the region AST because the count is
an SSA operand -- `mkExpr` sees one operation at a time and cannot follow it
to its defining constant. Each region is its own scope: a bound callee's `%0`
is not its caller's. -/
partial def allocaCountsAreOne (reg : Region 0) : Except String Unit := do
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
meta def elabRegionTerm (t : Term) : TermElabM (MLIR.AST.Region 0) := do
  let e ← elabTermEnsuringTypeQ t q(MLIR.AST.Region 0)
  synthesizeSyntheticMVarsNoPostponing
  SSA.evalExprOfTypeRegion 0 (← instantiateMVars e)

open Lean Elab Term in
meta def elabCalleeTable (bs : Array (TSyntax ``sllvmCallee)) :
    TermElabM (List (String × MLIR.AST.Region 0)) :=
  bs.toList.mapM fun b => do
    match b with
    | `(sllvmCallee| @$name:ident := $t) =>
        return (name.getId.toString, ← elabRegionTerm t)
    | _ => throwUnsupportedSyntax

-- module: the elaborator needs this module's own dialect instances, which stay non-`meta`
set_option compiler.relaxedMetaCheck true in
elab "[sllvm| " reg:mlir_region "]" : term =>
  SSA.elabIntoCom' reg SLLVM (pre := foldGepZeroIndex) (check := allocaCountsAreOne)

-- module: the elaborator needs this module's own dialect instances, which stay non-`meta`
set_option compiler.relaxedMetaCheck true in
/-- `[sllvm| ‹region› with @f := fRegion]` binds the bodies of the symbols the
region's `llvm.call`s name, where `fRegion : MLIR.AST.Region 0` -- as
`[mlir_region| … ]` produces. MLIR's `llvm.call` carries no inline region, so
this is how a lifted call site gets its callee. -/
elab "[sllvm| " reg:mlir_region " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCalleeTable bs.getElems
  SSA.elabIntoCom' reg SLLVM (pre := foldGepZeroIndex ∘ bindCallees table)
    (check := allocaCountsAreOne)

-- module: the elaborator needs this module's own dialect instances, which stay non-`meta`
set_option compiler.relaxedMetaCheck true in
/-- `[sllvm| … ]` from an already-built `MLIR.AST.Region 0`, so a region can be
written once and used both as a `Com` and as a callee binding. -/
elab "[sllvm_of| " t:term "]" : term => do
  SSA.elabIntoCom'OfRegion (foldGepZeroIndex (← elabRegionTerm t)) SLLVM
    (check := allocaCountsAreOne)

-- module: the elaborator needs this module's own dialect instances, which stay non-`meta`
set_option compiler.relaxedMetaCheck true in
/-- `[sllvm_of| r with @f := fRegion]`: `[sllvm_of| r]` with callee bindings,
for a lifted region that both *is* a callee and *has* callees of its own. -/
elab "[sllvm_of| " t:term " with " bs:sllvmCallee,+ "]" : term => do
  let table ← elabCalleeTable bs.getElems
  SSA.elabIntoCom'OfRegion (foldGepZeroIndex (bindCallees table (← elabRegionTerm t))) SLLVM
    (check := allocaCountsAreOne)
