module

public import MLIR.Syntax.AST
public import MLIR.Func
public import MLIR.Semantics.Operations.LibCall

/-!
# MLIR AST to `Func`

`Prog.ofRegion` checks a parsed region and translates it to a `Prog`: the function's instructions
with registers as indices and every type resolved. `Prog.toFunc` builds the `Func`, and `mlir_def`
(`Syntax/Elab.lean`) builds the terms of a hand lift from the same `Prog`. `Prog.constant?` folds a
region that only builds a constant, as a global's initializer does.

Registers: `%argK` is `.arg K` and `%K` is `.val K`; a block's arguments are values, numbered as
MLIR numbers them. The translation is trusted, and guarded by tests.
-/

namespace MLIR

open MLIR

@[expose] public section

/-! ## Checked programs -/

/-- A register: `%argK` or `%K`. -/
inductive RegRef
  | arg (i : Nat)
  | val (i : Nat)
  deriving DecidableEq, Repr

/-- A constant, as written: a scalar, a vector's lanes or an integer array's elements, or one for
all (`dense<c>`); or an aggregate, as `Prog.constant?` folds it. -/
inductive ConstLit
  | bv (w : Nat) (v : Int)
  | vec (l w : Nat) (vs : List Int)
  | splat (l w : Nat) (v : Int)
  | array (n w : Nat) (vs : List Int)
  | arraySplat (n w : Nat) (v : Int)
  /-- A byte array, byte `i` `v`'s `i`-th lowest: a string, one literal however long. -/
  | bytes (n v : Nat)
  | null
  /-- An array's elements or a struct's fields, of type `t`. -/
  | agg (t : Ty) (ms : List ConstLit)
  deriving Repr

def ConstLit.ty : ConstLit → Ty
  | .bv w _ => .bv w
  | .vec l w _ | .splat l w _ => .vec l w
  | .array n w _ | .arraySplat n w _ => .array n (.bv w)
  | .bytes n _ => .array n (.bv 8)
  | .null => .ptr
  | .agg t _ => t

mutual
/-- `t`'s all-zero constant, with null pointers: `llvm.mlir.zero`. -/
def ConstLit.zero : Ty → ConstLit
  | .bv w => .bv w 0
  | .ptr => .null
  | .vec l w => .splat l w 0
  | .array n (.bv w) => .arraySplat n w 0
  | t@(.array n et) => .agg t (.replicate n (ConstLit.zero et))
  | t@(.struct fs) => .agg t (ConstLit.zeroFields fs)
def ConstLit.zeroFields : List Ty → List ConstLit
  | [] => []
  | t :: ts => ConstLit.zero t :: ConstLit.zeroFields ts
end

/-- An `Instr` with registers as indices; `dst` and `rets` index `Γ.vals`. -/
inductive PInstr
  | const (c : ConstLit) (dst : Nat)
  | poison (t : Ty) (dst : Nat)
  | unop {t₁ t : Ty} (op : UnOp t₁ t) (dst : Nat) (a : RegRef)
  | binop {t₁ t₂ t : Ty} (op : BinOp t₁ t₂ t) (dst : Nat) (a b : RegRef)
  | ternop {t₁ t₂ t₃ t : Ty} (op : TernOp t₁ t₂ t₃ t) (dst : Nat) (a b c : RegRef)
  | load (t : Ty) (dst : Nat) (p : RegRef)
  | store (t : Ty) (p v : RegRef)
  | maskedLoad (l w : Nat) (dst : Nat) (p mask passthru : RegRef)
  | maskedStore (l w : Nat) (v p mask : RegRef)
  | memset (w : Nat) (p v l : RegRef)
  | memcpy (w : Nat) (dst src l : RegRef)
  | memmove (w : Nat) (dst src l : RegRef)
  | ptrtoaddr (w : Nat) (dst : Nat) (p : RegRef)
  | ptricmp (pred : IntPred) (dst : Nat) (a b : RegRef)
  /-- `dead` until a `lifetimeStart`: an `alloca` with lifetime markers. -/
  | alloca (dst : Nat) (bytes : Nat) (dead : Bool)
  | lifetimeStart (p : RegRef) (bytes : Nat)
  | lifetimeEnd (p : RegRef) (bytes : Nat)
  | assume (c : RegRef)
  /-- A call of the symbol `callee`, from argument types `ts` to result types `us`; `noreturn` at
  the call site: UB. -/
  | call (callee : String) (ts us : List Ty) (args : List RegRef) (rets : List Nat)
    (noreturn : Bool)
  | addressof (global : String) (dst : Nat)

/-- A jump to block `target` with arguments `args`. -/
structure PJump where
  target : Nat
  args : List RegRef

inductive PExit
  | ret (vs : List RegRef)
  | unreachable
  | br (j : PJump)
  | condBr (c : RegRef) (t f : PJump)
  | switch (w : Nat) (v : RegRef) (dflt : PJump) (cases : List (Int × PJump))

structure PBlock where
  /-- The MLIR name, e.g. `bb1`. -/
  name : String
  /-- The block arguments' value registers. -/
  params : List Nat
  body : List PInstr
  exit : PExit

/-- A checked function: its blocks, entry block first, whose parameters are `[]`. -/
structure Prog where
  Γ : Ctx
  tRets : List Ty
  blocks : List PBlock

/-! ## Printing, for error messages -/

/-- `t` as spelled inside an `!llvm.` type: `ptr`, `array<…>`, `struct<…>` without the prefix. -/
def Ty.toMLIRInner : Ty → String
  | .bv w => s!"i{w}"
  | .ptr => "ptr"
  | .vec l w => s!"vector<{l}xi{w}>"
  | .array n t => s!"array<{n} x {t.toMLIRInner}>"
  | .struct fs => s!"struct<({", ".intercalate (fs.map toMLIRInner)})>"

def Ty.toMLIR : Ty → String
  | t@.ptr | t@(.array ..) | t@(.struct _) => "!llvm." ++ t.toMLIRInner
  | t => t.toMLIRInner

def MLIR.Op.render (op : Op) : String :=
  let vals (vs : List TypedSSAVal) := ", ".intercalate (vs.map (s!"%{·.1}"))
  let tys (vs : List TypedSSAVal) := ", ".intercalate (vs.map (toString ·.2))
  let res := if op.res.isEmpty then "" else s!"{vals op.res} = "
  let succs :=
    if op.successors.isEmpty then "" else s!"[{", ".intercalate (op.successors.map ("^" ++ ·))}]"
  let resTys := if let [(_, t)] := op.res then toString t else s!"({tys op.res})"
  s!"{res}\"{op.name}\"({vals op.args}){succs} : ({tys op.args}) -> {resTys}"

/-! ## Types and layouts -/

namespace Translate

def takeNat (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none else some ((String.ofList ds).toNat!, cs.dropWhile Char.isDigit)

def dropWs (cs : List Char) : List Char :=
  cs.dropWhile (· == ' ')

mutual
/-- Decode one type from the head of `cs`. A packed struct is the plain one when that has no
padding and, unless `top` (the type is no struct's field), its alignment is a byte's. -/
partial def parseTy (top : Bool) : List Char → Option (Ty × List Char)
  | 'i' :: cs => (takeNat cs).map fun (w, rest) => (.bv w, rest)
  | 'p' :: 't' :: 'r' :: cs => some (.ptr, cs)
  | 'a' :: 'r' :: 'r' :: 'a' :: 'y' :: '<' :: cs => do
    let (n, cs) ← takeNat (dropWs cs)
    let 'x' :: cs := dropWs cs | none
    let (t, cs) ← parseTy top (dropWs cs)
    let '>' :: cs := dropWs cs | none
    return (.array n t, cs)
  | 'v' :: 'e' :: 'c' :: 't' :: 'o' :: 'r' :: '<' :: cs => do
    let (n, cs) ← takeNat (dropWs cs)
    let 'x' :: cs := dropWs cs | none
    let (t, cs) ← parseTy false (dropWs cs)
    let '>' :: cs := dropWs cs | none
    match t with
    | .bv w =>
      return (.vec n w, cs)
    | .ptr =>
      return (.array n .ptr, cs)
    | _ =>
      none
  | 's' :: 't' :: 'r' :: 'u' :: 'c' :: 't' :: '<' :: cs => do
    -- an optional `"name", `
    let cs ←
      match dropWs cs with
      | '"' :: cs =>
        let '"' :: cs := cs.dropWhile (· != '"') | none
        let ',' :: cs := dropWs cs | none
        pure (dropWs cs)
      | cs =>
        pure cs
    let (packed, cs) :=
      match cs with
      | 'p' :: 'a' :: 'c' :: 'k' :: 'e' :: 'd' :: cs => (true, dropWs cs)
      | cs => (false, cs)
    let '(' :: cs := cs | none
    let (fields, cs) ← parseTyFields (dropWs cs) []
    let '>' :: cs := dropWs cs | none
    let t := Ty.struct fields
    if packed && (t.hasPadding || !top && t.align != 8) then none
    return (t, cs)
  | _ => none
/-- `t (, t)* )`, struct fields. -/
partial def parseTyFields (cs : List Char) (acc : List Ty) : Option (List Ty × List Char) := do
  let (t, cs) ← parseTy false cs
  match dropWs cs with
  | ',' :: cs =>
    parseTyFields (dropWs cs) (t :: acc)
  | ')' :: cs =>
    return ((t :: acc).reverse, cs)
  | _ =>
    none
end

def ty : MLIRType → Except String Ty
  | .int w => return .bv w
  | .vector [n] [] (.int w) => return .vec n w
  -- a pointer vector: `n` pointers, laid out as an array's
  | .vector [n] [] (.undefined "llvm.ptr") => return .array n .ptr
  | .undefined "llvm.ptr" => return .ptr
  | t@(.undefined s) =>
    match parseTy true ((s.drop "llvm.".length).toString.toList) with
    | some (a, []) => return a
    | _ => throw s!"cannot decode the type {t}"
  | t => throw s!"unsupported type {t}"

/-- The byte offset of element `k` of `t`, and that element's type. -/
def Ty.index (k : Nat) : Ty → Except String (Nat × Ty)
  | .struct fields => do
    let some f := fields[k]? | throw s!"struct field index {k} out of range"
    return (Ty.fieldOffset 0 k fields / 8, f)
  | .array n t => do
    unless k < n do
      throw s!"array index {k} out of range"
    return (k * t.size, t)
  | .vec n w => do
    unless k < n do
      throw s!"vector index {k} out of range"
    return (k * ((w + 7) / 8), .bv w)
  | t => throw s!"cannot index into {repr t}"

/-- The byte offset of `getelementptr`'s constant indices over `t`, for its one dynamic index
(`-2147483648`) the stride it steps by (the size of what it indexes), and the first index's part of
the offset: only the first index, over whole `t`s, may be negative. -/
def gepOffset (t : Ty) : List Int → Except String (Int × Option Nat × Int)
  | [] => return (0, none, 0)
  | k₀ :: ks => do
    let dynamic := -2147483648
    let natIdx (k : Int) : Except String Nat := do
      unless 0 ≤ k do
        throw s!"negative index {k}"
      return k.toNat
    -- the first index steps over whole `t`s, the others into `t`
    let (off, stride) : Int × Option Nat :=
      if k₀ == dynamic then (0, some t.size) else (k₀ * t.size, none)
    let first := off
    let (off, stride, _) ←
      ks.foldlM (init := (off, stride, t)) fun (off, stride, t) k => do
          if k == dynamic then
            if stride.isSome then
              throw "only one dynamic index is supported"
            let .array _ et := t | throw "a dynamic index must index an array"
            return (off, some et.size, et)
          let (step, t) ← Ty.index (← natIdx k) t
          return (off + step, stride, t)
    return (off, stride, first)

/-! ## Attributes -/

def intAttr? (op : Op) (k : String) : Option Int :=
  match op.getAttr? k with
  | some (.int v _) => some v
  | _ => none

/-- A `getelementptr`'s no-wrap flags: `noWrapFlags` (bits `inbounds`, `nusw`, `nuw`), or the
older `inbounds` attribute. -/
def gepFlags (op : Op) : Except String GepFlags := do
  let bits := (intAttr? op "noWrapFlags").getD 0
  unless 0 ≤ bits && bits < 8 do
    throw s!"unknown `noWrapFlags` {bits}"
  let inbounds := bits % 2 == 1 || (op.getAttr? "inbounds").isSome
  return { nusw := inbounds || bits / 2 % 2 == 1, nuw := bits / 4 % 2 == 1 }

def arrayInts (op : Op) (k : String) : Except String (List Int) := do
  let some (.array _ vs) := op.getAttr? k | throw s!"expected an `array<…>` attribute `{k}`"
  vs.mapM fun
      | .int v _ => pure v
      | _ => throw s!"`{k}` must hold integers"

def overflowFlags (op : Op) : Except String OverflowFlags :=
  let flag : String → Except String OverflowFlags
    | "nsw" => return { nsw := true }
    | "nuw" => return { nuw := true }
    | "none" => return {}
    | s => throw s!"unknown overflow flag `{s}`"
  match op.getAttr? "overflowFlags" with
  | none => return {}
  -- newer MLIR: a bit mask, `1` for `nsw` and `2` for `nuw`
  | some (.int v _) =>
    if 0 ≤ v && v < 4 then return { nsw := v % 2 == 1, nuw := v / 2 == 1 }
    else throw s!"unknown overflow flags `{v}`"
  | some (.opaque_ "llvm.overflow" s) => flag s
  | some (.list fs) =>
    fs.foldlM (init := {}) fun acc f => do
      let .opaque_ "llvm.overflow" s := f | throw "malformed `overflowFlags`"
      let f ← flag s
      return { nsw := acc.nsw || f.nsw, nuw := acc.nuw || f.nuw }
  | some _ => throw "malformed `overflowFlags`"

def intPred : Int → Except String IntPred
  | 0 => return .eq
  | 1 => return .ne
  | 2 => return .slt
  | 3 => return .sle
  | 4 => return .sgt
  | 5 => return .sge
  | 6 => return .ult
  | 7 => return .ule
  | 8 => return .ugt
  | 9 => return .uge
  | p => throw s!"unknown predicate {p}"

/-- The `w`-bit elements of a `dense<"0x…">` blob: each little-endian in `(w + 7) / 8` bytes. -/
def denseHex (w : Nat) (s : String) : Except String (List Int) := do
  let digit (c : Char) : Except String Nat :=
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else
      if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
      else
        if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
        else throw s!"`dense<\"0x…\">`: bad hex digit '{c}'"
  let rec bytes : List Char → Except String (List Nat)
    | h :: l :: cs => return (16 * (← digit h) + (← digit l)) :: (← bytes cs)
    | [] => pure []
    | _ => throw "`dense<\"0x…\">`: odd number of hex digits"
  let k := (w + 7) / 8
  let bs ← bytes (s.toList.drop 2)
  unless k > 0 && bs.length % k == 0 do
    throw s!"`dense<\"0x…\">`: {bs.length} bytes for {k}-byte elements"
  return (List.range (bs.length / k)).map fun i =>
      (((bs.drop (i * k)).take k).foldr (fun b v => 256 * v + b) 0 % 2 ^ w : Nat)

/-- The integers of a `dense<…>` value of `w`-bit elements: one per lane, or one for all;
`true` and `false` as `1` and `0`. -/
def denseInts (w : Nat) : AttrValue → Except String (List Int ⊕ Int)
  | .int v _ => return .inr v
  | .bool b => return .inr (if b then 1 else 0)
  | .str s => do
    unless s.startsWith "0x" do
      throw "expected a `dense<\"0x…\">` hex blob"
    -- a blob of one element is a splat
    match ← denseHex w s with
    | [v] =>
      return .inr v
    | vs =>
      return .inl vs
  | .list vs =>
    .inl <$>
      vs.mapM fun
        | .int v _ => pure v
        | .bool b => pure (if b then 1 else 0)
        | _ => throw "`dense<…>` elements must be integers"
  | _ => throw "expected integers inside `dense<…>`"

/-! ## Registers and blocks -/

/-- What the translation reads everywhere: the context and the block names. -/
structure Env where
  Γ : Ctx
  blocks : List String
  /-- The defining op of each value, for `alloca`'s count. -/
  defs : List (String × Op)
  /-- The values a `lifetime.start` marks: `alloca`s that start dead. -/
  started : List String := []

/-- The register of value `%v`: its number less `Γ.valBase`. -/
def valIdx (E : Env) (v : SSAVal) : Except String Nat := do
  let some i := v.toNat? | throw s!"unsupported value name %{v}"
  unless E.Γ.valBase ≤ i do
    throw s!"%{v} is below the region's first value %{E.Γ.valBase}"
  return i - E.Γ.valBase

def reg (E : Env) (v : SSAVal) : Except String (RegRef × Ty) := do
  if v.startsWith "arg" then
    if let some i := (v.drop 3).toString.toNat? then
      let some t := if E.Γ.argBase ≤ i then E.Γ.args[i - E.Γ.argBase]? else none
        | throw s!"%{v} is not an argument of the function"
      return (.arg (i - E.Γ.argBase), t)
  let i ← valIdx E v
  let some t := E.Γ.vals[i]? | throw s!"%{v} is not defined"
  return (.val i, t)

/-- An operand, checked against its type at the use. -/
def operand (E : Env) (v : TypedSSAVal) : Except String (RegRef × Ty) := do
  let (r, t) ← reg E v.1
  let t' ← ty v.2
  unless t == t' do
    throw s!"%{v.1} has type {t.toMLIR} but is used at {t'.toMLIR}"
  return (r, t)

def result (E : Env) (op : Op) : Except String (Nat × Ty) := do
  let [(v, t)] := op.res | throw s!"expected one result, found {op.res.length}"
  return (← valIdx E v, ← ty t)

def target (E : Env) (name : String) : Except String Nat :=
  match E.blocks.idxOf? name with
  | some i => return i
  | none => throw s!"unknown block ^{name}"

/-- A jump to `name` with `args`, checked against the target's parameters `blockTys`. -/
def jump (E : Env) (blockTys : List (List Ty)) (name : String) (args : List TypedSSAVal) :
    Except String PJump := do
  let i ← target E name
  let tys := blockTys[i]?.getD []
  unless args.length == tys.length do
    throw s!"^{name} takes {tys.length} argument(s), but the jump passes {args.length}"
  let args ← args.mapM (operand E)
  for ((_, t), t', k) in args.zip (tys.zip (List.range tys.length)) do
    unless t == t' do
      throw s!"argument {k} of the jump to ^{name} has type {t.toMLIR}, expected {t'.toMLIR}"
  return ⟨i, args.map (·.1)⟩

/-! ## Operations -/

/-- A lane-wise or scalar binary operation, at the operands' type. -/
def arith (op : ∀ {w}, BinOp (.bv w) (.bv w) (.bv w)) :
    Nat × Ty → List (RegRef × Ty) → Except String PInstr
  | (dst, resTy), [(a, t₁), (b, t₂)] => do
    unless t₁ == t₂ && t₁ == resTy do
      throw s!"the operand and result types must agree"
    match t₁ with
    | .bv w =>
      return .binop (op (w := w)) dst a b
    | .vec l w =>
      return .binop (.vector (l := l) (op (w := w))) dst a b
    | t =>
      throw s!"unsupported operand type {t.toMLIR}"
  | _, _ => throw "expected two operands"

/-- The three operands of a vector intrinsic, all at `vector<l x iw>`. -/
def vec3 (resTy : Ty) : List (RegRef × Ty) → Except String (Nat × Nat × RegRef × RegRef × RegRef)
  | [(a, .vec l w), (b, t₂), (c, t₃)] => do
    unless t₂ == .vec l w && t₃ == .vec l w && resTy == .vec l w do
      throw "the operand and result types must agree"
    return (l, w, a, b, c)
  | _ => throw "expected three vector operands"

/-! ## Attributes

Each attribute the translation meets is `modeled`, `inert` or `ignored`; any other is rejected,
so none is dropped unseen. -/

/-- How the translation treats an attribute. -/
inductive AttrUse where
  /-- read into the operation, or checked -/
  | modeled
  /-- without semantics in the IR: calling conventions, linkage, profile and target hints -/
  | inert
  /-- UB, poison or unknown values LLVM adds that the model leaves out, so the model is more
  defined -/
  | ignored

/-- The attributes of the operation `name`, beyond `modeled` ones its translation reads.
`ignored`: GEP `inbounds`'s object bounds (its `nusw` is modeled), access
alignment, TBAA and alias scopes, call and intrinsic parameter attributes, memory effects,
`willreturn`, `tail` and `nounwind` (the model has no unwinding), loop `mustProgress`; `alloca`
alignment, as the model has no addresses; `volatile`, whose access the model makes plainly, its UB
conditions kept (one thread, no memory-mapped I/O). `inert`: atomic and fence orderings' `syncscope`
and a fence's ordering, as the model runs one thread; a `prefetch`'s hints. -/
def opAttrUses : String → List (String × AttrUse)
  | "llvm.add" | "llvm.sub" | "llvm.mul" | "llvm.shl" | "llvm.trunc" =>
    [("overflowFlags", .modeled)]
  | "llvm.or" => [("isDisjoint", .modeled)]
  | "llvm.lshr" | "llvm.ashr" => [("isExact", .modeled)]
  | "llvm.zext" => [("nonNeg", .modeled)]
  | "llvm.icmp" => [("predicate", .modeled)]
  | "llvm.intr.cttz" => [("is_zero_poison", .modeled)]
  | "llvm.intr.abs" => [("is_int_min_poison", .modeled)]
  | "llvm.intr.prefetch" => [("rw", .inert), ("hint", .inert), ("cache", .inert)]
  | "llvm.select" => [("fastmathFlags", .inert)]
  | "llvm.mlir.constant" => [("value", .modeled)]
  | "llvm.insertvalue" | "llvm.extractvalue" => [("position", .modeled)]
  | "llvm.shufflevector" => [("mask", .modeled)]
  | "llvm.mlir.addressof" => [("global_name", .modeled)]
  | "llvm.alloca" => [("elem_type", .modeled), ("alignment", .ignored)]
  | "llvm.getelementptr" =>
    [("elem_type", .modeled), ("rawConstantIndices", .modeled), ("noWrapFlags", .modeled),
      ("inbounds", .modeled)]
  | "llvm.load" | "llvm.store" =>
    [("ordering", .modeled), ("syncscope", .inert), ("alignment", .ignored), ("tbaa", .ignored),
      ("alias_scopes", .ignored), ("noalias_scopes", .ignored), ("volatile_", .ignored)]
  | "llvm.intr.masked.load" | "llvm.intr.masked.store" => [("alignment", .ignored)]
  | "llvm.intr.memset" | "llvm.intr.memcpy" | "llvm.intr.memmove" =>
    [("isVolatile", .ignored), ("arg_attrs", .ignored), ("tbaa", .ignored),
      ("alias_scopes", .ignored), ("noalias_scopes", .ignored)]
  | "llvm.intr.lifetime.start" | "llvm.intr.lifetime.end" => [("size", .modeled)]
  | "llvm.intr.assume" => [("op_bundle_sizes", .modeled), ("op_bundle_tags", .modeled)]
  | "llvm.intr.experimental.noalias.scope.decl" => [("scope", .inert)]
  | "llvm.fence" => [("ordering", .inert), ("syncscope", .inert)]
  | "llvm.inline_asm" =>
    [("asm_string", .modeled), ("constraints", .modeled), ("asm_dialect", .inert),
      ("has_side_effects", .inert), ("is_align_stack", .inert), ("tail_call_kind", .ignored)]
  | "llvm.call" =>
    [("callee", .modeled), ("op_bundle_sizes", .modeled), ("operandSegmentSizes", .modeled),
      ("noreturn", .modeled), ("CConv", .inert), ("fastmathFlags", .inert), ("no_inline", .inert),
      ("inline_hint", .inert), ("TailCallKind", .ignored), ("arg_attrs", .ignored),
      ("res_attrs", .ignored), ("memory_effects", .ignored), ("no_unwind", .ignored),
      ("will_return", .ignored), ("alias_scopes", .ignored), ("noalias_scopes", .ignored)]
  | "llvm.call_intrinsic" =>
    [("intrin", .modeled), ("op_bundle_sizes", .modeled), ("operandSegmentSizes", .modeled),
      ("fastmathFlags", .inert), ("arg_attrs", .ignored), ("res_attrs", .ignored)]
  | "llvm.br" => [("loop_annotation", .ignored)]
  | "llvm.cond_br" =>
    [("operandSegmentSizes", .modeled), ("branch_weights", .inert), ("loop_annotation", .ignored)]
  | "llvm.switch" =>
    [("case_values", .modeled), ("case_operand_segments", .modeled),
      ("operandSegmentSizes", .modeled), ("branch_weights", .inert)]
  | _ => []

/-- A function's attributes. `ignored`: memory effects, `willreturn` and `nounwind`, parameter and
result attributes. `inert`: size and inlining hints, and the unwinding `personality`, as the model
has no unwinding. -/
def funcAttrUses : List (String × AttrUse) :=
  [("sym_name", .modeled), ("function_type", .modeled), ("passthrough", .modeled),
    ("CConv", .inert), ("linkage", .inert), ("visibility_", .inert), ("dso_local", .inert),
    ("unnamed_addr", .inert), ("no_inline", .inert), ("inline_hint", .inert), ("minsize", .inert),
    ("optsize", .inert), ("uwtable_kind", .inert), ("frame_pointer", .inert),
    ("personality", .inert), ("target_cpu", .inert), ("target_features", .inert),
    ("tune_cpu", .inert), ("memory_effects", .ignored), ("will_return", .ignored),
    ("no_unwind", .ignored), ("arg_attrs", .ignored), ("res_attrs", .ignored)]

/-- A function's `passthrough` attributes. `ignored`: those promising progress, termination,
no frees, no recursion and no synchronization. `inert`: code generation's (stack protection and
probing, lazy binding, diagnostics). -/
def passthroughUses : List (String × AttrUse) :=
  [("mustprogress", .ignored), ("willreturn", .ignored), ("nofree", .ignored),
    ("norecurse", .ignored), ("nosync", .ignored), ("nocallback", .ignored),
    ("min-legal-vector-width", .inert), ("no-trapping-math", .inert), ("ssp", .inert),
    ("sspstrong", .inert), ("stack-protector-buffer-size", .inert), ("probe-stack", .inert),
    ("nonlazybind", .inert), ("warn-stack-size", .inert), ("target-cpu", .inert),
    ("target-features", .inert), ("tune-cpu", .inert)]

/-- Parameter and result attributes. `ignored`: those making an argument or result UB or poison
(`noundef`, `nonnull`, `range`, `align`, `dereferenceable`, `noalias`, `sret`) or promising how the
callee uses it (`nocapture`, `nofree`, `readonly`, `writeonly`, `readnone`, `returned`, `writable`,
`dead_on_unwind`, `dead_on_return`). -/
def paramAttrUses : List (String × AttrUse) :=
  [("llvm.zeroext", .inert), ("llvm.signext", .inert), ("llvm.immarg", .inert),
    ("llvm.noundef", .ignored), ("llvm.nonnull", .ignored), ("llvm.range", .ignored),
    ("llvm.align", .ignored), ("llvm.dereferenceable", .ignored),
    ("llvm.dereferenceable_or_null", .ignored), ("llvm.noalias", .ignored),
    ("llvm.nocapture", .ignored), ("llvm.nofree", .ignored), ("llvm.readonly", .ignored),
    ("llvm.writeonly", .ignored), ("llvm.readnone", .ignored), ("llvm.returned", .ignored),
    ("llvm.writable", .ignored), ("llvm.dead_on_unwind", .ignored),
    ("llvm.dead_on_return", .ignored), ("llvm.sret", .ignored)]

/-- A global's attributes; `alignment` is `ignored`, as the model has no addresses. -/
def globalAttrUses : List (String × AttrUse) :=
  [("sym_name", .modeled), ("global_type", .modeled), ("constant", .modeled),
    ("addr_space", .modeled), ("value", .modeled), ("linkage", .inert), ("visibility_", .inert),
    ("dso_local", .inert), ("unnamed_addr", .modeled), ("alignment", .ignored)]

/-- Reject an attribute of `d` that `uses` does not list, and a parameter attribute
`paramAttrUses` does not. -/
def checkAttrs (uses : List (String × AttrUse)) (d : AttrDict) : Except String Unit := do
  let .mk es := d
  for .mk k v in es do
    unless (uses.lookup k).isSome do
      throw s!"unsupported attribute `{k}`"
    if k == "arg_attrs" || k == "res_attrs" then
      let .list ds := v | throw s!"malformed `{k}`"
      for p in ds do
        let .dict (.mk ps) := p | throw s!"malformed `{k}`"
        for .mk k' _ in ps do
          unless (paramAttrUses.lookup k').isSome do
            throw s!"unsupported parameter attribute `{k'}`"

/-- An operation's attributes, checked as `checkAttrs`; operand bundles are rejected. -/
def checkOpAttrs (op : Op) : Except String Unit := do
  checkAttrs (opAttrUses op.name) op.attrs
  if let some b := op.getAttr? "op_bundle_sizes" then
    unless b matches .array _ [] do
      throw "operand bundles are not supported"
  if let some b := op.getAttr? "op_bundle_tags" then
    unless b matches .list [] do
      throw "operand bundles are not supported"

/-- A function's attributes, checked as `checkAttrs`, with its `passthrough` list. -/
def checkFuncAttrs (d : AttrDict) : Except String Unit := do
  checkAttrs funcAttrUses d
  if let some (.list ps) := d.getAttr? "passthrough" then
    for p in ps do
      let k ←
        match p with
        | .str k =>
          pure k
        | .list [.str k, _] =>
          pure k
        | _ =>
          throw "malformed `passthrough`"
      unless (passthroughUses.lookup k).isSome do
        throw s!"unsupported function attribute `{k}`"

/-- A global's attributes: those `globalAttrUses` lists, address space `0`. -/
def checkGlobalAttrs (d : AttrDict) : Except String Unit := do
  checkAttrs globalAttrUses d
  if let some (.int s _) := d.getAttr? "addr_space" then
    unless s == 0 do
      throw "a global must be in address space 0"

/-- The operations a pointer vector (`Ty.array n .ptr`) may meet: none reads it lane-wise but
`getelementptr`. -/
def ptrVecOps : List String :=
  ["llvm.getelementptr", "llvm.load", "llvm.store", "llvm.mlir.poison", "llvm.mlir.undef",
    "llvm.mlir.zero", "llvm.call"]

def instr (E : Env) (op : Op) : Except String PInstr := do
  checkOpAttrs op
  if
      (op.args ++ op.res).any (·.2 matches .vector _ _ (.undefined "llvm.ptr")) &&
        !ptrVecOps.contains op.name then
    throw s!"pointer vectors are supported only by {", ".intercalate ptrVecOps}"
  let args ← op.args.mapM (operand E)
  let res := result E op
  -- an atomic access (`unordered` to `seq_cst`) is a plain one: the model runs one thread
  let checkOrdering : Except String Unit := do
    if let some o := intAttr? op "ordering" then
      unless [0, 1, 2, 4, 5, 6, 7].contains o do
        throw s!"unknown atomic ordering {o}"
  -- the intrinsics' direct calls, as the x86vector dialect spells them
  let name :=
    match op.name, op.getAttr? "callee" with
    | "llvm.call", some (.symbol "x86_avx512_vpermi2var_q_512") =>
      "x86vector.avx512.intr.vpermi2var.q.512"
    | "llvm.call", some (.symbol "x86_avx512_vpmadd52l_uq_512") =>
      "x86vector.avx512.intr.vpmadd52l.uq.512"
    | "llvm.call", some (.symbol "x86_avx512_vpmadd52h_uq_512") =>
      "x86vector.avx512.intr.vpmadd52h.uq.512"
    | name, _ =>
      match name, op.getAttr? "intrin" with
      | "llvm.call_intrinsic", some (.str "llvm.x86.avx512.vpermi2var.q.512") =>
        "x86vector.avx512.intr.vpermi2var.q.512"
      | "llvm.call_intrinsic", some (.str "llvm.x86.avx512.vpmadd52l.uq.512") =>
        "x86vector.avx512.intr.vpmadd52l.uq.512"
      | "llvm.call_intrinsic", some (.str "llvm.x86.avx512.vpmadd52h.uq.512") =>
        "x86vector.avx512.intr.vpmadd52h.uq.512"
      | "llvm.call_intrinsic", some (.str "llvm.x86.avx512.vpmadd52l.uq.256") =>
        "x86vector.avx512.intr.vpmadd52l.uq.512"
      | "llvm.call_intrinsic", some (.str "llvm.x86.avx512.vpmadd52h.uq.256") =>
        "x86vector.avx512.intr.vpmadd52h.uq.512"
      | "llvm.call_intrinsic", some (.str i) => s!"intrinsic {i}"
      | name, _ => name
  match name with
  | "llvm.mlir.zero" =>
    do
      let (dst, t) ← res
      return .const (.zero t) dst
  | "llvm.mlir.constant" =>
    do
      let (dst, t) ← res
      match t, op.getAttr? "value" with
      -- a string's characters are its bytes, as `mlirStrValue` decodes them
      | .array n (.bv 8), some (.str bytes) =>
        unless bytes.length == n do
          throw s!"{bytes.length} bytes for {n} array elements"
        return .const (.bytes n (bytes.toList.foldr (fun c v => 256 * v + c.toNat) 0)) dst
      | .bv w, some (.int v _) =>
        return .const (.bv w v) dst
      | .bv 1, some (.bool b) =>
        return .const (.bv 1 (if b then 1 else 0)) dst
      | .vec l w, some (.dense v _) =>
        match ← denseInts w v with
        | .inr v =>
          return .const (.splat l w v) dst
        | .inl vs =>
          unless vs.length == l do
            throw s!"{vs.length} elements for {l} lanes"
          return .const (.vec l w vs) dst
      | .array n (.bv w), some (.dense v _) =>
        match ← denseInts w v with
        | .inr v =>
          return .const (.arraySplat n w v) dst
        | .inl vs =>
          unless vs.length == n do
            throw s!"{vs.length} elements for {n} array elements"
          return .const (.array n w vs) dst
      | t, _ =>
        throw s!"unsupported constant of type {t.toMLIR}"
  -- `undef` as poison: less defined, so what holds with poison holds for every undef
  | "llvm.mlir.poison" | "llvm.mlir.undef" =>
    do
      let (dst, t) ← res
      return .poison t dst
  | "llvm.and" =>
    arith .and (← res) args
  | "llvm.or" =>
    arith (.or (op.hasAttr "isDisjoint")) (← res) args
  | "llvm.xor" =>
    arith .xor (← res) args
  | "llvm.intr.fshl" | "llvm.intr.fshr" =>
    do
      let (dst, t) ← res
      let op {w} : TernOp (.bv w) (.bv w) (.bv w) (.bv w) :=
        if name == "llvm.intr.fshl" then .fshl else .fshr
      match args with
      | [(a, .bv w), (b, t₂), (c, t₃)] =>
        unless t₂ == .bv w && t₃ == .bv w && t == .bv w do
          throw "the operand and result types must agree"
        return .ternop (op (w := w)) dst a b c
      | [(a, .vec l w), (b, t₂), (c, t₃)] =>
        unless t₂ == .vec l w && t₃ == .vec l w && t == .vec l w do
          throw "the operand and result types must agree"
        return .ternop (.vector (l := l) (op (w := w))) dst a b c
      | _ =>
        throw "expected three integer or vector operands"
  | "llvm.intr.bswap" =>
    do
      let (dst, t) ← res
      match args with
      | [(a, .bv w)] =>
        unless t == .bv w && w % 16 == 0 do
          throw "expected a result of the operand's type, an even number of bytes"
        return .unop (.bswap (w := w)) dst a
      | [(a, .vec l w)] =>
        unless t == .vec l w && w % 16 == 0 do
          throw "expected a result of the operand's type, lanes of an even number of bytes"
        return .unop (.vector (l := l) (.bswap (w := w))) dst a
      | _ =>
        throw "expected one integer or vector operand"
  | "llvm.intr.cttz" =>
    do
      let (dst, t) ← res
      let [(a, .bv w)] := args | throw "expected one integer operand"
      unless t == .bv w do
        throw "expected a result of the operand's type"
      let some (.bool z) := op.getAttr? "is_zero_poison"
        | throw "expected a boolean `is_zero_poison`"
      return .unop (.cttz z (w := w)) dst a
  | "llvm.intr.vector.reduce.or" | "llvm.intr.vector.reduce.and" | "llvm.intr.vector.reduce.add" =>
    do
      let (dst, t) ← res
      let [(v, .vec l w)] := args | throw "expected one vector operand"
      unless t == .bv w do
        throw "the result must be the vector's lane type"
      match name with
      | "llvm.intr.vector.reduce.or" =>
        return .unop (.reduceOr (l := l) (w := w)) dst v
      | "llvm.intr.vector.reduce.and" =>
        return .unop (.reduceAnd (l := l) (w := w)) dst v
      | _ =>
        return .unop (.reduceAdd (l := l) (w := w)) dst v
  | "intrinsic llvm.x86.subborrow.32" | "intrinsic llvm.x86.subborrow.64" =>
    do
      let (dst, t) ← res
      let [(c, .bv 8), (a, .bv w), (b, t₃)] := args
        | throw "expected an `i8` borrow and two integer operands"
      unless t₃ == .bv w && t == .struct [.bv 8, .bv w] && name.endsWith s!".{w}" do
        throw "the operand and result types must agree with the intrinsic's width"
      return .ternop (.subborrow (w := w)) dst c a b
  | "llvm.bitcast" =>
    do
      let (dst, t) ← res
      let [(a, t₁)] := args | throw "expected one operand"
      if t₁ == .ptr || t == .ptr then
        throw "pointer bitcasts are not supported"
      if h : t₁.width = t.width then
        return .unop (.bitcast h) dst a
      else
        throw s!"{t₁.toMLIR} and {t.toMLIR} differ in width"
  | "llvm.add" =>
    arith (.add (← overflowFlags op)) (← res) args
  | "llvm.sub" =>
    arith (.sub (← overflowFlags op)) (← res) args
  | "llvm.mul" =>
    arith (.mul (← overflowFlags op)) (← res) args
  | "llvm.shl" =>
    arith (.shl (← overflowFlags op)) (← res) args
  | "llvm.lshr" =>
    arith (.lshr (op.hasAttr "isExact")) (← res) args
  | "llvm.ashr" =>
    arith (.ashr (op.hasAttr "isExact")) (← res) args
  | "llvm.intr.smin" =>
    arith .smin (← res) args
  | "llvm.intr.smax" =>
    arith .smax (← res) args
  | "llvm.intr.umin" =>
    arith .umin (← res) args
  | "llvm.intr.umax" =>
    arith .umax (← res) args
  | "llvm.intr.usub.sat" =>
    arith .usubSat (← res) args
  | "llvm.intr.abs" =>
    do
      let (dst, t) ← res
      let some (.bool p) := op.getAttr? "is_int_min_poison"
        | throw "expected a boolean `is_int_min_poison`"
      match args with
      | [(a, .bv w)] =>
        unless t == .bv w do
          throw "expected a result of the operand's type"
        return .unop (.abs p (w := w)) dst a
      | [(a, .vec l w)] =>
        unless t == .vec l w do
          throw "expected a result of the operand's type"
        return .unop (.vector (l := l) (.abs p (w := w))) dst a
      | _ =>
        throw "expected one integer or vector operand"
  | "llvm.intr.scmp" | "llvm.intr.ucmp" =>
    do
      let (dst, t) ← res
      let op {w w'} : BinOp (.bv w) (.bv w) (.bv w') :=
        if name == "llvm.intr.scmp" then .scmp else .ucmp
      match args, t with
      | [(a, .bv w), (b, t₂)], .bv w' =>
        unless t₂ == .bv w && 2 ≤ w' do
          throw "expected two operands of one type, and a result of at least 2 bits"
        return .binop (op (w := w) (w' := w')) dst a b
      | [(a, .vec l w), (b, t₂)], .vec l' w' =>
        unless t₂ == .vec l w && l == l' && 2 ≤ w' do
          throw "expected two operands of one type, and as many result lanes of at least 2 bits"
        return .binop (.vector (l := l) (op (w := w) (w' := w'))) dst a b
      | _, _ =>
        throw "expected two integer or vector operands"
  | "llvm.ptrtoaddr" | "llvm.ptrtoint" =>
    do
      let (dst, t) ← res
      let [(p, .ptr)] := args | throw "expected one pointer operand"
      let .bv w := t | throw "expected an integer result"
      -- `ptrtoaddr` gives the address's own width
      if name == "llvm.ptrtoaddr" && w != 64 then
        throw "expected an `i64` result"
      return .ptrtoaddr w dst p
  | "llvm.inline_asm" =>
    do
      let (dst, t) ← res
      let [(a, t₁)] := args | throw "expected one operand"
      let some (.str asm) := op.getAttr? "asm_string" | throw "expected an `asm_string`"
      let some (.str cs) := op.getAttr? "constraints" | throw "expected `constraints`"
      -- an empty asm, its one output tied to its one input: the input
      let clobber (c : String) :=
        c ∈ ["~{dirflag}", "~{fpsr}", "~{flags}", "~{memory}", "~{cc}"]
      unless asm.isEmpty && t₁ == t do
        throw "only an empty asm returning its operand is supported"
      match (cs.splitOn ",").map String.trimAscii with
      | o :: i :: rest =>
        unless o.toString == "=r" && i.toString == "0" && rest.all (clobber ·.toString) do
          throw s!"unsupported constraints \"{cs}\""
      | _ =>
        throw s!"unsupported constraints \"{cs}\""
      return .unop (.copy (t := t)) dst a
  | "llvm.icmp" =>
    do
      let (dst, t) ← res
      let some p := intAttr? op "predicate" | throw "expected a `predicate` attribute"
      let p ← intPred p
      let [(a, t₁), (b, t₂)] := args | throw "expected two operands"
      unless t₁ == t₂ do
        throw "the operand types differ"
      match t₁, t with
      | .bv w, .bv 1 =>
        return .binop (.icmp (w := w) p) dst a b
      | .vec l w, .vec l' 1 =>
        unless l == l' do
          throw "the result has another lane count"
        return .binop (.vector (l := l) (.icmp (w := w) p)) dst a b
      | .ptr, .bv 1 =>
        match p with
        | .eq =>
          return .binop (.ptrcmp false) dst a b
        | .ne =>
          return .binop (.ptrcmp true) dst a b
        | p =>
          return .ptricmp p dst a b
      | t₁, _ =>
        throw s!"unsupported operand type {t₁.toMLIR}"
  | "llvm.select" =>
    do
      let (dst, t) ← res
      let [(c, tCond), (a, t₁), (b, t₂)] := args
        | throw "expected a condition and two operands"
      let op : Nat → RegRef → RegRef → RegRef → PInstr ←
        match tCond, t with
        | .bv 1, _ =>
          pure <| .ternop (.select (τ := t))
        | .vec l 1, .vec l' w =>
          do
            unless l == l' do
              throw "vector condition has wrong lane count"
            pure <| .ternop (.vector (l := l) (.select (τ := .bv w)))
        | _, _ =>
          throw "bad arguments for select"
      unless t₁ == t && t₂ == t do
        throw "the operand and result types must agree"
      return op dst c a b
  | "llvm.trunc" | "llvm.zext" | "llvm.sext" =>
    do
      let (dst, t) ← res
      -- the scalar cast, and the lane count for a vector's
      let (a, w, w', lanes) ←
        match args, t with
        | [(a, .bv w)], .bv w' =>
          pure (a, w, w', none)
        | [(a, .vec l w)], .vec l' w' =>
          unless l == l' do
            throw "the result has another lane count"
          pure (a, w, w', some l)
        | _, _ =>
          throw "expected one integer or vector operand, and a result of its kind"
      let cast : UnOp (.bv w) (.bv w') ←
        if op.name == "llvm.trunc" then
          unless w' < w do
            throw "the result must be narrower"
          pure (.trunc (← overflowFlags op))
        else
          unless w < w' do
            throw "the result must be wider"
          pure (if op.name == "llvm.zext" then .zext (op.hasAttr "nonNeg") else .sext)
      match lanes with
      | none =>
        return .unop cast dst a
      | some l =>
        return .unop (.vector (l := l) cast) dst a
  | "llvm.load" =>
    do
      checkOrdering
      let (dst, t) ← res
      let [(p, .ptr)] := args | throw "expected one pointer operand"
      return .load t dst p
  | "llvm.store" =>
    do
      checkOrdering
      let [(v, t), (p, .ptr)] := args | throw "expected a value and a pointer operand"
      return .store t p v
  | "llvm.intr.masked.load" =>
    do
      let (dst, t) ← res
      let [(p, .ptr), (mask, .vec l 1), (pass, t')] := args
        | throw "expected a pointer, an `i1` mask vector and a passthrough vector"
      let .vec l' w := t | throw "expected a vector result"
      unless l' == l && t' == t && w % 8 == 0 do
        throw "expected the mask's lanes, the passthrough's type and whole-byte lanes"
      return .maskedLoad l w dst p mask pass
  | "llvm.intr.masked.store" =>
    do
      let [(v, .vec l w), (p, .ptr), (mask, t)] := args
        | throw "expected a vector, a pointer and an `i1` mask vector"
      unless t == .vec l 1 && w % 8 == 0 do
        throw "expected the value's lanes in the mask, and whole-byte lanes"
      return .maskedStore l w v p mask
  | "llvm.intr.memset" =>
    do
      let [(dst, .ptr), (val, .bv 8), (len, .bv w)] :=
        args | throw "expected destination pointer, byte and length"
      return .memset w dst val len
  | "llvm.intr.memcpy" | "llvm.intr.memmove" =>
    do
      let [(dst, .ptr), (src, .ptr), (len, .bv w)] :=
        args | throw "expected destination and source pointer, and length"
      if name == "llvm.intr.memcpy" then
        return .memcpy w dst src len
      else
        return .memmove w dst src len
  | "llvm.alloca" =>
    do
      let (dst, t) ← res
      unless t == .ptr do
        throw "expected a pointer result"
      let [(count, _)] := op.args | throw "expected one count operand"
      let isOne :=
        match E.defs.lookup count with
        | some c => c.name == "llvm.mlir.constant" && intAttr? c "value" == some 1
        | none => false
      unless isOne do
        throw s!"the count %{count} must be the constant 1"
      let some (.type et) := op.getAttr? "elem_type" | throw "expected an `elem_type` attribute"
      let dead := op.res.any fun (v, _) => E.started.contains v
      return .alloca dst (← ty et).size dead
  | "llvm.intr.lifetime.start" | "llvm.intr.lifetime.end" =>
    do
      let [(p, .ptr)] := args | throw "expected one pointer operand"
      -- newer LLVM drops `size`: the pointer is an `alloca`, and all of it
      let size ←
        match intAttr? op "size", op.args with
        | some size, _ =>
          pure size
        | none, [(v, _)] =>
          match E.defs.lookup v with
          | some a@{ name := "llvm.alloca", .. } =>
            let some (.type et) := a.getAttr? "elem_type"
              | throw "expected an `elem_type` attribute"
            pure ((← ty et).size : Int)
          | _ =>
            throw s!"without a `size`, %{v} must be an `alloca`"
        | none, _ =>
          throw "expected one pointer operand"
      unless 0 ≤ size do
        throw "negative `size`"
      if op.name == "llvm.intr.lifetime.start" then
        return .lifetimeStart p size.toNat
      else
        return .lifetimeEnd p size.toNat
  | "llvm.intr.assume" =>
    do
      let [(c, .bv 1)] := args | throw "expected one `i1` operand"
      return .assume c
  | "llvm.getelementptr" =>
    do
      let (dst, t) ← res
      -- a pointer vector's lane count
      let lanes? ←
        match t with
        | .ptr =>
          pure none
        | .array n .ptr =>
          pure (some n)
        | _ =>
          throw "expected a pointer or pointer vector result"
      let some (.type et) := op.getAttr? "elem_type" | throw "expected an `elem_type` attribute"
      let flags ← gepFlags op
      let (off, stride, first) ← gepOffset (← ty et) (← arrayInts op "rawConstantIndices")
      -- with flags, the model checks the whole offset, signed below `2 ^ 63`, and the address it
      -- reaches: a negative offset only alone (its address the one LLVM passes through), never
      -- with `nuw` (LLVM's unsigned index times the size)
      if flags != {} then
        unless off.natAbs < 2 ^ 63 && stride.all (· < 2 ^ 63) do
          throw s!"offset {off} or stride out of the signed 64-bit range"
        if first < 0 && (flags.nuw || off != first || stride.isSome) then
          throw s!"negative index part {first} with other parts or `nuw`"
      match lanes?, args, stride with
      | none, [(p, .ptr)], none =>
        return .unop (.gepConst flags off) dst p
      | none, [(p, .ptr), (i, .bv 64)], some stride =>
        unless 0 ≤ off do
          throw s!"negative offset {off} with a dynamic index"
        return .binop (.gepDyn flags off.toNat stride) dst p i
      | some n, [(p, tp)], none =>
        unless tp == .array n .ptr do
          throw "expected a pointer vector of the result's lanes"
        return .unop (.ptrLanes (n := n) (.gepConst flags off)) dst p
      | some n, [(p, tp), (i, ti)], some stride =>
        unless 0 ≤ off do
          throw s!"negative offset {off} with a dynamic index"
        let vb ←
          if tp == .ptr then
            pure false
          else if tp == .array n .ptr then
            pure true
          else
            throw "expected a pointer or a pointer vector of the result's lanes"
        let vi ←
          if ti == .bv 64 then
            pure false
          else if ti == .vec n 64 then
            pure true
          else
            throw "expected an `i64` index, or a vector of the result's lanes of them"
        return .binop (.gepVec flags off.toNat stride (n := n) vb vi) dst p i
      | _, _, _ =>
        throw "expected a pointer, and an `i64` operand for the dynamic index"
  | "llvm.shufflevector" =>
    do
      let (dst, .vec l₂ wₒ) ← res | throw "expected vector output type"
      let [(a, .vec l₁ w), (b, t₂)] := args | throw "expected two vector operands"
      unless t₂ == .vec l₁ w do
        throw "the two operand types must agree"
      unless w == wₒ do
        throw "the input and output element widths must agree"
      let mask ← arrayInts op "mask"
      unless mask.length == l₂ do
        throw s!"the mask has {mask.length} lanes, expected {l₂}"
      let lanes ←
        mask.mapM fun (k : Int) => do
            if k == -1 then
              return none
            unless 0 ≤ k && k < 2 * l₁ do
              throw s!"mask index {k} out of range"
            return some k.toNat
      let idx : Vector (Option (Fin (2 * l₁))) l₂ :=
        Vector.ofFn fun i =>
          (lanes[i]?.getD none).bind fun k => if h : k < 2 * l₁ then some ⟨k, h⟩ else none
      return .binop (.shufflevector (w := w) (l₁ := l₁) (l₂ := l₂) idx) dst a b
  | "llvm.insertelement" =>
    do
      let (dst, t) ← res
      let [(v, .vec l w), (x, t₂), (i, .bv wi)] := args
        | throw "expected a vector, a lane value and an integer index"
      unless t₂ == .bv w && t == .vec l w do
        throw "the lane and result types must match the vector's"
      return .ternop (.insertelement (l := l) (w := w) (wi := wi)) dst v x i
  | "llvm.extractelement" =>
    do
      let (dst, t) ← res
      let [(v, .vec l w), (i, .bv wi)] := args | throw "expected a vector and an integer index"
      unless t == .bv w do
        throw "the result must be the vector's lane type"
      return .binop (.extractelement (l := l) (w := w) (wi := wi)) dst v i
  | "llvm.insertvalue" =>
    do
      let (dst, t) ← res
      let [(c, tCont), (v, tVal)] := args | throw "expected a container and a value"
      unless t == tCont do
        throw "the result type must match the first argument"
      let indices ←
        ((← arrayInts op "position").mapM
            (fun i : Int => do
              let some i := i.toNat? | throw "negative position"
              return i))
      if h : tCont.memberType indices == some tVal then
        do
          return .binop (.insertvalue indices tCont tVal h) dst c v
      else
        do
          throw "the value type must match the containers element"
  | "llvm.extractvalue" =>
    do
      let (dst, t) ← res
      let [(c, tCont)] := args | throw "expected one container"
      let indices ←
        ((← arrayInts op "position").mapM
            (fun i : Int => do
              let some i := i.toNat? | throw "negative position"
              return i))
      -- `extractvalue` reads arrays and structs, not a vector's lanes
      if
          (List.range indices.length).any fun k =>
            tCont.memberType (indices.take k) matches some (.vec ..) then
        throw "the position must not index into a vector"
      if h : tCont.memberType indices == some t then
        return .unop (.extractvalue indices tCont t h) dst c
      else
        throw "the result type must match the container's member"
  | "intrinsic llvm.x86.avx2.pblendvb" =>
    do
      let (dst, t) ← res
      let (l, w, a, b, c) ← vec3 t args
      unless w == 8 do
        throw "expected 8-bit lanes"
      return .ternop (.pblendvb (l := l)) dst a b c
  | "x86vector.avx512.intr.vpermi2var.q.512" =>
    do
      let (dst, t) ← res
      let (l, w, a, b, c) ← vec3 t args
      return .ternop (.vpermi2var (l := l) (w := w)) dst a b c
  | "x86vector.avx512.intr.vpmadd52l.uq.512" =>
    do
      let (dst, t) ← res
      let (l, w, a, b, c) ← vec3 t args
      unless w == 64 do
        throw "expected 64-bit lanes"
      return .ternop (.vpmadd52l (l := l)) dst a b c
  | "x86vector.avx512.intr.vpmadd52h.uq.512" =>
    do
      let (dst, t) ← res
      let (l, w, a, b, c) ← vec3 t args
      unless w == 64 do
        throw "expected 64-bit lanes"
      return .ternop (.vpmadd52h (l := l)) dst a b c
  | "llvm.call" =>
    do
      let some (.symbol callee) := op.getAttr? "callee" | throw "expected a `callee` symbol"
      let rets ← op.res.mapM (valIdx E ·.1)
      let us ← op.res.mapM (ty ·.2)
      return .call callee (args.map (·.2)) us (args.map (·.1)) rets (op.hasAttr "noreturn")
  | "llvm.mlir.addressof" =>
    do
      let some (.symbol global) :=
        op.getAttr? "global_name" | throw "expected a `global_name` symbol"
      let (dst, .ptr) ← res | throw "expected addressof target to be a `ptr`"
      return .addressof global dst
  | name =>
    throw s!"unsupported operation '{name}'"

def exit (E : Env) (blockTys : List (List Ty)) (op : Op) : Except String PExit := do
  checkOpAttrs op
  match op.name, op.successors with
  | "llvm.return", [] =>
    return .ret ((← op.args.mapM (operand E)).map (·.1))
  | "llvm.unreachable", [] =>
    return .unreachable
  | "llvm.br", [s] =>
    return .br (← jump E blockTys s op.args)
  | "llvm.cond_br", [sT, sF] =>
    do
      let [nC, nT, nF] := (← arrayInts op "operandSegmentSizes").map Int.toNat
        | throw "malformed `operandSegmentSizes`"
      let c :: rest := op.args | throw "expected a condition operand"
      unless nC == 1 && rest.length == nT + nF do
        throw "the operands do not match `operandSegmentSizes`"
      let (c, t) ← operand E c
      unless t == .bv 1 do
        throw "the condition must be an `i1`"
      return .condBr c (← jump E blockTys sT (rest.take nT)) (← jump E blockTys sF (rest.drop nT))
  | "llvm.switch", dflt :: cases =>
    do
      let v :: rest := op.args | throw "expected a scrutinee operand"
      let (v, t) ← operand E v
      let .bv w := t | throw s!"the scrutinee must be an integer, found {t.toMLIR}"
      let [_, nDef, _] := (← arrayInts op "operandSegmentSizes").map Int.toNat
        | throw "malformed `operandSegmentSizes`"
      let segs ←
        if cases.isEmpty then
          pure []
        else
          arrayInts op "case_operand_segments"
      let vals ←
        match op.getAttr? "case_values" with
        | none =>
          pure []
        | some (.dense v _) =>
          match ← denseInts w v with
          | .inl vs =>
            pure vs
          | .inr v =>
            pure [v]
        | some _ =>
          throw "`case_values` must be a `dense<…>` attribute"
      unless vals.length == cases.length && segs.length == cases.length do
        throw "`case_values` and `case_operand_segments` do not match the successors"
      let dflt ← jump E blockTys dflt (rest.take nDef)
      let (cs, _) ←
        (vals.zip (cases.zip segs)).foldlM (init := ([], rest.drop nDef))
            fun (cs, pending) (c, s, n) => do
            let j ← jump E blockTys s (pending.take n.toNat)
            return (cs ++ [(c, j)], pending.drop n.toNat)
      return .switch w v dflt cs
  | "llvm.return", _ | "llvm.unreachable", _ | "llvm.br", _ | "llvm.cond_br", _
  | "llvm.switch", _ =>
    throw s!"wrong number of successors"
  | name, _ =>
    throw
        s!"'{name}' is not a terminator; a block must end in llvm.return, llvm.unreachable, \
    llvm.br, llvm.cond_br or llvm.switch"

/-- `f`, with errors prefixed by the operation. -/
def atOp {α : Type} (blk : String) (op : Op) (f : Except String α) : Except String α :=
  f.mapError fun e => s!"^{blk}: {op.render}: {e}"

def isTerminator (name : String) : Bool :=
  name ∈ ["llvm.return", "llvm.unreachable", "llvm.br", "llvm.cond_br", "llvm.switch"]

/-- Operations translated to nothing: `noalias.scope.decl` only declares alias scopes, for alias
analysis, which the model has none of; a `fence` orders memory between threads, and the model
runs one; a `prefetch` has no effect on the program's behavior, not even UB. -/
def isDropped (name : String) : Bool :=
  name == "llvm.intr.experimental.noalias.scope.decl" || name == "llvm.fence" ||
    name == "llvm.intr.prefetch"

end Translate

open Translate in
/-- Check `rgn` and translate it. -/
def Prog.ofRegion (rgn : Region) : Except String Prog := do
  let entry :: _ := rgn.blocks | throw "the region has no blocks"
  -- `Γ.args`: the entry block's arguments, `%argB … %arg(B + N)` for the first's `B`
  let argBase :=
    match entry.args with
    | (v, _) :: _ => ((v.drop 3).toString.toNat?).getD 0
    | [] => 0
  let args ←
    entry.args.zipIdx.mapM fun ((v, t), i) => do
        unless v == s!"arg{argBase + i}" do
          throw s!"the entry block's argument {i} must be %arg{argBase + i}, not %{v}"
        ty t |>.mapError (s!"%{v}: " ++ ·)
  -- `Γ.vals`: every `%K`, block arguments and results, defined exactly once, from the least `K`
  let defs : List TypedSSAVal :=
    (rgn.blocks.drop 1).flatMap (·.args) ++ rgn.blocks.flatMap fun b => b.ops.flatMap (·.res)
  let nums ←
    defs.mapM fun (v, _) => do
        let some i := v.toNat? | throw s!"unsupported value name %{v}; values must be numbered"
        return i
  let valBase := nums.min?.getD 0
  let mut vals : Array (Option Ty) := #[]
  for ((v, t), i) in defs.zip nums do
    let t ← ty t |>.mapError (s!"%{v}: " ++ ·)
    let i := i - valBase
    if vals.size ≤ i then
      vals := vals ++ .replicate (i + 1 - vals.size) none
    if vals[i]!.isSome then
      throw s!"%{v} is defined twice"
    vals := vals.set! i (some t)
  let valTys ←
    vals.toList.zipIdx.mapM fun (t, i) => do
        let some t := t | throw s!"%{valBase + i} is not defined, but a higher value is"
        return t
  let Γ : Ctx := ⟨valTys.length, args, valTys, rfl, argBase, valBase⟩
  let names := rgn.blocks.map (·.name)
  unless names.eraseDups.length == names.length do
    throw "duplicate block name"
  let defs := rgn.blocks.flatMap fun b => b.ops.flatMap fun op => op.res.map fun (v, _) => (v, op)
  let started :=
    rgn.blocks.flatMap fun b =>
      b.ops.filterMap fun op =>
        if op.name == "llvm.intr.lifetime.start" then op.args.getLast?.map (·.1) else none
  let E : Translate.Env := { Γ, blocks := names, defs, started }
  -- block parameters
  let params ←
    (rgn.blocks.drop 1).mapM fun b =>
        b.args.mapM fun (v, _) => do
          let (.val i, _) ← reg E v | throw s!"^{b.name}: argument %{v} must be a value"
          return i
  let params := [] :: params
  let blockTys := params.map fun ps => ps.map fun i => (Γ.vals[i]?).getD (.bv 0)
  -- return types, from the first `llvm.return`
  let tRets ←
    match (rgn.blocks.flatMap (·.ops)).find? (·.name == "llvm.return") with
    | some op =>
      op.args.mapM fun (_, t) => ty t
    | none =>
      pure []
  let blocks ←
    (rgn.blocks.zip params).mapM fun (b, ps) => do
        let some term := b.ops.getLast? | throw s!"^{b.name} is empty"
        let body ←
          b.ops.dropLast.filterMapM fun op =>
              atOp b.name op do
                if isTerminator op.name then
                  throw "a terminator must end its block"
                if isDropped op.name then
                  checkOpAttrs op
                  return none
                return some (← instr E op)
        let exit ←
          atOp b.name term do
              let x ← exit E blockTys term
              if let .ret vs := x then
                let ts ← term.args.mapM fun (_, t) => ty t
                unless ts == tRets do
                  throw
                      s!"returns ({", ".intercalate (ts.map Ty.toMLIR)}), but another llvm.return \
            returns ({", ".intercalate (tRets.map Ty.toMLIR)})"
                let _ := vs
              return x
        return { name := b.name, params := ps, body, exit : PBlock }
  return { Γ, tRets, blocks }

/-! ## Folding constants -/

namespace Translate

/-- A value being folded: undefined (`undef`, `poison`), a constant, a global's address (`off` bytes
into `sym`), or an aggregate's members. -/
inductive Folded
  | undef
  | lit (c : ConstLit)
  | addr (sym : String) (off : Int)
  | agg (t : Ty) (ms : List Folded)

/-- `f`'s members, at array or struct type `t`. -/
def Folded.members (t : Ty) : Folded → Option (List Folded)
  | .undef =>
    match t with
    | .array n _ => some (.replicate n .undef)
    | .struct fs => some (fs.map fun _ => .undef)
    | _ => none
  | .lit (.array _ w vs) => some (vs.map (.lit <| .bv w ·))
  | .lit (.arraySplat n w v) => some (.replicate n (.lit (.bv w v)))
  | .lit (.bytes n v) => some ((List.range n).map fun i => .lit (.bv 8 (v / 256 ^ i % 256)))
  | .lit (.agg _ ms) => some (ms.map .lit)
  | .lit _ => none
  | .addr .. => none
  | .agg _ ms => some ms

/-- `f`, of type `t`, with its member at `path` set to `v`: `insertvalue`. -/
def Folded.insert (v : Folded) (t : Ty) (f : Folded) : (path : List Nat) → Option Folded
  | [] => some v
  | i :: is => do
    let ms ← f.members t
    let m ← v.insert (← t.memberType [i]) (← ms[i]?) is
    return .agg t (ms.set i m)

mutual
/-- `f`'s constant at type `t`, its undefined members (addresses among them) zero, and their paths
and types. -/
def Folded.toLit (t : Ty) : Folded → Option (ConstLit × List (List Nat × Ty))
  | .undef | .addr .. => some (.zero t, [([], t)])
  | .lit c => some (c, [])
  | .agg t ms => do
    let (cs, us) ← toLits t 0 ms
    return (.agg t cs, us)
/-- `toLit` of the members `fs` of an aggregate of type `t`, from member `i`. -/
def Folded.toLits (t : Ty) (i : Nat) : List Folded → Option (List ConstLit × List (List Nat × Ty))
  | [] => some ([], [])
  | f :: fs => do
    let (c, us) ← f.toLit (← t.memberType [i])
    let (cs, us') ← toLits t (i + 1) fs
    return (c :: cs, us.map (fun (p, τ) => (i :: p, τ)) ++ us')
end

/-- `f`'s addresses: each member's path, the global it points into and the byte offset. -/
partial def Folded.addrs : Folded → List (List Nat × String × Int)
  | .addr sym off => [([], sym, off)]
  | .agg _ ms => ms.zipIdx.flatMap fun (m, i) => m.addrs.map fun (p, a) => (i :: p, a)
  | _ => []

end Translate

/-- The bit offset of the member at `path` of a `t`, as `Ty.width` lays it out. -/
def Ty.memberOffset : Ty → List Nat → Option Nat
  | _, [] => some 0
  | .array _ t, i :: is => return i * t.stride + (← t.memberOffset is)
  | .struct fs, i :: is => do
    let t ← fs[i]?
    return Ty.fieldOffset 0 i fs + (← t.memberOffset is)
  | _, _ => none

open Translate in
/-- The value `p`'s one block returns, folded, and its type, if the block builds it from constants,
`undef`s, addresses (`addressof`, a constant `getelementptr` off one) and `insertvalue`s alone. -/
def Prog.folded? (p : Prog) : Option (Folded × Ty) := do
  let [b] := p.blocks | none
  let .ret [.val r] := b.exit | none
  -- registers start undefined, as `Env.init` starts them poison
  let vals ←
    b.body.foldlM (init := Array.replicate p.Γ.n Folded.undef) fun vals i => do
        match i with
        | .const c d =>
          return vals.set! d (.lit c)
        | .poison _ d =>
          return vals.set! d .undef
        | .binop (.insertvalue is t _ _) d (.val a) (.val v) =>
          return vals.set! d (← (← vals[v]?).insert t (← vals[a]?) is)
        | .addressof g d =>
          return vals.set! d (.addr g 0)
        -- a constant offset: as `gep` takes it, a negative one with flags (or one past `2 ^ 63`)
        -- left undefined, less defined than LLVM
        | .unop (.gepConst f k) d (.val a) =>
          let .addr g o ← vals[a]? | none
          if (0 ≤ o && 0 ≤ k && o + k < 2 ^ 63) || f == {} then return vals.set! d (.addr g (o + k))
          else return vals.set! d .undef
        | _ =>
          none
  return (← vals[r]?, ← p.Γ.vals[r]?)

open Translate in
/-- The constant `p` returns (`Prog.folded?`), if it is not all undefined: its undefined members
zero, addresses among them, with their paths and types. -/
def Prog.constant? (p : Prog) : Option (ConstLit × List (List Nat × Ty)) := do
  let (f, t) ← p.folded?
  let (c, us) ← f.toLit t
  guard (!us.any (·.1.isEmpty))
  return (c, us)

open Translate in
/-- The pointer members of the value `p` returns (`Prog.folded?`): each one's bit offset, the global
it points into and the byte offset into it. -/
def Prog.constantPtrs (p : Prog) : List (Nat × String × Int) :=
  match p.folded? with
  | some (f, t) => f.addrs.filterMap fun (path, sym, off) => (t.memberOffset path).map (·, sym, off)
  | none => []

/-! ## Building the `Func` -/

/-- A callee's semantics, typically `g.call` for a `g : Func`. -/
abbrev Callee :=
  Σ (ts us : List Ty), Vals ts → EffectM (Vals us)

/-- The library function `name` as a callee: an unbound call of one, of its signature. -/
def libCall? : String → Option Callee
  | "memcmp" => some ⟨_, _, Operation.memcmp⟩
  | "bcmp" => some ⟨_, _, Operation.bcmp⟩
  | "explicit_bzero" => some ⟨_, _, Operation.explicitBzero⟩
  | "__explicit_bzero_chk" => some ⟨_, _, Operation.explicitBzeroChk⟩
  | "memset_explicit" => some ⟨_, _, Operation.memsetExplicit⟩
  | _ => none

mutual
/-- `t`'s all-zero raw value, with null pointers. -/
def Ty.zeroRaw : (t : Ty) → ⟦t⟧ᵣ
  | .bv w => 0#w
  | .ptr => Pointer.null
  | .vec l w => Vector.replicate l 0#w
  | .array n t => Vector.replicate n t.zeroRaw
  | .struct fs => Ty.zeroRawFields fs
def Ty.zeroRawFields : (fs : List Ty) → Ty.denoteFieldsRaw fs
  | [] => ()
  | [t] => t.zeroRaw
  | t :: t' :: ts => (t.zeroRaw, Ty.zeroRawFields (t' :: ts))
end

/-- `v`, a value of `c`, at type `t`; zero if `c` has another type. -/
def ConstLit.castTo (c : ConstLit) (v : ⟦c.ty⟧ᵣ) (t : Ty) : ⟦t⟧ᵣ :=
  if h : c.ty = t then h ▸ v else t.zeroRaw

mutual
def ConstLit.value : (c : ConstLit) → ⟦c.ty⟧ᵣ
  | .bv w v => BitVec.ofInt w v
  | .vec l w vs => Vector.ofFn fun i : Fin l => BitVec.ofInt w (vs[i]?.getD 0)
  | .splat l w v => Vector.replicate l (BitVec.ofInt w v)
  | .array n w vs => Vector.ofFn fun i : Fin n => BitVec.ofInt w (vs[i]?.getD 0)
  | .arraySplat n w v => Vector.replicate n (BitVec.ofInt w v)
  | .bytes n v => Vector.ofFn fun i : Fin n => BitVec.ofNat 8 (v >>> (8 * i.1))
  | .null => Pointer.null
  | .agg (.array _ t) ms => Vector.ofFn fun i => (ConstLit.valuesAt t ms).getD i t.zeroRaw
  | .agg (.struct fs) ms => ConstLit.fieldsAt fs ms
  | .agg t _ => t.zeroRaw
/-- `cs`' values at type `t`. -/
def ConstLit.valuesAt (t : Ty) : List ConstLit → List ⟦t⟧ᵣ
  | [] => []
  | c :: cs => c.castTo c.value t :: ConstLit.valuesAt t cs
/-- A struct of fields `fs` from `cs`' values; zero where `cs` runs out. -/
def ConstLit.fieldsAt : (fs : List Ty) → List ConstLit → Ty.denoteFieldsRaw fs
  | [f], c :: _ => c.castTo c.value f
  | f :: f' :: fs, c :: cs => (c.castTo c.value f, ConstLit.fieldsAt (f' :: fs) cs)
  | fs, _ => Ty.zeroRawFields fs
end

namespace Prog

variable (Γ : Ctx)

def mkReg (t : Ty) : RegRef → Except String (Reg Γ t)
  | .arg i =>
    if h : i < Γ.args.length then
      if h' : Γ.args[i] = t then return .arg ⟨i, h⟩ h'
      else throw s!"%arg{Γ.argBase + i}: type mismatch"
    else throw s!"%arg{Γ.argBase + i} out of range"
  | .val i =>
    if h : i < Γ.n then
      if h' : Γ.ty ⟨i, h⟩ = t then return .val ⟨i, h⟩ h'
      else throw s!"%{Γ.valBase + i}: type mismatch"
    else throw s!"%{Γ.valBase + i} out of range"

def mkDst (t : Ty) (i : Nat) : Except String (Dst Γ t) :=
  if h : i < Γ.n then
    if h' : Γ.ty ⟨i, h⟩ = t then return ⟨⟨i, h⟩, h'⟩ else throw s!"%{Γ.valBase + i}: type mismatch"
  else throw s!"%{Γ.valBase + i} out of range"

def mkRegs : (ts : List Ty) → List RegRef → Except String (Regs Γ ts)
  | [], [] => return .nil
  | t :: ts, r :: rs => return .cons (← mkReg Γ t r) (← mkRegs ts rs)
  | _, _ => throw "wrong number of registers"

def mkDsts : (ts : List Ty) → List Nat → Except String (Dsts Γ ts)
  | [], [] => return .nil
  | t :: ts, d :: ds => return .cons (← mkDst Γ t d) (← mkDsts ts ds)
  | _, _ => throw "wrong number of registers"

def mkInstr (callees : String → Option Callee) : PInstr → Except String (Instr Γ)
  | .const c d => return .const c.value (← mkDst Γ _ d)
  | .poison t d => return .poison (← mkDst Γ t d)
  | .unop op d a => return .unop op (← mkDst Γ _ d) (← mkReg Γ _ a)
  | .binop op d a b => return .binop op (← mkDst Γ _ d) (← mkReg Γ _ a) (← mkReg Γ _ b)
  | .ternop op d a b c =>
    return .ternop op (← mkDst Γ _ d) (← mkReg Γ _ a) (← mkReg Γ _ b) (← mkReg Γ _ c)
  | .load t d p => return .load (← mkDst Γ t d) (← mkReg Γ .ptr p)
  | .store t p v => return .store (← mkReg Γ .ptr p) (← mkReg Γ t v)
  | .maskedLoad l w d p m pt =>
    return .maskedLoad (← mkDst Γ (.vec l w) d) (← mkReg Γ .ptr p) (← mkReg Γ (.vec l 1) m)
      (← mkReg Γ (.vec l w) pt)
  | .maskedStore l w v p m =>
    return .maskedStore (← mkReg Γ (.vec l w) v) (← mkReg Γ .ptr p) (← mkReg Γ (.vec l 1) m)
  | .memset w dst v l =>
    return .memset (← mkReg Γ .ptr dst) (← mkReg Γ (.bv 8) v) (← mkReg Γ (.bv w) l)
  | .memcpy w dst src l =>
    return .memcpy (← mkReg Γ .ptr dst) (← mkReg Γ .ptr src) (← mkReg Γ (.bv w) l)
  | .memmove w dst src l =>
    return .memmove (← mkReg Γ .ptr dst) (← mkReg Γ .ptr src) (← mkReg Γ (.bv w) l)
  | .ptrtoaddr w d p => return .ptrtoaddr (← mkDst Γ (.bv w) d) (← mkReg Γ .ptr p)
  | .ptricmp pred d a b =>
    return .ptricmp pred (← mkDst Γ (.bv 1) d) (← mkReg Γ .ptr a) (← mkReg Γ .ptr b)
  | .alloca d n dead => return .alloca (← mkDst Γ .ptr d) n dead
  | .lifetimeStart p n => return .lifetimeStart (← mkReg Γ .ptr p) n
  | .lifetimeEnd p n => return .lifetimeEnd (← mkReg Γ .ptr p) n
  | .assume c => return .assume (← mkReg Γ (.bv 1) c)
  | .call name ts us args rets noret => do
    let some ⟨ts', us', f⟩ :=
        if noret then some ⟨ts, us, Operation.noreturn⟩
        else (callees name).orElse fun _ => libCall? name
      | throw s!"no callee bound for @{name}"
    if h : ts' = ts ∧ us' = us then
      return .call (h.1 ▸ h.2 ▸ f) (← mkRegs Γ ts args) (← mkDsts Γ us rets)
    else
      throw s!"@{name} does not have the type the call site needs"
  | .addressof name dst => return .addressof name (← mkDst Γ .ptr dst)

variable {n : Nat} (blockTys : Fin n → List Ty)

def mkJump (j : PJump) : Except String (Jump Γ blockTys) := do
  if h : j.target < n then
    return ⟨⟨j.target, h⟩, ← mkRegs Γ _ j.args⟩
  else
    throw s!"block {j.target} out of range"

def mkExit (tRets : List Ty) : PExit → Except String (Exit Γ tRets blockTys)
  | .ret vs => return .ret (← mkRegs Γ tRets vs)
  | .unreachable => return .unreachable
  | .br j => return .br (← mkJump Γ blockTys j)
  | .condBr c t f =>
    return .condBr (← mkReg Γ (.bv 1) c) (← mkJump Γ blockTys t) (← mkJump Γ blockTys f)
  | .switch w v d cs => do
    let cs ← cs.mapM fun (c, j) => return ((BitVec.ofInt w c : ⟦Ty.bv w⟧ᵣ), ← mkJump Γ blockTys j)
    return .switch (← mkReg Γ (.bv w) v) (← mkJump Γ blockTys d) cs

end Prog

/-- The `Func` of `p`, calling `callees name` for `@name`, its globals `globals`. -/
def Prog.toFunc (p : Prog) (callees : String → Option Callee := fun _ => none)
    (globals : List Global := []) : Except String Func := do
  let n := p.blocks.length
  let params ←
    p.blocks.toArray.mapM fun b => do
        let ts := b.params.map fun i => (p.Γ.vals[i]?).getD (.bv 0)
        return (⟨ts, ← mkDsts p.Γ ts b.params⟩ : Σ ts, Dsts p.Γ ts)
  let blockTys (k : Fin n) : List Ty := (params[k.val]?.getD ⟨[], .nil⟩).1
  let blockParams (k : Fin n) : Dsts p.Γ (blockTys k) := (params[k.val]?.getD ⟨[], .nil⟩).2
  if hn : n > 0 then
    if hentry : blockTys ⟨0, hn⟩ = [] then
      let blocks ←
        p.blocks.toArray.mapM fun b => do
            return ({
                  body := ← b.body.mapM (mkInstr p.Γ callees)
                  exit := ← mkExit p.Γ blockTys p.tRets b.exit } :
                BasicBlock p.Γ p.tRets blockTys)
      if hs : blocks.size = n then
        return { Γ := p.Γ, tRets := p.tRets, n, blockTys, blockParams, hhasBlock := hn, hentry,
                 blocks := fun k => blocks[k.val], globals }
      else
        throw "internal: block count"
    else
      throw "the entry block has parameters"
  else
    throw "no blocks"

/-- Translate `reg` to a `Func`. -/
def translate (reg : Region) (callees : String → Option Callee := fun _ => none)
    (globals : List Global := []) : Except String Func := do
  (← Prog.ofRegion reg).toFunc callees globals

end

end MLIR
