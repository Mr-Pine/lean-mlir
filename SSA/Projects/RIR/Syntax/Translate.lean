module

public import SSA.Projects.RIR.Syntax.AST
public import SSA.Projects.RIR.Func

/-!
# MLIR AST to `Func`

`Prog.ofRegion` checks a parsed region and translates it to a `Prog`: the function's instructions
with registers as indices and every type resolved. `Prog.toFunc` builds the `Func`, and `mlir_def`
(`Syntax/Elab.lean`) builds the terms of a hand lift from the same `Prog`. `Prog.constant?` folds a
region that only builds a constant, as a global's initializer does.

Registers: `%argK` is `.arg K` and `%K` is `.val K`; a block's arguments are values, numbered as
MLIR numbers them. The translation is trusted, and guarded by tests.
-/

namespace LeanMLIR.RIR

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
  | null
  /-- An array's elements or a struct's fields, of type `t`. -/
  | agg (t : Ty) (ms : List ConstLit)
  deriving Repr

def ConstLit.ty : ConstLit → Ty
  | .bv w _ => .bv w
  | .vec l w _ | .splat l w _ => .vec l w
  | .array n w _ | .arraySplat n w _ => .array n (.bv w)
  | .null => .ptr
  | .agg t _ => t

/-- An `Instr` with registers as indices; `dst` and `rets` index `Γ.vals`. -/
inductive PInstr
  | const (c : ConstLit) (dst : Nat)
  | poison (t : Ty) (dst : Nat)
  | unop {t₁ t : Ty} (op : UnOp t₁ t) (dst : Nat) (a : RegRef)
  | binop {t₁ t₂ t : Ty} (op : BinOp t₁ t₂ t) (dst : Nat) (a b : RegRef)
  | ternop {t₁ t₂ t₃ t : Ty} (op : TernOp t₁ t₂ t₃ t) (dst : Nat) (a b c : RegRef)
  | load (t : Ty) (dst : Nat) (p : RegRef)
  | store (t : Ty) (p v : RegRef)
  | memset (w : Nat) (p v l : RegRef)
  | memcpy (w : Nat) (dst src l : RegRef)
  | alloca (dst : Nat) (bytes : Nat)
  | lifetimeStart (p : RegRef) (bytes : Nat)
  | lifetimeEnd (p : RegRef) (bytes : Nat)
  /-- A call of the symbol `callee`, from argument types `ts` to result types `us`. -/
  | call (callee : String) (ts us : List Ty) (args : List RegRef) (rets : List Nat)
  | addressof (global : String) (dst : Nat)

/-- A jump to block `target` with arguments `args`. -/
structure PJump where
  target : Nat
  args : List RegRef

inductive PExit
  | ret (vs : List RegRef)
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
/-- Decode one type from the head of `cs`. -/
partial def parseTy : List Char → Option (Ty × List Char)
  | 'i' :: cs => (takeNat cs).map fun (w, rest) => (.bv w, rest)
  | 'p' :: 't' :: 'r' :: cs => some (.ptr, cs)
  | 'a' :: 'r' :: 'r' :: 'a' :: 'y' :: '<' :: cs => do
    let (n, cs) ← takeNat (dropWs cs)
    let 'x' :: cs := dropWs cs | none
    let (t, cs) ← parseTy (dropWs cs)
    let '>' :: cs := dropWs cs | none
    return (.array n t, cs)
  | 'v' :: 'e' :: 'c' :: 't' :: 'o' :: 'r' :: '<' :: cs => do
    let (n, cs) ← takeNat (dropWs cs)
    let 'x' :: cs := dropWs cs | none
    let (t, cs) ← parseTy (dropWs cs)
    let .bv w := t | none
    let '>' :: cs := dropWs cs | none
    return (.vec n w, cs)
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
    let '(' :: cs := cs | none
    let (fields, cs) ← parseTyFields (dropWs cs) []
    let '>' :: cs := dropWs cs | none
    return (.struct fields, cs)
  | _ => none
/-- `t (, t)* )` -/
partial def parseTyFields (cs : List Char) (acc : List Ty) : Option (List Ty × List Char) := do
  let (t, cs) ← parseTy cs
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
  | .undefined "llvm.ptr" => return .ptr
  | t@(.undefined s) =>
    match parseTy ((s.drop "llvm.".length).toString.toList) with
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

/-- The byte offset of `getelementptr`'s constant indices over `t`, and for its one dynamic index
(`-2147483648`) the stride it steps by: the size of what it indexes. -/
def gepOffset (t : Ty) : List Int → Except String (Nat × Option Nat)
  | [] => return (0, none)
  | k₀ :: ks => do
    let dynamic := -2147483648
    let natIdx (k : Int) : Except String Nat := do
      unless 0 ≤ k do
        throw s!"negative index {k}"
      return k.toNat
    -- the first index steps over whole `t`s, the others into `t`
    let (off, stride) ←
      if k₀ == dynamic then
        pure (0, some t.size)
      else
        pure ((← natIdx k₀) * t.size, none)
    let (off, stride, _) ←
      ks.foldlM (init := (off, stride, t)) fun (off, stride, t) k => do
          if k == dynamic then
            if stride.isSome then
              throw "only one dynamic index is supported"
            let .array _ et := t | throw "a dynamic index must index an array"
            return (off, some et.size, et)
          let (step, t) ← Ty.index (← natIdx k) t
          return (off + step, stride, t)
    return (off, stride)

/-! ## Attributes -/

def intAttr? (op : Op) (k : String) : Option Int :=
  match op.getAttr? k with
  | some (.int v _) => some v
  | _ => none

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

/-- The integers of a `dense<…>` value: one per lane, or one for all. -/
def denseInts : AttrValue → Except String (List Int ⊕ Int)
  | .int v _ => return .inr v
  | .list vs =>
    .inl <$>
      vs.mapM fun
        | .int v _ => pure v
        | _ => throw "`dense<…>` elements must be integers"
  | _ => throw "expected integers inside `dense<…>`"

/-! ## Registers and blocks -/

/-- What the translation reads everywhere: the context and the block names. -/
structure Env where
  Γ : Ctx
  blocks : List String
  /-- The defining op of each value, for `alloca`'s count. -/
  defs : List (String × Op)

def reg (E : Env) (v : SSAVal) : Except String (RegRef × Ty) := do
  if v.startsWith "arg" then
    if let some i := (v.drop 3).toString.toNat? then
      let some t := E.Γ.args[i]? | throw s!"%{v} is not an argument of the function"
      return (.arg i, t)
  let some i := v.toNat? | throw s!"unsupported value name %{v}"
  let some t := E.Γ.vals[i]? | throw s!"%{v} is not defined"
  return (.val i, t)

/-- An operand, checked against its type at the use. -/
def operand (E : Env) (v : TypedSSAVal) : Except String (RegRef × Ty) := do
  let (r, t) ← reg E v.1
  let t' ← ty v.2
  unless t == t' do
    throw s!"%{v.1} has type {t.toMLIR} but is used at {t'.toMLIR}"
  return (r, t)

def result (op : Op) : Except String (Nat × Ty) := do
  let [(v, t)] := op.res | throw s!"expected one result, found {op.res.length}"
  let some i := v.toNat? | throw s!"unsupported result name %{v}"
  return (i, ← ty t)

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

def instr (E : Env) (op : Op) : Except String PInstr := do
  let args ← op.args.mapM (operand E)
  let res := result op
  let checkNotAtomic : Except String Unit := do
    if let some o := intAttr? op "ordering" then
      unless o == 0 do
        throw "atomic accesses are not supported"
  -- the intrinsics' direct calls, as the x86vector dialect spells them
  let name :=
    match op.name, op.getAttr? "callee" with
    | "llvm.call", some (.symbol "x86_avx512_vpermi2var_q_512") =>
      "x86vector.avx512.intr.vpermi2var.q.512"
    | "llvm.call", some (.symbol "x86_avx512_vpmadd52l_uq_512") =>
      "x86vector.avx512.intr.vpmadd52l.uq.512"
    | "llvm.call", some (.symbol "x86_avx512_vpmadd52h_uq_512") =>
      "x86vector.avx512.intr.vpmadd52h.uq.512"
    | name, _ => name
  match name with
  | "llvm.mlir.zero" =>
    do
      let (dst, t) ← res
      match t with
      | .ptr =>
        return .const .null dst
      | .bv w =>
        return .const (.bv w 0) dst
      | .vec l w =>
        return .const (.splat l w 0) dst
      | .array n (.bv w) =>
        return .const (.arraySplat n w 0) dst
      | t =>
        throw s!"unsupported zero of type {t.toMLIR}"
  | "llvm.mlir.constant" =>
    do
      let (dst, t) ← res
      match t, op.getAttr? "value" with
      | .bv w, some (.int v _) =>
        return .const (.bv w v) dst
      | .bv 1, some (.bool b) =>
        return .const (.bv 1 (if b then 1 else 0)) dst
      | .vec l w, some (.dense v _) =>
        match ← denseInts v with
        | .inr v =>
          return .const (.splat l w v) dst
        | .inl vs =>
          unless vs.length == l do
            throw s!"{vs.length} elements for {l} lanes"
          return .const (.vec l w vs) dst
      | .array n (.bv w), some (.dense v _) =>
        match ← denseInts v with
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
      let [(a, .bv w), (b, t₂), (c, t₃)] := args | throw "expected three integer operands"
      unless t₂ == .bv w && t₃ == .bv w && t == .bv w do
        throw "the operand and result types must agree"
      if name == "llvm.intr.fshl" then
        return .ternop (.fshl (w := w)) dst a b c
      else
        return .ternop (.fshr (w := w)) dst a b c
  | "llvm.intr.bswap" =>
    do
      let (dst, t) ← res
      let [(a, .bv w)] := args | throw "expected one integer operand"
      unless t == .bv w && w % 8 == 0 do
        throw "expected a result of the operand's type, a whole number of bytes"
      return .unop (.bswap (w := w)) dst a
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
        | _ =>
          throw "pointers compare only by `eq` and `ne`"
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
      let [(a, .bv w)] := args | throw "expected one integer operand"
      let .bv w' := t | throw "expected an integer result"
      if op.name == "llvm.trunc" then
        unless w' < w do
          throw "the result must be narrower"
        return .unop (.trunc (w := w) (w' := w') (← overflowFlags op)) dst a
      else
        unless w < w' do
          throw "the result must be wider"
        if op.name == "llvm.zext" then
          return .unop (.zext (w := w) (w' := w') (op.hasAttr "nonNeg")) dst a
        else
          return .unop (.sext (w := w) (w' := w')) dst a
  | "llvm.load" =>
    do
      checkNotAtomic
      let (dst, t) ← res
      let [(p, .ptr)] := args | throw "expected one pointer operand"
      return .load t dst p
  | "llvm.store" =>
    do
      checkNotAtomic
      let [(v, t), (p, .ptr)] := args | throw "expected a value and a pointer operand"
      return .store t p v
  | "llvm.intr.memset" =>
    do
      checkNotAtomic
      let [(dst, .ptr), (val, .bv 8), (len, .bv w)] :=
        args | throw "expected destination pointer, byte and length"
      return .memset w dst val len
  | "llvm.intr.memcpy" =>
    do
      checkNotAtomic
      let [(dst, .ptr), (src, .ptr), (len, .bv w)] :=
        args | throw "expected destination and source pointer, and length"
      return .memcpy w dst src len
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
      return .alloca dst (← ty et).size
  | "llvm.intr.lifetime.start" | "llvm.intr.lifetime.end" =>
    do
      let [(p, .ptr)] := args | throw "expected one pointer operand"
      let some size := intAttr? op "size" | throw "expected a `size` attribute"
      unless 0 ≤ size do
        throw "negative `size`"
      if op.name == "llvm.intr.lifetime.start" then
        return .lifetimeStart p size.toNat
      else
        return .lifetimeEnd p size.toNat
  | "llvm.getelementptr" =>
    do
      let (dst, t) ← res
      unless t == .ptr do
        throw "expected a pointer result"
      let some (.type et) := op.getAttr? "elem_type" | throw "expected an `elem_type` attribute"
      match args, ← gepOffset (← ty et) (← arrayInts op "rawConstantIndices") with
      | [(p, .ptr)], (off, none) =>
        return .unop (.gepConst off) dst p
      | [(p, .ptr), (i, .bv 64)], (off, some stride) =>
        return .binop (.gepDyn off stride) dst p i
      | _, _ =>
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
      let rets ←
        op.res.mapM fun (v, _) => do
            let some i := v.toNat? | throw s!"unsupported result name %{v}"
            return i
      let us ← op.res.mapM (ty ·.2)
      return .call callee (args.map (·.2)) us (args.map (·.1)) rets
  | "llvm.mlir.addressof" =>
    do
      let some (.symbol global) :=
        op.getAttr? "global_name" | throw "expected a `global_name` symbol"
      let (dst, .ptr) ← res | throw "expected addressof target to be a `ptr`"
      return .addressof global dst
  | name =>
    throw s!"unsupported operation '{name}'"

def exit (E : Env) (blockTys : List (List Ty)) (op : Op) : Except String PExit := do
  match op.name, op.successors with
  | "llvm.return", [] =>
    return .ret ((← op.args.mapM (operand E)).map (·.1))
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
          match ← denseInts v with
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
  | "llvm.return", _ | "llvm.br", _ | "llvm.cond_br", _ | "llvm.switch", _ =>
    throw s!"wrong number of successors"
  | name, _ =>
    throw
        s!"'{name}' is not a terminator; a block must end in llvm.return, llvm.br, \
    llvm.cond_br or llvm.switch"

/-- `f`, with errors prefixed by the operation. -/
def atOp {α : Type} (blk : String) (op : Op) (f : Except String α) : Except String α :=
  f.mapError fun e => s!"^{blk}: {op.render}: {e}"

def isTerminator (name : String) : Bool :=
  name ∈ ["llvm.return", "llvm.br", "llvm.cond_br", "llvm.switch"]

end Translate

open Translate in
/-- Check `rgn` and translate it. -/
def Prog.ofRegion (rgn : Region) : Except String Prog := do
  let entry :: _ := rgn.blocks | throw "the region has no blocks"
  -- `Γ.args`: the entry block's arguments, `%arg0 … %argN`
  let args ←
    entry.args.zipIdx.mapM fun ((v, t), i) => do
        unless v == s!"arg{i}" do
          throw s!"the entry block's argument {i} must be %arg{i}, not %{v}"
        ty t |>.mapError (s!"%{v}: " ++ ·)
  -- `Γ.vals`: every `%K`, block arguments and results, defined exactly once
  let defs : List TypedSSAVal :=
    (rgn.blocks.drop 1).flatMap (·.args) ++ rgn.blocks.flatMap fun b => b.ops.flatMap (·.res)
  let mut vals : Array (Option Ty) := #[]
  for (v, t) in defs do
    let some i := v.toNat? | throw s!"unsupported value name %{v}; values must be %0, %1, …"
    let t ← ty t |>.mapError (s!"%{v}: " ++ ·)
    if vals.size ≤ i then
      vals := vals ++ .replicate (i + 1 - vals.size) none
    if vals[i]!.isSome then
      throw s!"%{i} is defined twice"
    vals := vals.set! i (some t)
  let valTys ←
    vals.toList.zipIdx.mapM fun (t, i) => do
        let some t := t | throw s!"%{i} is not defined, but a higher value is"
        return t
  let Γ : Ctx := ⟨valTys.length, args, valTys, rfl⟩
  let names := rgn.blocks.map (·.name)
  unless names.eraseDups.length == names.length do
    throw "duplicate block name"
  let defs := rgn.blocks.flatMap fun b => b.ops.flatMap fun op => op.res.map fun (v, _) => (v, op)
  let E : Env := { Γ, blocks := names, defs }
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
          b.ops.dropLast.mapM fun op =>
              atOp b.name op do
                if isTerminator op.name then
                  throw "a terminator must end its block"
                instr E op
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

/-- A value being folded: undefined (`undef`, `poison`), a constant, or an aggregate's members. -/
inductive Folded
  | undef
  | lit (c : ConstLit)
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
  | .lit _ => none
  | .agg _ ms => some ms

/-- `f`, of type `t`, with its member at `path` set to `v`: `insertvalue`. -/
def Folded.insert (v : Folded) (t : Ty) (f : Folded) : (path : List Nat) → Option Folded
  | [] => some v
  | i :: is => do
    let ms ← f.members t
    let m ← v.insert (← t.memberType [i]) (← ms[i]?) is
    return .agg t (ms.set i m)

mutual
/-- `f`'s constant, if no member is undefined. -/
def Folded.toLit : Folded → Option ConstLit
  | .undef => none
  | .lit c => some c
  | .agg t ms => .agg t <$> toLits ms
def Folded.toLits : List Folded → Option (List ConstLit)
  | [] => some []
  | f :: fs => return (← f.toLit) :: (← toLits fs)
end

end Translate

open Translate in
/-- The constant `p` returns, if its one block builds it from constants, `undef`s and
`insertvalue`s alone and leaves no member undefined. -/
def Prog.constant? (p : Prog) : Option ConstLit := do
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
        | _ =>
          none
  (← vals[r]?).toLit

/-! ## Building the `Func` -/

/-- A global's initializer, typically `G.value` for a `G : GlobalInitializer`. -/
abbrev Global :=
  Σ (t : Ty), EffectM ⟦t⟧

/-- A callee's semantics, typically `g.call` for a `g : Func`. -/
abbrev Callee :=
  Σ (ts us : List Ty), Vals ts → EffectM (Vals us)

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
      if h' : Γ.args[i] = t then return .arg ⟨i, h⟩ h' else throw s!"%arg{i}: type mismatch"
    else throw s!"%arg{i} out of range"
  | .val i =>
    if h : i < Γ.n then
      if h' : Γ.ty ⟨i, h⟩ = t then return .val ⟨i, h⟩ h' else throw s!"%{i}: type mismatch"
    else throw s!"%{i} out of range"

def mkDst (t : Ty) (i : Nat) : Except String (Dst Γ t) :=
  if h : i < Γ.n then
    if h' : Γ.ty ⟨i, h⟩ = t then return ⟨⟨i, h⟩, h'⟩ else throw s!"%{i}: type mismatch"
  else throw s!"%{i} out of range"

def mkRegs : (ts : List Ty) → List RegRef → Except String (Regs Γ ts)
  | [], [] => return .nil
  | t :: ts, r :: rs => return .cons (← mkReg Γ t r) (← mkRegs ts rs)
  | _, _ => throw "wrong number of registers"

def mkDsts : (ts : List Ty) → List Nat → Except String (Dsts Γ ts)
  | [], [] => return .nil
  | t :: ts, d :: ds => return .cons (← mkDst Γ t d) (← mkDsts ts ds)
  | _, _ => throw "wrong number of registers"

def mkInstr (callees : String → Option Callee) (globals : String → Option Global) :
    PInstr → Except String (Instr Γ)
  | .const c d => return .const c.value (← mkDst Γ _ d)
  | .poison t d => return .poison (← mkDst Γ t d)
  | .unop op d a => return .unop op (← mkDst Γ _ d) (← mkReg Γ _ a)
  | .binop op d a b => return .binop op (← mkDst Γ _ d) (← mkReg Γ _ a) (← mkReg Γ _ b)
  | .ternop op d a b c =>
    return .ternop op (← mkDst Γ _ d) (← mkReg Γ _ a) (← mkReg Γ _ b) (← mkReg Γ _ c)
  | .load t d p => return .load (← mkDst Γ t d) (← mkReg Γ .ptr p)
  | .store t p v => return .store (← mkReg Γ .ptr p) (← mkReg Γ t v)
  | .memset w dst v l =>
    return .memset (← mkReg Γ .ptr dst) (← mkReg Γ (.bv 8) v) (← mkReg Γ (.bv w) l)
  | .memcpy w dst src l =>
    return .memcpy (← mkReg Γ .ptr dst) (← mkReg Γ .ptr src) (← mkReg Γ (.bv w) l)
  | .alloca d n => return .alloca (← mkDst Γ .ptr d) n
  | .lifetimeStart p n => return .lifetimeStart (← mkReg Γ .ptr p) n
  | .lifetimeEnd p n => return .lifetimeEnd (← mkReg Γ .ptr p) n
  | .call name ts us args rets => do
    let some ⟨ts', us', f⟩ := callees name | throw s!"no callee bound for @{name}"
    if h : ts' = ts ∧ us' = us then
      return .call (h.1 ▸ h.2 ▸ f) (← mkRegs Γ ts args) (← mkDsts Γ us rets)
    else
      throw s!"@{name} does not have the type the call site needs"
  | .addressof name dst => do
    let some ⟨_, v⟩ := globals name | throw s!"no global bound for @{name}"
    return .addressof v (← mkDst Γ .ptr dst)

variable {n : Nat} (blockTys : Fin n → List Ty)

def mkJump (j : PJump) : Except String (Jump Γ blockTys) := do
  if h : j.target < n then
    return ⟨⟨j.target, h⟩, ← mkRegs Γ _ j.args⟩
  else
    throw s!"block {j.target} out of range"

def mkExit (tRets : List Ty) : PExit → Except String (Exit Γ tRets blockTys)
  | .ret vs => return .ret (← mkRegs Γ tRets vs)
  | .br j => return .br (← mkJump Γ blockTys j)
  | .condBr c t f =>
    return .condBr (← mkReg Γ (.bv 1) c) (← mkJump Γ blockTys t) (← mkJump Γ blockTys f)
  | .switch w v d cs => do
    let cs ← cs.mapM fun (c, j) => return ((BitVec.ofInt w c : ⟦Ty.bv w⟧ᵣ), ← mkJump Γ blockTys j)
    return .switch (← mkReg Γ (.bv w) v) (← mkJump Γ blockTys d) cs

end Prog

/-- The `Func` of `p`, calling `callees name` for `@name`. -/
def Prog.toFunc (p : Prog) (callees : String → Option Callee := fun _ => none)
    (globals : String → Option Global := fun _ => none) : Except String Func := do
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
                  body := ← b.body.mapM (mkInstr p.Γ callees globals)
                  exit := ← mkExit p.Γ blockTys p.tRets b.exit } :
                BasicBlock p.Γ p.tRets blockTys)
      if hs : blocks.size = n then
        return { Γ := p.Γ, tRets := p.tRets, n, blockTys, blockParams, hhasBlock := hn, hentry,
                 blocks := fun k => blocks[k.val] }
      else
        throw "internal: block count"
    else
      throw "the entry block has parameters"
  else
    throw "no blocks"

/-- Translate `reg` to a `Func`. -/
def translate (reg : Region) (callees : String → Option Callee := fun _ => none)
    (globals : String → Option Global := fun _ => none) : Except String Func := do
  (← Prog.ofRegion reg).toFunc callees globals

end

end LeanMLIR.RIR
