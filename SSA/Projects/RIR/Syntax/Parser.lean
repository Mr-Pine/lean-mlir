module

public import SSA.Projects.RIR.Syntax.AST
public meta import Lean.Parser
public meta import Lean.PrettyPrinter
public meta import Lean.Elab.Exception
public meta import SSA.Projects.RIR.Syntax.AST

/-!
# Generic-form MLIR regions

The grammar of `mlir-opt --mlir-print-op-generic` output, as the Firedancer regions use it, and its
conversion to the `MLIR` AST.
-/

namespace LeanMLIR.RIR.MLIR

open Lean Parser PrettyPrinter

/-! ## Raw parsers -/

public meta section

/-- Consume a balanced payload, preserving quoted strings and all interior source text. -/
partial def balancedBracketsFnAux (startPos i : String.Pos.Raw) (closes : List Char)
    (quoted escaped : Bool) : ParserFn :=
  fun c s =>
  if c.atEnd i then s.mkError "found EOF"
  else if quoted then
    let ch := c.get i
    balancedBracketsFnAux startPos (c.next i) closes
      (escaped || ch != '"') (!escaped && ch == '\\') c s
  else
    match c.get i with
    | '"' => balancedBracketsFnAux startPos (c.next i) closes true false c s
    | '(' => balancedBracketsFnAux startPos (c.next i) (')' :: closes) false false c s
    | '[' => balancedBracketsFnAux startPos (c.next i) (']' :: closes) false false c s
    | '<' => balancedBracketsFnAux startPos (c.next i) ('>' :: closes) false false c s
    | '{' => balancedBracketsFnAux startPos (c.next i) ('}' :: closes) false false c s
    | ')' | ']' | '>' | '}' =>
      let ch := c.get i
      match closes with
      | close :: rest =>
        if ch != close then s.mkErrorAt s!"expected '{close}'" i
        else if rest.isEmpty then
          mkNodeToken `balanced_brackets startPos true c (s.setPos (c.next i))
        else balancedBracketsFnAux startPos (c.next i) rest false false c s
      | [] => s.mkErrorAt "unexpected closing bracket" i
    | _ => balancedBracketsFnAux startPos (c.next i) closes false false c s

def balancedBracketsFn : ParserFn := fun c s =>
  if c.get s.pos == '<' then balancedBracketsFnAux s.pos s.pos [] false false c s
  else s.mkError "'<'"

/-- A `<…>` payload with nested brackets, as raw text: `vector<8xi64>`'s `<8xi64>`. -/
def balancedBrackets : Parser :=
  withAntiquot (mkAntiquot "balancedBrackets" `balanced_brackets)
    { fn := balancedBracketsFn, info := mkAtomicInfo "balancedBrackets" }

@[combinator_formatter balancedBrackets]
def balancedBrackets.formatter : Formatter :=
  pure ()

@[combinator_parenthesizer balancedBrackets]
def balancedBrackets.parenthesizer : Parenthesizer :=
  pure ()

/-- A `//` comment up to the end of the line, as `^bb1:  // 2 preds: ^bb0, ^bb1` has. -/
def commentFn : ParserFn := fun c s =>
  let i := s.pos
  if c.get i == '/' && c.get (c.next i) == '/' then
    let s := takeUntilFn (· == '\n') c (s.setPos (c.next (c.next i)))
    mkNodeToken `mlir_comment i true c s
  else s.mkErrorAt "'//' line comment" i

@[inherit_doc commentFn]
def comment : Parser :=
  withAntiquot (mkAntiquot "comment" `mlir_comment)
    { fn := commentFn, info := mkAtomicInfo "comment" }

@[combinator_formatter comment]
def comment.formatter : Formatter :=
  pure ()

@[combinator_parenthesizer comment]
def comment.parenthesizer : Parenthesizer :=
  pure ()

end

/-! ## Grammar

Syntax categories are global even inside a Lean namespace. Keep RIR's categories
separate from `LeanMLIR.MLIRSyntax.GenericParser`: both parsers must be importable
when relating RIR programs to SLLVM semantics. The public `mlir_def` and
`mlir_region%` syntax is unchanged.
-/

public section

declare_syntax_cat rir_mlir_type

declare_syntax_cat rir_mlir_attr_val

declare_syntax_cat rir_mlir_op

declare_syntax_cat rir_mlir_bb

declare_syntax_cat rir_mlir_region

/-- `%arg0` or `%7`. `%arg` is a token of its own once `Run.Tactic` is imported. -/
syntax ssaValue := ("%arg" noWs num) <|> ("%" noWs (num <|> ident))

syntax bbId := num <|> ident

/-- `i64`, `index`, `vector<8xi64>`. -/
syntax ident (balancedBrackets)? : rir_mlir_type

/-- `!llvm.ptr`, `!llvm.array<5 x i64>`. -/
syntax "!" ident (balancedBrackets)? : rir_mlir_type

syntax signedNum := "-"? num

syntax signedNum (":" rir_mlir_type)? : rir_mlir_attr_val

syntax str : rir_mlir_attr_val

syntax "@" (ident <|> str) : rir_mlir_attr_val

syntax "#" ident : rir_mlir_attr_val

/-- Dialect bodies need not be comma-separated attributes (e.g. LLVM memory effects). -/
syntax "#" ident balancedBrackets : rir_mlir_attr_val

/-- The enum/string list form already interpreted by RIR, including overflow flags. -/
declare_syntax_cat dialect_attr_enums

syntax dialect_attr_enum := ident <|> str

syntax dialect_attr_enum,* : dialect_attr_enums

syntax "dense<" rir_mlir_attr_val ">" ":" rir_mlir_type : rir_mlir_attr_val

syntax "array<" rir_mlir_type (":" rir_mlir_attr_val,*)? ">" : rir_mlir_attr_val

syntax "[" rir_mlir_attr_val,* "]" : rir_mlir_attr_val

syntax rir_mlir_type : rir_mlir_attr_val

syntax attrEntry := (ident <|> str) (" = " rir_mlir_attr_val)?

syntax attrDict := "<"? "{" attrEntry,* "}" ">"?

syntax attrDict : rir_mlir_attr_val

/-- `^bb0` or `^name`. `^bb` is a token of its own once `Func` is imported. -/
syntax bbLabel := ("^bb" noWs (num <|> ident)) <|> ("^" bbId)

syntax resultTypes := ("(" rir_mlir_type,* ")") <|> rir_mlir_type

syntax (ssaValue,+ " = ")? str "(" ssaValue,* ")" ("[" bbLabel,* "]")? (attrDict)? ":" "("
  rir_mlir_type,* ")" "->" resultTypes : rir_mlir_op

syntax bbArg := ssaValue ":" rir_mlir_type

syntax bbLabel ("(" bbArg,* ")")? ":" (comment)? rir_mlir_op* : rir_mlir_bb

syntax "{" rir_mlir_bb+ "}" : rir_mlir_region

syntax "{" rir_mlir_op* "}" : rir_mlir_region

end

/-! ## Syntax to AST -/

public meta section

/-- The atoms, literals and identifiers of `stx`, in order. -/
partial def leaves (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ k args => if k == numLitKind || k == strLitKind then #[stx] else args.flatMap leaves
  | .missing => #[]
  | stx => #[stx]

/-- The name of `%arg0` or `%7`, without the `%`. -/
def valueName (v : TSyntax ``ssaValue) : CoreM SSAVal :=
  match leaves v.raw with
  | #[.atom _ "%arg", n] => return s!"arg{n.isNatLit?.getD 0}"
  | #[.atom _ "%", n] =>
    match n.isNatLit? with
    | some k => return toString k
    | none => return n.getId.toString
  | _ => throwErrorAt v "malformed SSA value"

def bbName (x : TSyntax ``bbLabel) : String :=
  let name (n : Syntax) := (n.isNatLit?.map toString).getD n.getId.toString
  match leaves x.raw with
  | #[.atom _ "^bb", n] => "bb" ++ name n
  | #[_, n] => name n
  | _ => ""

/-- The text of a `balancedBrackets` node. -/
def bracketsText (b : Syntax) : String :=
  match leaves b with
  | #[.atom _ s] => s
  | _ => ""

/-- `vector<…>`'s payload without the brackets: `8xi64` is `([8], [], "i64")`. -/
partial def vectorDims (cs : List Char) (fixed scalable : List Nat) :
    Option (List Nat × List Nat × String) :=
  let num (cs : List Char) := (cs.takeWhile Char.isDigit, cs.dropWhile Char.isDigit)
  match cs with
  | '[' :: cs =>
    match num cs with
    | (ds@(_ :: _), ']' :: 'x' :: rest) =>
      vectorDims rest fixed (scalable ++ [(String.ofList ds).toNat!])
    | _ => none
  | cs =>
    match num cs with
    | (ds@(_ :: _), 'x' :: rest) =>
      if scalable.isEmpty then vectorDims rest (fixed ++ [(String.ofList ds).toNat!]) scalable
      else none
    | _ => some (fixed, scalable, String.ofList cs)

def intType? (s : String) : Option MLIRType :=
  if s.startsWith "i" then ((s.drop 1).toString.toNat?).map .int else none

def mlirType : TSyntax `rir_mlir_type → CoreM MLIRType
  | `(rir_mlir_type| $x:ident $[$b]?) => do
    let s := x.getId.toString
    match s, b with
    | "index", none => return .index
    | "vector", some b =>
      let text := bracketsText b
      let some (fixed, scalable, elem) := vectorDims ((text.toList.drop 1).dropLast) [] []
        | throwErrorAt b "malformed vector type 'vector{text}'"
      let some elem := intType? elem
        | throwErrorAt b "unsupported vector element type '{elem}'"
      return .vector fixed scalable elem
    | s, none =>
      let some t := intType? s | throwErrorAt x "unsupported MLIR type '{s}'"
      return t
    | s, some b => throwErrorAt x "unsupported MLIR type '{s}{bracketsText b}'"
  | `(rir_mlir_type| ! $x:ident $[$b]?) =>
    return .undefined (x.getId.toString ++ (b.map (bracketsText ·.raw)).getD "")
  | stx => throwErrorAt stx "malformed MLIR type"

def intValue (n : TSyntax ``signedNum) : Int :=
  match leaves n.raw with
  | #[.atom _ "-", n] => -(n.isNatLit?.getD 0 : Int)
  | #[n] => n.isNatLit?.getD 0
  | _ => 0

/-- Keep the existing enum/list representation where it applies; otherwise retain the
entire dialect body verbatim. The translator remains responsible for known attributes. -/
def dialectAttr (dialect body : String) : CoreM AttrValue := do
  let rawValue := AttrValue.opaque_ dialect body
  let .ok stx := Parser.runParserCategory (← getEnv) `dialect_attr_enums body
    | return rawValue
  let `(dialect_attr_enums| $vs:dialect_attr_enum,*) := stx | return rawValue
  let vs := vs.getElems.toList.map fun v =>
    match leaves v.raw with
    | #[x] => AttrValue.opaque_ dialect ((x.isStrLit?).getD x.getId.toString)
    | _ => rawValue
  return match vs with
    | [v] => v
    | vs => .list vs

mutual

partial def attrVal : TSyntax `rir_mlir_attr_val → CoreM AttrValue
  | `(rir_mlir_attr_val| $n:signedNum $[: $t]?) => do
    return .int (intValue n) (← match t with | some t => mlirType t | none => pure (.int 64))
  | `(rir_mlir_attr_val| $s:str) => return .str s.getString
  | `(rir_mlir_attr_val| @ $x:ident) => return .symbol x.getId.toString
  | `(rir_mlir_attr_val| @ $s:str) => return .symbol s.getString
  | `(rir_mlir_attr_val| # $x:ident) => return .alias x.getId.toString
  | `(rir_mlir_attr_val| # $d:ident $b:balancedBrackets) => do
    let body := bracketsText b
    dialectAttr d.getId.toString (String.ofList ((body.toList.drop 1).dropLast))
  | `(rir_mlir_attr_val| dense< $v > : $t) => return .dense (← attrVal v) (← mlirType t)
  | `(rir_mlir_attr_val| array< $t $[: $vs,*]? >) => do
    let vs : Array (TSyntax `rir_mlir_attr_val) := (vs.map (·.getElems)).getD #[]
    return .array (← mlirType t) (← vs.toList.mapM attrVal)
  | `(rir_mlir_attr_val| [ $vs,* ]) => return .list (← vs.getElems.toList.mapM attrVal)
  | `(rir_mlir_attr_val| $t:rir_mlir_type) => do
    match leaves t.raw with
    | #[x] =>
      if x.isIdent && x.getId.toString == "true" then return .bool true
      if x.isIdent && x.getId.toString == "false" then return .bool false
      return .type (← mlirType t)
    | _ => return .type (← mlirType t)
  | `(rir_mlir_attr_val| $d:attrDict) => return .dict (← attrDictVal d)
  | stx => throwErrorAt stx "malformed MLIR attribute"

partial def attrDictVal : TSyntax ``attrDict → CoreM AttrDict
  | `(attrDict| $[<%$l]? { $es,* } $[>%$r]?) => do
    if l.isSome != r.isSome then
      throwErrorAt (l.getD (r.getD .missing)) "unbalanced '<\{' … '}>'"
    let es ← es.getElems.toList.mapM fun (e : TSyntax ``attrEntry) => do
      match e with
      | `(attrEntry| $k:ident $[= $v]?) =>
        return AttrEntry.mk k.getId.toString (← attrValOrUnit v)
      | `(attrEntry| $k:str $[= $v]?) => return AttrEntry.mk k.getString (← attrValOrUnit v)
      | e => throwErrorAt e "malformed MLIR attribute entry"
    return .mk es
  | stx => throwErrorAt stx "malformed MLIR attribute dictionary"

/-- A dictionary entry's value; a bare key is `unit`. -/
partial def attrValOrUnit : Option (TSyntax `rir_mlir_attr_val) → CoreM AttrValue
  | some v => attrVal v
  | none => return .unit

end

def resTypes : TSyntax ``resultTypes → CoreM (List MLIRType)
  | `(resultTypes| ( $ts,* )) => ts.getElems.toList.mapM mlirType
  | `(resultTypes| $t:rir_mlir_type) => return [← mlirType t]
  | stx => throwErrorAt stx "malformed result types"

/-- Names paired with their types. -/
def typed (ref : Syntax) (what : String) (vs : List SSAVal) (ts : List MLIRType) :
    CoreM (List TypedSSAVal) := do
  unless vs.length == ts.length do
    throwErrorAt ref "{vs.length} {what}, but {ts.length} types"
  return vs.zip ts

def op : TSyntax `rir_mlir_op → CoreM Op
  | stx@`(rir_mlir_op| $[$res,* =]? $name:str ( $args,* ) $[[ $succs,* ]]? $[$attrs]?
      : ( $argTys,* ) -> $resTys) => do
    let res : Array (TSyntax ``ssaValue) := (res.map (·.getElems)).getD #[]
    let succs : Array (TSyntax ``bbLabel) := (succs.map (·.getElems)).getD #[]
    return {
      name := name.getString
      res := ← typed stx "results" (← res.toList.mapM valueName) (← resTypes resTys)
      args :=
        ← typed stx "operands" (← args.getElems.toList.mapM valueName)
          (← argTys.getElems.toList.mapM mlirType)
      successors := succs.toList.map bbName
      attrs := ← match attrs with | some d => attrDictVal d | none => pure (.mk []) }
  | stx => throwErrorAt stx "malformed MLIR operation"

def bbArgVal : TSyntax ``bbArg → CoreM TypedSSAVal
  | `(bbArg| $v : $t) => return (← valueName v, ← mlirType t)
  | a => throwErrorAt a "malformed block argument"

def block : TSyntax `rir_mlir_bb → CoreM Block
  | `(rir_mlir_bb| $name:bbLabel $[( $args,* )]? : $[$_]? $ops*) => do
    let args : Array (TSyntax ``bbArg) := (args.map (·.getElems)).getD #[]
    return { name := bbName name, args := ← args.toList.mapM bbArgVal,
             ops := ← ops.toList.mapM op }
  | stx => throwErrorAt stx "malformed MLIR block"

/-- The region `stx`; a region without block headers is one block `^bb0` without arguments. -/
def region : TSyntax `rir_mlir_region → CoreM Region
  | `(rir_mlir_region| { $bs:rir_mlir_bb* }) => return ⟨← bs.toList.mapM block⟩
  | `(rir_mlir_region| { $ops:rir_mlir_op* }) =>
    return ⟨[{ name := "bb0", args := [], ops := ← ops.toList.mapM op }]⟩
  | stx => throwErrorAt stx "malformed MLIR region"

end

end LeanMLIR.RIR.MLIR
