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

/-- Consume up to the `>` closing the `<` at the start; the node's atom is the text read. -/
partial def balancedBracketsFnAux (startPos i : String.Pos.Raw) (depth : Nat) : ParserFn :=
  fun c s =>
  if c.atEnd i then s.mkError "found EOF"
  else
    match c.get i with
    | '(' | '[' | '<' | '{' => balancedBracketsFnAux startPos (c.next i) (depth + 1) c s
    | ')' | ']' | '>' | '}' =>
      if depth == 1 then mkNodeToken `balanced_brackets startPos true c (s.setPos (c.next i))
      else balancedBracketsFnAux startPos (c.next i) (depth - 1) c s
    | _ => balancedBracketsFnAux startPos (c.next i) depth c s

def balancedBracketsFn : ParserFn := fun c s =>
  if c.get s.pos == '<' then balancedBracketsFnAux s.pos s.pos 0 c s else s.mkError "'<'"

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

/-! ## Grammar -/

public section

declare_syntax_cat mlir_type

declare_syntax_cat mlir_attr_val

declare_syntax_cat mlir_op

declare_syntax_cat mlir_bb

declare_syntax_cat mlir_region

/-- `%arg0` or `%7`. `%arg` is a token of its own once `Run.Tactic` is imported. -/
syntax ssaValue := ("%arg" noWs num) <|> ("%" noWs (num <|> ident))

syntax bbId := num <|> ident

/-- `i64`, `index`, `vector<8xi64>`. -/
syntax ident (balancedBrackets)? : mlir_type

/-- `!llvm.ptr`, `!llvm.array<5 x i64>`. -/
syntax "!" ident (balancedBrackets)? : mlir_type

syntax signedNum := "-"? num

syntax signedNum (":" mlir_type)? : mlir_attr_val

syntax str : mlir_attr_val

syntax "@" (ident <|> str) : mlir_attr_val

syntax "#" ident : mlir_attr_val

syntax "#" ident "<" mlir_attr_val,* ">" : mlir_attr_val

syntax "dense<" mlir_attr_val ">" ":" mlir_type : mlir_attr_val

syntax "array<" mlir_type (":" mlir_attr_val,*)? ">" : mlir_attr_val

syntax "[" mlir_attr_val,* "]" : mlir_attr_val

syntax mlir_type : mlir_attr_val

syntax attrEntry := (ident <|> str) (" = " mlir_attr_val)?

syntax attrDict := "<"? "{" attrEntry,* "}" ">"?

syntax attrDict : mlir_attr_val

syntax successor := "^" bbId

syntax resultTypes := ("(" mlir_type,* ")") <|> mlir_type

syntax (ssaValue,+ " = ")? str "(" ssaValue,* ")" ("[" successor,* "]")? (attrDict)? ":" "("
  mlir_type,* ")" "->" resultTypes : mlir_op

syntax bbArg := ssaValue ":" mlir_type

syntax "^" bbId ("(" bbArg,* ")")? ":" (comment)? mlir_op* : mlir_bb

syntax "{" mlir_bb+ "}" : mlir_region

syntax "{" mlir_op* "}" : mlir_region

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

def bbName (x : TSyntax ``bbId) : String :=
  match leaves x.raw with
  | #[n] => (n.isNatLit?.map toString).getD n.getId.toString
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

def mlirType : TSyntax `mlir_type → CoreM MLIRType
  | `(mlir_type| $x:ident $[$b]?) => do
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
  | `(mlir_type| ! $x:ident $[$b]?) =>
    return .undefined (x.getId.toString ++ (b.map (bracketsText ·.raw)).getD "")
  | stx => throwErrorAt stx "malformed MLIR type"

def intValue (n : TSyntax ``signedNum) : Int :=
  match leaves n.raw with
  | #[.atom _ "-", n] => -(n.isNatLit?.getD 0 : Int)
  | #[n] => n.isNatLit?.getD 0
  | _ => 0

mutual

partial def attrVal : TSyntax `mlir_attr_val → CoreM AttrValue
  | `(mlir_attr_val| $n:signedNum $[: $t]?) => do
    return .int (intValue n) (← match t with | some t => mlirType t | none => pure (.int 64))
  | `(mlir_attr_val| $s:str) => return .str s.getString
  | `(mlir_attr_val| @ $x:ident) => return .symbol x.getId.toString
  | `(mlir_attr_val| @ $s:str) => return .symbol s.getString
  | `(mlir_attr_val| # $x:ident) => return .alias x.getId.toString
  | `(mlir_attr_val| # $d:ident < $vs,* >) => do
    let dialect := d.getId.toString
    let vs ← vs.getElems.toList.mapM fun (v : TSyntax `mlir_attr_val) => do
      match leaves v.raw with
      | #[x] =>
        if x.isIdent then return AttrValue.opaque_ dialect x.getId.toString
        if let some s := x.isStrLit? then return AttrValue.opaque_ dialect s
        throwErrorAt v "unsupported contents of '#{dialect}<…>'"
      | _ => throwErrorAt v "unsupported contents of '#{dialect}<…>'"
    match vs with
    | [v] => return v
    | vs => return .list vs
  | `(mlir_attr_val| dense< $v > : $t) => return .dense (← attrVal v) (← mlirType t)
  | `(mlir_attr_val| array< $t $[: $vs,*]? >) => do
    let vs : Array (TSyntax `mlir_attr_val) := (vs.map (·.getElems)).getD #[]
    return .array (← mlirType t) (← vs.toList.mapM attrVal)
  | `(mlir_attr_val| [ $vs,* ]) => return .list (← vs.getElems.toList.mapM attrVal)
  | `(mlir_attr_val| $t:mlir_type) => do
    match leaves t.raw with
    | #[x] =>
      if x.isIdent && x.getId.toString == "true" then return .bool true
      if x.isIdent && x.getId.toString == "false" then return .bool false
      return .type (← mlirType t)
    | _ => return .type (← mlirType t)
  | `(mlir_attr_val| $d:attrDict) => return .dict (← attrDictVal d)
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
partial def attrValOrUnit : Option (TSyntax `mlir_attr_val) → CoreM AttrValue
  | some v => attrVal v
  | none => return .unit

end

def resTypes : TSyntax ``resultTypes → CoreM (List MLIRType)
  | `(resultTypes| ( $ts,* )) => ts.getElems.toList.mapM mlirType
  | `(resultTypes| $t:mlir_type) => return [← mlirType t]
  | stx => throwErrorAt stx "malformed result types"

/-- Names paired with their types. -/
def typed (ref : Syntax) (what : String) (vs : List SSAVal) (ts : List MLIRType) :
    CoreM (List TypedSSAVal) := do
  unless vs.length == ts.length do
    throwErrorAt ref "{vs.length} {what}, but {ts.length} types"
  return vs.zip ts

def op : TSyntax `mlir_op → CoreM Op
  | stx@`(mlir_op| $[$res,* =]? $name:str ( $args,* ) $[[ $succs,* ]]? $[$attrs]?
      : ( $argTys,* ) -> $resTys) => do
    let res : Array (TSyntax ``ssaValue) := (res.map (·.getElems)).getD #[]
    let succs : Array (TSyntax ``successor) := (succs.map (·.getElems)).getD #[]
    return {
      name := name.getString
      res := ← typed stx "results" (← res.toList.mapM valueName) (← resTypes resTys)
      args :=
        ← typed stx "operands" (← args.getElems.toList.mapM valueName)
          (← argTys.getElems.toList.mapM mlirType)
      successors := succs.toList.map fun s => bbName ⟨s.raw[1]⟩
      attrs := ← match attrs with | some d => attrDictVal d | none => pure (.mk []) }
  | stx => throwErrorAt stx "malformed MLIR operation"

def bbArgVal : TSyntax ``bbArg → CoreM TypedSSAVal
  | `(bbArg| $v : $t) => return (← valueName v, ← mlirType t)
  | a => throwErrorAt a "malformed block argument"

def block : TSyntax `mlir_bb → CoreM Block
  | `(mlir_bb| ^ $name $[( $args,* )]? : $[$_]? $ops*) => do
    let args : Array (TSyntax ``bbArg) := (args.map (·.getElems)).getD #[]
    return { name := bbName name, args := ← args.toList.mapM bbArgVal,
             ops := ← ops.toList.mapM op }
  | stx => throwErrorAt stx "malformed MLIR block"

/-- The region `stx`; a region without block headers is one block `^bb0` without arguments. -/
def region : TSyntax `mlir_region → CoreM Region
  | `(mlir_region| { $bs:mlir_bb* }) => return ⟨← bs.toList.mapM block⟩
  | `(mlir_region| { $ops:mlir_op* }) =>
    return ⟨[{ name := "bb0", args := [], ops := ← ops.toList.mapM op }]⟩
  | stx => throwErrorAt stx "malformed MLIR region"

end

end LeanMLIR.RIR.MLIR
