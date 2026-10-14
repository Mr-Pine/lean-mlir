module

public import MLIR.Syntax.AST
public meta import Lean.Parser
public meta import Lean.PrettyPrinter
public meta import Lean.Elab.Exception
public meta import MLIR.Syntax.AST

/-!
# Generic-form MLIR regions

The grammar of `mlir-opt --mlir-print-op-generic` output, as the Firedancer regions use it, and its
conversion to the `MLIR` AST.
-/

namespace MLIR.MLIR

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

/-- Consume up to the `"` closing the string, skipping each escaped character. -/
partial def mlirStrFnAux (startPos : String.Pos.Raw) (i : String.Pos.Raw) : ParserFn := fun c s =>
  if c.atEnd i then s.mkError "unterminated string"
  else
    match c.get i with
    | '"' => mkNodeToken `mlir_str startPos true c (s.setPos (c.next i))
    | '\\' => if c.atEnd (c.next i) then s.mkError "unterminated string"
      else mlirStrFnAux startPos (c.next (c.next i)) c s
    | _ => mlirStrFnAux startPos (c.next i) c s

def mlirStrFn : ParserFn := fun c s =>
  if c.get s.pos == '"' then mlirStrFnAux s.pos (c.next s.pos) c s else s.mkError "string"

/-- A string with MLIR's escapes (`\\`, `\"`, `\n`, `\t` and `\XX` in hex), as raw text: Lean's
string literal rejects `"\ED"`. -/
def mlirStr : Parser :=
  withAntiquot (mkAntiquot "mlirStr" `mlir_str)
    { fn := mlirStrFn, info := mkAtomicInfo "mlirStr" }

@[combinator_formatter mlirStr]
def mlirStr.formatter : Formatter :=
  pure ()

@[combinator_parenthesizer mlirStr]
def mlirStr.parenthesizer : Parenthesizer :=
  pure ()

/-- Consume a symbol name's characters: letters, digits, `_`, `$`, `.` and `-`. -/
def mlirSymbolNameFn : ParserFn := fun c s =>
  let ok (ch : Char) := ch.isAlphanum || ch == '_' || ch == '$' || ch == '.' || ch == '-'
  let i := s.pos
  if c.atEnd i || !ok (c.get i) then s.mkError "symbol name"
  else mkNodeToken `mlir_symbol_name i true c (takeWhileFn ok c s)

/-- A symbol's name after the `@`, as raw text: `anon.042b.50`, which is no Lean identifier. -/
def mlirSymbolName : Parser :=
  withAntiquot (mkAntiquot "mlirSymbolName" `mlir_symbol_name)
    { fn := mlirSymbolNameFn, info := mkAtomicInfo "mlirSymbolName" }

@[combinator_formatter mlirSymbolName]
def mlirSymbolName.formatter : Formatter :=
  pure ()

@[combinator_parenthesizer mlirSymbolName]
def mlirSymbolName.parenthesizer : Parenthesizer :=
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

declare_syntax_cat mlir_symbol

/-- `%arg0` or `%7`. `%arg` is a token of its own once `Run.Tactic` is imported. -/
syntax ssaValue := ("%arg" noWs num) <|> ("%" noWs (num <|> ident))

syntax bbId := num <|> ident

/-- `i64`, `index`, `vector<8xi64>`. -/
syntax ident (balancedBrackets)? : mlir_type

/-- `!llvm.ptr`, `!llvm.array<5 x i64>`. -/
syntax "!" ident (balancedBrackets)? : mlir_type

syntax signedNum := "-"? num

/-- An attribute: a string first, which `mlir_attr_val`'s token lookahead would reject. -/
syntax attrValue := mlirStr <|> mlir_attr_val

syntax signedNum (":" mlir_type)? : mlir_attr_val

syntax "@" (mlirSymbolName <|> mlirStr) : mlir_attr_val

syntax "#" ident : mlir_attr_val

/-- `distinct[0]<>`, an alias scope's identity. -/
syntax distinctAttr := &"distinct" "[" num "]" balancedBrackets

/-- `nsw`, `argMem = read` as in `#llvm.memory_effects<…>`, a keyword (`private`), or
`distinct[0]<>`. -/
syntax dialectArg := (atomic(ident " = "))? (atomic(distinctAttr) <|> attrValue <|> rawIdent)

syntax "#" ident "<" dialectArg,* ">" : mlir_attr_val

syntax "dense<" attrValue ">" ":" mlir_type : mlir_attr_val

syntax "array<" mlir_type (":" attrValue,*)? ">" : mlir_attr_val

syntax "[" attrValue,* "]" : mlir_attr_val

/-- `<#tbaa_type_desc, 0>`, an element of a TBAA type's `members = {…}`. -/
syntax attrTuple := "<" attrValue,* ">"

syntax namedAttr := ident " = " attrValue

/-- `<id = "omnipotent char", members = {…}>`: an attribute without a dialect prefix, as an inline
TBAA type descriptor. -/
syntax "<" namedAttr,+ ">" : mlir_attr_val

syntax "{" attrTuple,+ "}" : mlir_attr_val

syntax mlir_type : mlir_attr_val

syntax attrEntry := (ident <|> str) (" = " attrValue)?

syntax attrDict := "<"? "{" attrEntry,* "}" ">"?

syntax attrDict : mlir_attr_val

/-- `^bb0` or `^name`. `^bb` is a token of its own once `Func` is imported. -/
syntax bbLabel := ("^bb" noWs (num <|> ident)) <|> ("^" bbId)

syntax resultTypes := ("(" mlir_type,* ")") <|> mlir_type

syntax (ssaValue,+ " = ")? str "(" ssaValue,* ")" ("[" bbLabel,* "]")? (attrDict)? ":" "("
  mlir_type,* ")" "->" resultTypes : mlir_op

syntax bbArg := ssaValue ":" mlir_type

syntax bbLabel ("(" bbArg,* ")")? ":" (comment)? mlir_op* : mlir_bb

/-- Blocks; the entry block's label may be left out. -/
syntax "{" mlir_op* mlir_bb* "}" : mlir_region

/-- `#tbaa_tag = #llvm.tbaa_tag<…>`, a module's attribute alias. -/
syntax aliasDef := "#" ident " = " attrValue

/-- An operation with one region and no operands, results or successors, after the aliases it
refers to: `"llvm.func"() <{…}> ({ … }) : () -> ()`. -/
syntax aliasDef* str "(" ")" attrDict "(" mlir_region ")" ":" "(" ")" "->" "(" ")" : mlir_symbol

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
    -- only as a `dense<…>` attribute's shape: kept as text, never a register's type
    | "tensor", some b => return .undefined ("tensor" ++ bracketsText b)
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

/-- The characters of the `mlirStr` node `x`, its escapes decoded: `\\XX` is the character of
code `XX`, a byte. -/
def mlirStrValue (x : Syntax) : String :=
  let hex (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : List Char → List Char
    | '\\' :: a :: b :: cs =>
      match hex a, hex b with
      | some h, some l => Char.ofNat (16 * h + l) :: go cs
      | _, _ => (if a == 'n' then '\n' else if a == 't' then '\t' else a) :: go (b :: cs)
    | '\\' :: a :: cs => (if a == 'n' then '\n' else if a == 't' then '\t' else a) :: go cs
    | c :: cs => c :: go cs
    | [] => []
  String.ofList (go ((bracketsText x).toList.drop 1).dropLast)

mutual

partial def anyAttrVal (v : TSyntax ``attrValue) : CoreM AttrValue :=
  let x := v.raw[0]
  if x.getKind == `mlir_str then return .str (mlirStrValue x) else attrVal ⟨x⟩

partial def attrVal : TSyntax `mlir_attr_val → CoreM AttrValue
  | `(mlir_attr_val| $n:signedNum $[: $t]?) => do
    return .int (intValue n) (← match t with | some t => mlirType t | none => pure (.int 64))
  | stx@`(mlir_attr_val| @ $_) =>
    let x := stx.raw[1]
    return .symbol (if x.getKind == `mlir_str then mlirStrValue x else bracketsText x)
  | `(mlir_attr_val| # $x:ident) => return .alias x.getId.toString
  | `(mlir_attr_val| # $d:ident < $vs,* >) => do
    let dialect := d.getId.toString
    -- `k = v`'s key, and the value: an attribute, or a keyword
    let vs := vs.getElems.toList.map fun (a : TSyntax ``dialectArg) =>
      (if a.raw[0][0].isIdent then some a.raw[0][0].getId.toString else none, a.raw[1])
    -- a word or string, `nsw`, `none`, `private`, as itself; anything else as an attribute
    let word (v : Syntax) : CoreM AttrValue := do
      if v.isIdent then return AttrValue.opaque_ dialect v.getId.toString
      if v.getKind == ``distinctAttr then
        return AttrValue.opaque_ "distinct" (toString (v[2].isNatLit?.getD 0))
      let x := v[0]
      if x.getKind == `mlir_str then return AttrValue.opaque_ dialect (mlirStrValue x)
      match leaves x with
      | #[y] => if y.isIdent then return AttrValue.opaque_ dialect y.getId.toString
      | _ => pure ()
      anyAttrVal ⟨v⟩
    -- `k = v, …`: a dictionary
    if vs.any (·.1.isSome) then
      let es ← vs.mapM fun
        | (some k, v) => return AttrEntry.mk k (← word v)
        | (none, v) => throwErrorAt v "expected `key = value` inside '#{dialect}<…>'"
      return .dict (.mk es)
    let vs ← vs.mapM (word ·.2)
    match vs with
    | [v] => return v
    | vs => return .list vs
  | `(mlir_attr_val| dense< $v > : $t) => return .dense (← anyAttrVal v) (← mlirType t)
  | `(mlir_attr_val| array< $t $[: $vs,*]? >) => do
    let vs : Array (TSyntax ``attrValue) := (vs.map (·.getElems)).getD #[]
    return .array (← mlirType t) (← vs.toList.mapM anyAttrVal)
  | `(mlir_attr_val| [ $vs,* ]) => return .list (← vs.getElems.toList.mapM anyAttrVal)
  | `(mlir_attr_val| { $ts:attrTuple,* }) =>
    .list <$> ts.getElems.toList.mapM fun (t : TSyntax ``attrTuple) => do
      match t with
      | `(attrTuple| < $vs,* >) => return .list (← vs.getElems.toList.mapM anyAttrVal)
      | t => throwErrorAt t "malformed `<…>` tuple"
  | `(mlir_attr_val| < $es:namedAttr,* >) =>
    .dict <$> .mk <$> es.getElems.toList.mapM fun (e : TSyntax ``namedAttr) => do
      match e with
      | `(namedAttr| $k:ident = $v) => return AttrEntry.mk k.getId.toString (← anyAttrVal v)
      | e => throwErrorAt e "malformed `key = value` entry"
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
partial def attrValOrUnit : Option (TSyntax ``attrValue) → CoreM AttrValue
  | some v => anyAttrVal v
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

def block : TSyntax `mlir_bb → CoreM Block
  | `(mlir_bb| $name:bbLabel $[( $args,* )]? : $[$_]? $ops*) => do
    let args : Array (TSyntax ``bbArg) := (args.map (·.getElems)).getD #[]
    return { name := bbName name, args := ← args.toList.mapM bbArgVal,
             ops := ← ops.toList.mapM op }
  | stx => throwErrorAt stx "malformed MLIR block"

/-- The region `stx`; operations before the first block header are the entry block `^bb0`, without
arguments. -/
def region : TSyntax `mlir_region → CoreM Region
  | `(mlir_region| { $ops:mlir_op* $bs:mlir_bb* }) => do
    let bs ← bs.toList.mapM block
    if ops.isEmpty && !bs.isEmpty then return ⟨bs⟩
    return ⟨{ name := "bb0", args := [], ops := ← ops.toList.mapM op } :: bs⟩
  | stx => throwErrorAt stx "malformed MLIR region"

def symbolOp : TSyntax `mlir_symbol → CoreM SymbolOp
  | `(mlir_symbol| $as:aliasDef* $name:str ( ) $attrs:attrDict ( $r:mlir_region ) : ( ) -> ( )) => do
    let aliases ← as.toList.mapM fun (a : TSyntax ``aliasDef) => do
      match a with
      | `(aliasDef| # $a:ident = $v) => return (a.getId.toString, ← anyAttrVal v)
      | a => throwErrorAt a "malformed attribute alias"
    return { aliases, name := name.getString, attrs := ← attrDictVal attrs, region := ← region r }
  | stx => throwErrorAt stx "malformed MLIR operation"

end

end MLIR.MLIR
