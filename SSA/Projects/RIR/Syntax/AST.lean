module

public import Lean.ToExpr

/-!
# MLIR syntax trees

The AST of generic-form MLIR regions, as `mlir_def` parses them: blocks of operations with typed
operands and results, successors and attributes. Widths are concrete; nested regions are not
represented.
-/

namespace LeanMLIR.RIR.MLIR

@[expose] public section

/-- An SSA value's name, without the `%`. -/
abbrev SSAVal :=
  String

inductive MLIRType where
  | int (w : Nat)
  | index
  /-- `vector<…>`: the fixed dimensions, then the scalable ones. -/
  | vector (fixed scalable : List Nat) (elem : MLIRType)
  /-- A dialect type as its source text without the `!`, e.g. `llvm.ptr` or
  `llvm.array<5 x i64>`. -/
  | undefined (s : String)
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- `%name : type`. -/
abbrev TypedSSAVal :=
  SSAVal × MLIRType

mutual
inductive AttrValue where
  | symbol (s : String)
  | str (s : String)
  | int (v : Int) (t : MLIRType)
  | bool (b : Bool)
  | type (t : MLIRType)
  | list (vs : List AttrValue)
    /-- `#name`. -/
  | alias (a : String)
    /-- `{k = v, …}`, or `#dialect<k = v, …>`. -/
  | dict (d : AttrDict)
    /-- `#dialect<value>`, e.g. `#llvm.overflow<nsw>`. -/
  | opaque_ (dialect value : String)
  | dense (v : AttrValue) (t : MLIRType)
  | array (t : MLIRType) (vs : List AttrValue)
  | unit
inductive AttrEntry where
  | mk (key : String) (value : AttrValue)
inductive AttrDict where
  | mk (entries : List AttrEntry)
end

deriving instance Lean.ToExpr for AttrValue, AttrEntry, AttrDict

def AttrDict.getAttr? : AttrDict → String → Option AttrValue
  | .mk es, k =>
    es.findSome? fun
      | .mk k' v => if k' == k then some v else none

structure Op where
  name : String
  res : List TypedSSAVal
  args : List TypedSSAVal
  /-- Successor block names, without the `^`. -/
  successors : List String
  attrs : AttrDict
  deriving Lean.ToExpr

def Op.getAttr? (op : Op) (k : String) : Option AttrValue :=
  op.attrs.getAttr? k

def Op.hasAttr (op : Op) (k : String) : Bool :=
  (op.getAttr? k).isSome

structure Block where
  name : String
  args : List TypedSSAVal
  ops : List Op
  deriving Lean.ToExpr

/-- A region's blocks, the entry block first. -/
structure Region where
  blocks : List Block
  deriving Lean.ToExpr

/-- The type as MLIR prints it. -/
partial def MLIRType.toString : MLIRType → String
  | .int w => s!"i{w}"
  | .index => "index"
  | .vector fixed scalable elem =>
    let dims := fixed.map (s!"{·}x") ++ scalable.map (s!"[{·}]x")
    s!"vector<{String.join dims}{elem.toString}>"
  | .undefined s => "!" ++ s

instance : ToString MLIRType :=
  ⟨MLIRType.toString⟩

end

end LeanMLIR.RIR.MLIR
