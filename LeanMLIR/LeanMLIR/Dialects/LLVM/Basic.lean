/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework
import LeanMLIR.Util
import LeanMLIR.Tactic.SimpSet

import LeanMLIR.Dialects.LLVM.Semantics

/-!
  # InstCombine Dialect

  This file defines a dialect of basic arithmetic and bitwise operations on bitvectors.

  The dialect supports types of arbitrary-width bitvectors.
  Thus, some definitions wil be parameterized by `φ`, the number of width meta-variables there are.
  This parameter will usually be either `0`, indicating that all widths are known, concrete values,
  or `1`, indicating there is exactly one distinct width meta-variable.

  In particular, we only define a denotational semantics for concrete programs (i.e., where `φ = 0`)


  see https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
-/

namespace InstCombine

open BitVec

open LLVM

/-! ### Types -/

abbrev Width φ := ConcreteOrMVar Nat φ

inductive MTy (φ : Nat)
  | bitvec (w : Width φ) : MTy φ
  | vector (l: Nat) (elem: MTy φ) : MTy φ
  deriving DecidableEq, Inhabited, Lean.ToExpr

/-! ### Type Formatting

NOTE: stated on `MTy` and placed here, rather than on `(MetaLLVM φ).Ty` further
down, because `MOp` carries an `MTy φ` and its `deriving Repr` needs these. -/

def MTy.print : MTy φ → String
  | .bitvec (.concrete w)  => s!"i{w}"
  | .bitvec (.mvar ⟨i, _⟩) => s!"i$\{%{i}}"
  | .vector length elem => s!"{print elem}×{length}"

instance : ToString (MTy φ) := ⟨MTy.print⟩
instance : Repr (MTy φ) where
  reprPrec ty _ := s!"{ty}"

/-! ### Operations -/

/-- Homogeneous, unary operations -/
inductive MOp.UnaryOp (φ : Nat) : Type
  | neg
  | not
  | copy
  | freeze
  | trunc (w' : Width φ) (noWrapFlags : NoWrapFlags := {nsw := false, nuw := false} )
  | zext  (w' : Width φ) (nneg : NonNegFlag := {nneg := false} )
  | sext  (w' : Width φ)
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Homogeneous, binary operations -/
inductive MOp.BinaryOp : Type
  | and
  | or   (disjoint : DisjointFlag := {disjoint := false} )
  | xor
  | shl  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | lshr (exact : ExactFlag := {exact := false} )
  | ashr (exact : ExactFlag := {exact := false} )
  | urem
  | srem
  | add  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | mul  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | sub  (nswnuw : NoWrapFlags := {nsw := false, nuw := false} )
  | sdiv (exact : ExactFlag := {exact := false} )
  | udiv (exact : ExactFlag := {exact := false} )
deriving DecidableEq, Inhabited, Lean.ToExpr

open Std (Format) in
/--
If both the nuw and nsw flags are the default value (false,false),
then we should not print them. This should be the default
behavior in Lean, but it isn't
-/
def reprWithoutFlags (op : MOp.BinaryOp) (prec : Nat) : Format :=
  let op  : String := match op with
    | .and                => "and"
    | .or   ⟨false⟩        => "or"
    | .or   ⟨true⟩         => "or disjoint"
    | .xor                => "xor"
    | .shl  ⟨false, false⟩ => "shl"
    | .shl  ⟨nsw, nuw⟩     => toString f!"shl {nsw} {nuw}"
    | .lshr ⟨false⟩        => "lshr"
    | .lshr ⟨true⟩         => "lshr exact"
    | .ashr ⟨false⟩        => "ashr"
    | .ashr ⟨true⟩         => "ashr exact"
    | .urem               => "urem"
    | .srem               => "srem"
    | .add  ⟨false, false⟩ => "add"
    | .add  ⟨nsw, nuw⟩     => toString f!"add {nsw} {nuw}"
    | .mul  ⟨false, false⟩ => "mul"
    | .mul  ⟨nsw, nuw⟩     => toString f!"mul {nsw} {nuw}"
    | .sub  ⟨false, false⟩ => "sub"
    | .sub  ⟨nsw, nuw⟩     => toString f!"sub {nsw} {nuw}"
    | .sdiv ⟨false⟩        => "sdiv"
    | .sdiv ⟨true⟩         => "sdiv exact"
    | .udiv ⟨false⟩        => "udiv"
    | .udiv ⟨true⟩         => "udiv exact"
  Repr.addAppParen (Format.group (Format.nest
    (if prec >= max_prec then 1 else 2) f!"InstCombine.MOp.BinaryOp.{op}"))
    prec

instance : Repr (MOp.BinaryOp) where
  reprPrec := reprWithoutFlags

-- See: https://releases.llvm.org/14.0.0/docs/LangRef.html#bitwise-binary-operations
inductive MOp (φ : Nat) : Type
  | unary   (w : Width φ) (op : MOp.UnaryOp φ) :  MOp φ
  | binary  (w : Width φ) (op : MOp.BinaryOp) :  MOp φ
  | select  (w : Width φ) : MOp φ
  | icmp    (c : IntPred) (w : Width φ) : MOp φ
  /-- Since the width of the const might not be known, we just store the value as an `Int` -/
  | const (w : Width φ) (val : ℤ) : MOp φ
  /-- `llvm.mlir.poison`. Carries a full `MTy φ` rather than a `Width φ`, since
  poison exists at every type, vectors included. -/
  | poison (t : MTy φ) : MOp φ
  /-- `llvm.mlir.constant` with a `dense<…>` value. Carries a full `MTy φ` for
  the same reason `poison` does. `vals` is either a single value (MLIR's splat
  form, `dense<0>`) or one value per lane (`dense<[1, 2, 3]>`). -/
  | constDense (t : MTy φ) (vals : List Int) : MOp φ
  /-- `llvm.insertelement` on a `vector l elem`, with an `idxW`-wide index. -/
  | insertelement (elem : MTy φ) (l : Nat) (idxW : Width φ) : MOp φ
  /-- `llvm.shufflevector` over two `vector l elem` operands. The mask is an
  attribute rather than an operand, so the op carries it; its length is the
  length of the result. -/
  | shufflevector (elem : MTy φ) (l : Nat) (mask : List Int) : MOp φ
  /-- The AVX-512 IFMA intrinsics `x86_avx512_vpmadd52{l,h}_uq_512`, reached
  through `llvm.call`. `hi` selects the high variant. -/
  | vpmadd52 (hi : Bool) (l : Nat) : MOp φ
  /-- A binary operation applied lane-wise to two `vector l (bitvec w)`
  operands. One constructor covers every `BinaryOp`, as LLVM's arithmetic is
  elementwise on vectors. -/
  | vectorBinary (l : Nat) (w : Width φ) (op : MOp.BinaryOp) : MOp φ
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

def toStringWithFlags (op : MOp.BinaryOp) : String :=
  let op  : String := match op with
    | .and                  => "and"
    | .or   ⟨false⟩         => "or"
    | .or   ⟨true⟩          => "or disjoint"
    | .xor                  => "xor"
    | .shl  ⟨false, false⟩  => "shl"
    | .shl  ⟨nsw, nuw⟩      => toString f!"shl {nsw} {nuw}"
    | .lshr ⟨false⟩         => "lshr"
    | .lshr ⟨true⟩          => "lshr exact"
    | .ashr ⟨false⟩         => "ashr"
    | .ashr ⟨true⟩          => "ashr exact"
    | .urem                 => "urem"
    | .srem                 => "srem"
    | .add  ⟨false, false⟩  => "add"
    | .add  ⟨nsw, nuw⟩      => toString f!"add {nsw} {nuw}"
    | .mul  ⟨false, false⟩  => "mul"
    | .mul  ⟨nsw, nuw⟩      => toString f!"mul {nsw} {nuw}"
    | .sub  ⟨false, false⟩  => "sub"
    | .sub  ⟨nsw, nuw⟩      => toString f!"sub {nsw} {nuw}"
    | .sdiv ⟨false⟩         => "sdiv"
    | .sdiv ⟨true⟩          => "sdiv exact"
    | .udiv ⟨false⟩         => "udiv"
    | .udiv ⟨true⟩          => "udiv exact"
  s!"llvm.{op}"

instance : ToString (MOp.BinaryOp) where
  toString := toStringWithFlags

instance : ToString (MOp.UnaryOp (φ : Nat)) where
  toString t := repr t |>.pretty

instance : ToString (MOp 0) where
   toString  op :=
     match op with
     | .unary _w op => s!"\"{toString op}\""
     | .binary _w op => s!"\"{toString  op}\""
     | .select  _w => "select"
     | .icmp  _pred _w => "icmp"
     | .const w val => s!"\"llvm.mlir.constant\"() \{value = {val} : {w}}"
     | .poison t => s!"\"llvm.mlir.poison\"() : () -> {t}"
     | .constDense t vals => s!"\"llvm.mlir.constant\"() \{value = dense<{vals}> : {t}}"
     | .insertelement .. => "\"llvm.insertelement\""
     | .shufflevector .. => "\"llvm.shufflevector\""
     | .vpmadd52 hi _ => if hi then "\"llvm.call\" vpmadd52huq" else "\"llvm.call\" vpmadd52luq"
     | .vectorBinary _ _ op => s!"\"llvm.{op}\""

/-! ## Dialect -/

/-- `MetaLLVM φ` is the `LLVM` dialect with at most `φ` metavariables -/
abbrev MetaLLVM (φ : Nat) : Dialect where
  Op := MOp φ
  Ty := MTy φ

def LLVM : Dialect where
  Op := MOp 0
  Ty := MTy 0

/-- Defining an instance for LLVM.Ty from InstCombine.Ty instance.-/
instance : DecidableEq LLVM.Ty :=
  inferInstanceAs <| DecidableEq (InstCombine.MTy _)

/-- Defining an instance for LLVM.Op from InstCombine.Op instance. -/
instance : DecidableEq LLVM.Op :=
    inferInstanceAs <| DecidableEq (InstCombine.MOp 0)

@[deprecated "Use `LLVM.Op` instead" (since:="2025-04-30")] abbrev Op := LLVM.Op
@[deprecated "Use `LLVM.Ty` instead" (since:="2025-04-30")] abbrev Ty := LLVM.Ty

namespace MOp

@[match_pattern] def neg    (w : Width φ) : MOp φ := .unary w .neg
@[match_pattern] def not    (w : Width φ) : MOp φ := .unary w .not
@[match_pattern] def copy   (w : Width φ) : MOp φ := .unary w .copy
@[match_pattern] def freeze (w : Width φ) : MOp φ := .unary w .freeze
@[match_pattern] def sext   (w w' : Width φ) : MOp φ := .unary w (.sext w')

/- This definition uses a nneg flag -/
@[match_pattern] def zext (w w' : Width φ)
  (NonNegFlag: NonNegFlag := {nneg := false}) : MOp φ
    := .unary w (.zext w' NonNegFlag)

@[match_pattern] def and    (w : Width φ) : MOp φ := .binary w .and
@[match_pattern] def xor    (w : Width φ) : MOp φ := .binary w .xor
@[match_pattern] def urem   (w : Width φ) : MOp φ := .binary w .urem
@[match_pattern] def srem   (w : Width φ) : MOp φ := .binary w .srem

/- This definition uses a disjoint flag -/
@[match_pattern] def or (w : Width φ)
  (DisjointFlag : DisjointFlag := {disjoint := false} ) : MOp φ
    := .binary w (.or DisjointFlag )

/- These definitions use NoWrapFlags -/
@[match_pattern] def trunc  (w w' : Width φ)
  (noWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .unary w (.trunc w' noWrapFlags)

@[match_pattern] def shl (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.shl NoWrapFlags )
@[match_pattern] def add (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.add NoWrapFlags )
@[match_pattern] def mul (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.mul NoWrapFlags )
@[match_pattern] def sub (w : Width φ)
  (NoWrapFlags: NoWrapFlags := {nsw := false , nuw := false}) : MOp φ
    := .binary w (.sub NoWrapFlags )

/- These definitions use an exact flag -/
@[match_pattern] def lshr (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.lshr ExactFlag )
@[match_pattern] def ashr (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.ashr ExactFlag )
@[match_pattern] def sdiv (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.sdiv ExactFlag )
@[match_pattern] def udiv (w : Width φ)
  (ExactFlag : ExactFlag := {exact := false} ) : MOp φ
    := .binary w (.udiv ExactFlag )

/-- Recursion principle in terms of individual operations, rather than `unary` or `binary` -/
def deepCasesOn {motive : ∀ {φ}, MOp φ → Sort*}
    (neg    : ∀ {φ} {w : Width φ},               motive (neg  w))
    (not    : ∀ {φ} {w : Width φ},               motive (not  w))
    (trunc  : ∀ {φ noWrapFlags} {w w' : Width φ},            motive (trunc w w' noWrapFlags))
    (zext   : ∀ {φ NonNegFlag} {w w' : Width φ}, motive (zext  w w' NonNegFlag))
    (sext   : ∀ {φ} {w w' : Width φ},            motive (sext  w w'))
    (copy   : ∀ {φ} {w : Width φ},               motive (copy w))
    (freeze : ∀ {φ} {w : Width φ},               motive (freeze w))
    (and    : ∀ {φ} {w : Width φ},               motive (and  w))
    (or     : ∀ {φ DisjointFlag} {w : Width φ},  motive (or w DisjointFlag))
    (xor    : ∀ {φ} {w : Width φ},               motive (xor  w))
    (shl    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (shl  w NoWrapFlags))
    (lshr   : ∀ {φ ExactFlag} {w : Width φ},     motive (lshr w ExactFlag))
    (ashr   : ∀ {φ ExactFlag} {w : Width φ},     motive (ashr w ExactFlag))
    (urem   : ∀ {φ} {w : Width φ},               motive (urem w))
    (srem   : ∀ {φ} {w : Width φ},               motive (srem w))
    (add    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (add w NoWrapFlags))
    (mul    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (mul w NoWrapFlags))
    (sub    : ∀ {φ NoWrapFlags} {w : Width φ},   motive (sub w NoWrapFlags))
    (sdiv   : ∀ {φ ExactFlag} {w : Width φ},     motive (sdiv w ExactFlag))
    (udiv   : ∀ {φ ExactFlag} {w : Width φ},     motive (udiv w ExactFlag))
    (select : ∀ {φ} {w : Width φ},               motive (select w))
    (icmp   : ∀ {φ c} {w : Width φ},             motive (icmp c w))
    (const  : ∀ {φ v} {w : Width φ},             motive (const w v))
    (poison : ∀ {φ} {t : MTy φ},                 motive (poison t))
    (constDense : ∀ {φ vs} {t : MTy φ},          motive (constDense t vs))
    (insertelement : ∀ {φ l} {e : MTy φ} {w : Width φ}, motive (insertelement e l w))
    (shufflevector : ∀ {φ l m} {e : MTy φ},      motive (shufflevector e l m))
    (vpmadd52 : ∀ {φ hi l},                      motive (φ := φ) (vpmadd52 hi l))
    (vectorBinary : ∀ {φ l o} {w : Width φ},     motive (vectorBinary l w o)) :
    ∀ {φ} (op : MOp φ), motive op
  | _, .poison _   => poison
  | _, .constDense ..  => constDense
  | _, .insertelement .. => insertelement
  | _, .shufflevector .. => shufflevector
  | _, .vpmadd52 ..    => vpmadd52
  | _, .vectorBinary .. => vectorBinary
  | _, .neg _      => neg
  | _, .not _      => not
  | _, .trunc _ _ _  => trunc
  | _, .zext _ _ _ => zext
  | _, .sext _ _   => sext
  | _, .copy _     => copy
  | _, .freeze _   => freeze
  | _, .and _      => and
  | _, .or _ _     => or
  | _, .xor _      => xor
  | _, .shl _ _    => shl
  | _, .lshr _ _   => lshr
  | _, .ashr _ _   => ashr
  | _, .urem _     => urem
  | _, .srem _     => srem
  | _, .add _ _    => add
  | _, .mul _ _    => mul
  | _, .sub _ _    => sub
  | _, .sdiv _ _   => sdiv
  | _, .udiv _ _   => udiv
  | _, .select _   => select
  | _, .icmp ..    => icmp
  | _, .const ..   => const

end MOp

namespace LLVM.Op

@[match_pattern] abbrev unary  (w : Nat) (op : MOp.UnaryOp 0) : LLVM.Op :=
  MOp.unary (.concrete w) op

@[match_pattern] abbrev binary (w : Nat) (op : MOp.BinaryOp) : LLVM.Op :=
  MOp.binary (.concrete w) op

@[match_pattern] abbrev and    : Nat → LLVM.Op := MOp.and    ∘ .concrete
@[match_pattern] abbrev not    : Nat → LLVM.Op := MOp.not    ∘ .concrete
@[match_pattern] abbrev sext   : Nat → Nat → LLVM.Op := fun w w' => MOp.sext (.concrete w) (.concrete w')
@[match_pattern] abbrev xor    : Nat → LLVM.Op := MOp.xor    ∘ .concrete
@[match_pattern] abbrev urem   : Nat → LLVM.Op := MOp.urem   ∘ .concrete
@[match_pattern] abbrev srem   : Nat → LLVM.Op := MOp.srem   ∘ .concrete
@[match_pattern] abbrev select : Nat → LLVM.Op := MOp.select ∘ .concrete
@[match_pattern] abbrev neg    : Nat → LLVM.Op := MOp.neg    ∘ .concrete
@[match_pattern] abbrev copy   : Nat → LLVM.Op := MOp.copy   ∘ .concrete
@[match_pattern] abbrev freeze : Nat → LLVM.Op := MOp.freeze  ∘ .concrete

@[match_pattern] abbrev icmp (c : IntPred)   : Nat → LLVM.Op  := MOp.icmp c ∘ .concrete
@[match_pattern] abbrev const (w : Nat) (val : ℤ) : LLVM.Op        := MOp.const (.concrete w) val
/-- Unlike its neighbours this takes a type rather than a width, since poison
exists at vector types too. -/
@[match_pattern] abbrev poison : LLVM.Ty → LLVM.Op                 := MOp.poison
@[match_pattern] abbrev constDense : LLVM.Ty → List Int → LLVM.Op  := MOp.constDense
@[match_pattern] abbrev insertelement (e : LLVM.Ty) (l w : Nat) : LLVM.Op :=
  MOp.insertelement e l (.concrete w)
@[match_pattern] abbrev shufflevector : LLVM.Ty → Nat → List Int → LLVM.Op :=
  MOp.shufflevector
@[match_pattern] abbrev vpmadd52 : Bool → Nat → LLVM.Op := MOp.vpmadd52
@[match_pattern] abbrev vectorBinary (l w : Nat) (op : MOp.BinaryOp) : LLVM.Op :=
  MOp.vectorBinary l (.concrete w) op

/- This operation is separate from the others because it takes in a flag: nneg. -/
@[match_pattern] abbrev zext (w w': Nat) (flag : NonNegFlag := {nneg := false}) : LLVM.Op :=
  MOp.zext (.concrete w) (.concrete w') flag

/- This operation is separate from the others because it takes in a flag: disjoint. -/
@[match_pattern] abbrev or (w : Nat) (flag : DisjointFlag := {disjoint := false} ) : LLVM.Op :=
  MOp.or (.concrete w) flag

/- These operations are separate from the others because they take in 2 flags: nuw and nsw.-/
@[match_pattern] abbrev trunc (w w': Nat) (flags: NoWrapFlags := {}) : LLVM.Op :=
  MOp.trunc (.concrete w) (.concrete w') flags

@[match_pattern] abbrev shl (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.shl (.concrete w) flags
@[match_pattern] abbrev add (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.add (.concrete w) flags
@[match_pattern] abbrev mul (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.mul (.concrete w) flags
@[match_pattern] abbrev sub (w : Nat) (flags: NoWrapFlags := {}) : LLVM.Op := MOp.sub (.concrete w) flags

/- These operations are separate from the others because they take in 1 flag: exact.-/
@[match_pattern] abbrev lshr (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.lshr (.concrete w) flag
@[match_pattern] abbrev ashr (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.ashr (.concrete w) flag
@[match_pattern] abbrev sdiv (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.sdiv (.concrete w) flag
@[match_pattern] abbrev udiv (w : Nat) (flag : ExactFlag := {} ) : LLVM.Op := MOp.udiv (.concrete w) flag

end LLVM.Op

/-! ### Basic Instances -/

instance : Monad (MetaLLVM φ).m := by unfold MetaLLVM; infer_instance
instance : LawfulMonad (MetaLLVM φ).m := by unfold MetaLLVM; infer_instance
instance : Monad LLVM.m := by unfold LLVM; infer_instance
instance : LawfulMonad LLVM.m := by unfold LLVM; infer_instance

instance {φ} : DialectToExpr (MetaLLVM φ) where
  toExprM := .const ``Id [0]
  toExprDialect := .app (.const ``MetaLLVM []) (Lean.toExpr φ)

instance : Lean.ToExpr (LLVM.Op) := by unfold LLVM; infer_instance
instance : Lean.ToExpr (LLVM.Ty) := by unfold LLVM; infer_instance
instance : DialectToExpr LLVM where
  toExprM := .const ``Id [0]
  toExprDialect := .const ``LLVM []

/-! ### Operation Formatting -/

instance : ToString (MOp φ) where
  toString
  | .poison _   => "poison"
  | .constDense ..  => "constant"
  | .insertelement .. => "insertelement"
  | .shufflevector .. => "shufflevector"
  | .vpmadd52 ..    => "vpmadd52"
  | .vectorBinary _ _ op => toString op
  | .and _      => "and"
  | .or _ _     => "or"
  | .not _      => "not"
  | .xor _      => "xor"
  | .shl _ _    => "shl"
  | .lshr _ _   => "lshr"
  | .ashr _ _   => "ashr"
  | .urem _     => "urem"
  | .srem _     => "srem"
  | .select _   => "select"
  | .add _ _    => "add"
  | .mul _ _    => "mul"
  | .sub _ _    => "sub"
  | .neg _      => "neg"
  | .copy _     => "copy"
  | .freeze _   => "freeze"
  | .trunc _ _ _  => "trunc"
  | .zext _ _ _ => "zext"
  | .sext _ _   => "sext"
  | .sdiv _ _   => "sdiv"
  | .udiv _ _   => "udiv"
  | .icmp ty _  => s!"icmp {ty}"
  | .const _ v  => s!"const {v}"

-- TODO: the `ToString Op` and `ToString MOp` instances have different behaviour;
--       this is not likely to be what we want
-- instance : ToString Op where
--   toString o := repr o |>.pretty

instance : ToString LLVM.Op := by unfold LLVM; infer_instance
instance : Repr LLVM.Op     := by unfold LLVM; infer_instance

instance : ToString LLVM.Ty := by unfold LLVM; infer_instance
instance : Repr LLVM.Ty     := by unfold LLVM; infer_instance

def MetaLLVM.opName : (MetaLLVM φ).Op → String
  | .poison _   => "llvm.mlir.poison"
  | .constDense ..  => "llvm.mlir.constant"
  | .insertelement .. => "llvm.insertelement"
  | .shufflevector .. => "llvm.shufflevector"
  | .vpmadd52 hi _  =>
    if hi then "x86vector.avx512.intr.vpmadd52h.uq.512"
    else "x86vector.avx512.intr.vpmadd52l.uq.512"
  -- NOTE: `toString` on a `BinaryOp` already yields e.g. "llvm.add"
  | .vectorBinary _ _ op => toString op
  | .and _      => "llvm.and"
  | .or _ _     => "llvm.or"
  | .not _      => "llvm.not"
  | .xor _      => "llvm.xor"
  | .shl _ _    => "llvm.shl"
  | .lshr _ _   => "llvm.lshr"
  | .ashr _ _   => "llvm.ashr"
  | .urem _     => "llvm.urem"
  | .srem _     => "llvm.srem"
  | .select _   => "llvm.select"
  | .add _ _    => "llvm.add"
  | .mul _ _    => "llvm.mul"
  | .sub _ _    => "llvm.sub"
  | .neg _      => "llvm.neg"
  | .copy _     => "llvm.copy"
  | .freeze _   => "llvm.freeze"
  | .trunc ..   => "llvm.trunc"
  | .zext ..    => "llvm.zext"
  | .sext _ _   => "llvm.sext"
  | .sdiv _ _   => "llvm.sdiv"
  | .udiv _ _   => "llvm.udiv"
  | .icmp ty _  => s!"llvm.icmp.{ty}"
  | .const _ _  => "llvm.mlir.constant"

def MetaLLVM.printAttributes : (MetaLLVM φ).Op → String
  | .const w v => s!"\{value = {v} : {w}}"
  | .or w ⟨true⟩ => s!"\{disjoint = true : {w}}"
  | .add _ f | .shl _ f | .sub _ f | .mul _ f => printOverflowFlags f
  | .udiv _ ⟨true⟩ | .sdiv _ ⟨true⟩ | .lshr _ ⟨true⟩ => "<{isExact}> "
  | _ => ""
where
  printOverflowFlags : NoWrapFlags → String
  | ⟨false, false⟩ => "<{overflowFlags = #llvm.overflow<none>}>"
  -- TODO: ^^ since this case matches the default, do we even want to print any
  --          flags in this case?
  | ⟨true, false⟩  => "<{overflowFlags = #llvm.overflow<nsw>}>"
  | ⟨false, true⟩  => "<{overflowFlags = #llvm.overflow<nuw>}>"
  | ⟨true, true⟩   => "<{overflowFlags = #llvm.overflow<nsw,nuw>}>"

instance : DialectPrint (MetaLLVM φ) where
  printOpName := MetaLLVM.opName
  printTy := MTy.print
  printAttributes := MetaLLVM.printAttributes
  dialectName := "llvm"
  printReturn _:= "llvm.return"
  printFunc _:= "^bb0"

instance : DialectPrint LLVM := by unfold LLVM; infer_instance

/-! ### Signature -/

@[simp, reducible]
def MOp.sig : MOp φ → List (MTy φ)
| .binary w _ | .icmp _ w =>
  [.bitvec w, .bitvec w]
| .unary w _ => [.bitvec w]
| .select w => [.bitvec 1, .bitvec w, .bitvec w]
| .const _ _ | .poison _ | .constDense _ _ => []
| .insertelement e l w => [.vector l e, e, .bitvec w]
| .shufflevector e l _ => [.vector l e, .vector l e]
| .vpmadd52 _ l =>
  [.vector l (.bitvec 64), .vector l (.bitvec 64), .vector l (.bitvec 64)]
| .vectorBinary l w _ => [.vector l (.bitvec w), .vector l (.bitvec w)]

@[simp, reducible]
def MOp.UnaryOp.outTy (w : Width φ) : MOp.UnaryOp φ → MTy φ
| .trunc w' _ => .bitvec w'
| .zext w' _ => .bitvec w'
| .sext w' => .bitvec w'
| _ => .bitvec w

@[simp, reducible]
def MOp.outTy : MOp φ → MTy φ
| .binary w _ | .select w | .const w _ =>
  .bitvec w
| .unary w op => UnaryOp.outTy w op
| .icmp _ _ => .bitvec 1
| .poison t => t
| .constDense t _ => t
| .insertelement e l _ => .vector l e
| .shufflevector e _ mask => .vector mask.length e
| .vpmadd52 _ l => .vector l (.bitvec 64)
| .vectorBinary l w _ => .vector l (.bitvec w)

instance {φ} : DialectSignature (MetaLLVM φ) where
  signature op := ⟨op.sig, [], [op.outTy], .pure⟩
instance : DialectSignature LLVM where
  signature op := ⟨op.sig, [], [op.outTy], .pure⟩

/-! ### Type Semantics -/

namespace LLVM.Ty

@[match_pattern] abbrev bitvec (w : Nat) : LLVM.Ty :=
  MTy.bitvec (.concrete w)

/-- As for `bitvec`: ascribing `LLVM.Ty` (rather than leaving the `MTy φ` that
`MTy.vector` infers) is what lets instance search find the `LLVM.Ty` instances,
since `LLVM.Ty` is a `Dialect` projection and not reducibly `MTy 0`. -/
@[match_pattern] abbrev vector (l : Nat) (e : LLVM.Ty) : LLVM.Ty :=
  MTy.vector l e

/-- The total number of bits, flattening vectors.

NOTE the multiplication is written `width e * l` rather than `l * width e`.
`Nat.mul` recurses on its *second* argument, so with this order
`width (vector (n+1) e) = width (vector n e) + width e` holds definitionally,
which is what lets `BitVec.packLanes` below build the flat encoding by plain
`BitVec.append` with no `BitVec.cast` anywhere. -/
def width : LLVM.Ty → Nat
  | bitvec w => w
  | vector l e => width e * l

/-- NOTE: this used to be stated for every `ty`, which held while `bitvec` was
the only constructor. It is false for vectors: `width` flattens them, so
`.bitvec (width (.vector 4 (.bitvec 32))) = .bitvec 128 ≠ .vector 4 (.bitvec 32)`. -/
@[simp]
theorem width_eq (w : Nat) : .bitvec (width (.bitvec w)) = LLVM.Ty.bitvec w := rfl

@[simp] -- TODO: this def should not live here
def BitVec.width {n : Nat} (_ : BitVec n) : Nat := n

/-- The denotation of an LLVM type. A vector denotes lane-wise, so poison is
tracked per lane exactly as it is in LLVM: `<4 x i32>` may be poison in one lane
while the others hold values. -/
def denote : LLVM.Ty → Type
  | bitvec w => LLVM.IntW w
  | vector l e => Vector (denote e) l

instance : TyDenote LLVM.Ty where
  toType := denote

@[simp_denote] lemma toType_bitvec : TyDenote.toType (Ty.bitvec w) = LLVM.IntW w := rfl

@[simp_denote] lemma toType_vector (l : Nat) (e : LLVM.Ty) :
    TyDenote.toType (vector l e) = Vector (TyDenote.toType e) l := rfl

/-! ### Flat, in-memory encoding

A value has to become a plain bitvector to be written to memory. LLVM lays a
vector out with lane `0` at the *lowest* address, i.e. in the low bits, and that
is what `flattenBV` produces; `unflatten` reads it back.

Poison is deliberately kept out of the encoding: `Defined` says every scalar
lane holds a value, and only then is there anything to store. `SLLVM`'s memory
model stores fully-defined values only (storing poison raises UB), so this split
is exactly the distinction it needs. -/

/-- Pack `n` lanes of width `we` into one bitvector, lane `0` in the low bits.

There is no `BitVec.cast` here: `width` multiplies as `width e * l` precisely so
that `we * (n+1)` reduces to `we * n + we`, which is the width `append` gives. -/
def _root_.BitVec.packLanes {we : Nat} : {n : Nat} → Vector (BitVec we) n → BitVec (we * n)
  | 0,   _ => 0#(we * 0)
  | _+1, v => BitVec.packLanes v.tail ++ v[0]

/-- Lane `i` of a packed bitvector is the `i`-th input lane. -/
theorem _root_.BitVec.extractLsb'_packLanes {we : Nat} :
    ∀ {n : Nat} (v : Vector (BitVec we) n) (i : Nat) (h : i < n),
      (BitVec.packLanes v).extractLsb' (i * we) we = v[i]
  | 0,   _, _,   h => absurd h (by omega)
  | _+1, v, 0,   _ => by
      simpa [BitVec.packLanes] using
        (BitVec.extractLsb'_append_eq_right (a := BitVec.packLanes v.tail) (b := v[0]))
  | n+1, v, i+1, h => by
      have hi : i < n := by omega
      have key : (BitVec.packLanes v).extractLsb' ((i + 1) * we) we
          = (BitVec.packLanes v.tail).extractLsb' (i * we) we := by
        have hunfold : (BitVec.packLanes v).extractLsb' ((i + 1) * we) we
            = (BitVec.packLanes v.tail ++ v[0]).extractLsb' ((i + 1) * we) we := rfl
        rw [hunfold, show (i + 1) * we = i * we + we from Nat.succ_mul i we,
          BitVec.extractLsb'_append_eq_of_le (Nat.le_add_left we (i * we))]
        congr 1
        omega
      rw [key, BitVec.extractLsb'_packLanes v.tail i hi]
      simp [Nat.add_comm]

/-! `TyDenote.toType (bitvec w)` and `TyDenote.toType (vector l e)` reduce to
`LLVM.IntW w` and `Vector _ l`, but only by unfolding `denote`, which instance
search will not do. These two identity functions put the reduced type in head
position so that `DecidableEq` and `GetElem` are found. -/

@[reducible] def ofBitvec {w : Nat} (x : TyDenote.toType (bitvec w)) : LLVM.IntW w := x
@[reducible] def ofVector {l : Nat} {e : LLVM.Ty} (v : TyDenote.toType (vector l e)) :
    Vector (TyDenote.toType e) l := v

/-- Every scalar lane of the value holds a value rather than poison. -/
def Defined : (t : LLVM.Ty) → TyDenote.toType t → Prop
  | bitvec _, x => ofBitvec x ≠ .poison
  | vector l e, v => ∀ i : Fin l, Defined e (ofVector v)[i]

instance decidableDefined : (t : LLVM.Ty) → (x : TyDenote.toType t) → Decidable (Defined t x)
  | bitvec _, x => inferInstanceAs (Decidable (ofBitvec x ≠ .poison))
  | vector l e, v =>
      have : ∀ i : Fin l, Decidable (Defined e (ofVector v)[i]) :=
        fun i => decidableDefined e _
      inferInstanceAs (Decidable (∀ i : Fin l, Defined e (ofVector v)[i]))

/-- The flat, in-memory bit pattern of a value. A poison lane contributes `0`;
that junk is only ever reachable when `Defined` fails, which is where `flatten`
raises poison instead. -/
def flattenBV : (t : LLVM.Ty) → TyDenote.toType t → BitVec (width t)
  | bitvec _, x => (ofBitvec x).toOption.getD 0
  | vector l e, v =>
      BitVec.packLanes (Vector.ofFn fun (i : Fin l) => flattenBV e (ofVector v)[i])

/-- The flat, in-memory encoding of a value: poison unless every lane is
defined. -/
def flatten (t : LLVM.Ty) (x : TyDenote.toType t) : LLVM.IntW (width t) :=
  if Defined t x then .value (flattenBV t x) else .poison

/-- Read a value of type `t` back out of its flat, in-memory encoding. -/
def unflatten : (t : LLVM.Ty) → BitVec (width t) → TyDenote.toType t
  | bitvec _, x => .value x
  | vector l e, x =>
      Vector.ofFn fun (i : Fin l) => unflatten e (x.extractLsb' (i.val * width e) (width e))

/-- Reading back what was written gives the original value. -/
theorem unflatten_flattenBV : ∀ (t : LLVM.Ty) (x : TyDenote.toType t), Defined t x →
    unflatten t (flattenBV t x) = x
  | bitvec _, x, h => by
      simp only [Defined] at h
      rcases hx : ofBitvec x with _ | b
      · exact absurd hx h
      · show (PoisonOr.value ((ofBitvec x).toOption.getD 0) : LLVM.IntW _) = ofBitvec x
        rw [hx]; rfl
  | vector l e, v, h => by
      simp only [Defined] at h
      show (Vector.ofFn _ : Vector (TyDenote.toType e) l) = ofVector v
      ext i hi
      simp only [flattenBV, Vector.getElem_ofFn]
      rw [BitVec.extractLsb'_packLanes _ i hi, Vector.getElem_ofFn]
      exact unflatten_flattenBV e _ (h ⟨i, hi⟩)

/-- **The layout, pinned down.** Lane `i` of a flattened vector occupies bits
`[i * width e, (i+1) * width e)` -- LLVM's little-endian in-memory order, with
lane `0` lowest.

This does *not* follow from `unflatten_flattenBV`: a store and a load share the
encoding, so any self-consistent lane order round-trips, and the round-trip
theorem would hold just as well with lane `0` in the high bits. What this lemma
adds is agreement with a *differently typed* access to the same bytes -- what a
constant-index `getelementptr`, or a comparison against a C implementation,
depends on. -/
theorem extractLsb'_flattenBV_vector {l : Nat} {e : LLVM.Ty}
    (v : TyDenote.toType (vector l e)) (i : Nat) (h : i < l) :
    (flattenBV (vector l e) v).extractLsb' (i * width e) (width e)
      = flattenBV e ((ofVector v)[i]'h) := by
  rw [flattenBV, BitVec.extractLsb'_packLanes _ i h, Vector.getElem_ofFn]
  rfl

/-- The round trip, in the form the memory model uses it. -/
theorem unflatten_flatten (t : LLVM.Ty) (x : TyDenote.toType t) (b : BitVec (width t))
    (h : flatten t x = .value b) : unflatten t b = x := by
  unfold flatten at h
  split at h
  · rw [← PoisonOr.value_inj.mp h]
    exact unflatten_flattenBV t x ‹_›
  · exact absurd h (PoisonOr.poison_ne_value b)

/-- The poison value at a type; a vector is poison in every lane. -/
def poison : (ty : LLVM.Ty) → TyDenote.toType ty
  | bitvec _ => PoisonOr.poison
  | vector l e => Vector.replicate l (poison e)

/-- The value of a `dense<…>` constant at a type. MLIR writes these either as a
splat (`dense<0>`, one value standing for every lane) or as one value per lane
(`dense<[1, 2, 3]>`); a short list splats its head, a long one is read
positionally. -/
def dense : (ty : LLVM.Ty) → List Int → TyDenote.toType ty
  | bitvec w, vals => .value <| BitVec.ofInt w (vals.headD 0)
  | vector l e, vals =>
      Vector.ofFn fun (i : Fin l) =>
        dense e (match vals with
                 | [v] => [v]
                 | _   => [vals.getD i.val 0])

/-- `llvm.insertelement`. Per LLVM, if the index is poison or out of range the
result is poison -- the whole vector, not just the addressed lane. -/
def insertelement {l : Nat} {e : LLVM.Ty} {w : Nat}
    (v : Vector (TyDenote.toType e) l) (x : TyDenote.toType e) (i : LLVM.IntW w) :
    Vector (TyDenote.toType e) l :=
  match i with
  | .poison => Vector.replicate l (poison e)
  | .value bv =>
      if h : bv.toNat < l then v.set bv.toNat x else Vector.replicate l (poison e)

/-- `llvm.shufflevector`. Mask element `i` indexes the concatenation of the two
operands; LLVM writes a poison lane as a negative mask element. -/
def shufflevector {l : Nat} {e : LLVM.Ty} (mask : List Int)
    (a b : Vector (TyDenote.toType e) l) : Vector (TyDenote.toType e) mask.length :=
  Vector.ofFn fun i =>
    let m := mask.getD i.val (-1)
    if m < 0 then poison e
    else if h : m.toNat < l then a[m.toNat]'h
    else if h' : m.toNat - l < l then b[m.toNat - l]'h'
    else poison e

/-- One lane of the AVX-512 IFMA intrinsics. The unsigned 52-bit low halves of
`b` and `c` are multiplied into a 104-bit product; the low variant adds its low
52 bits to `a`, the high variant adds bits 103:52. -/
def vpmadd52Lane (hi : Bool) : LLVM.IntW 64 → LLVM.IntW 64 → LLVM.IntW 64 → LLVM.IntW 64
  | .value av, .value bv, .value cv =>
      let p := (bv.toNat % 2 ^ 52) * (cv.toNat % 2 ^ 52)
      .value (av + BitVec.ofNat 64 (if hi then p / 2 ^ 52 else p % 2 ^ 52))
  | _, _, _ => .poison

def vpmadd52 {l : Nat} (hi : Bool) (a b c : Vector (LLVM.IntW 64) l) :
    Vector (LLVM.IntW 64) l :=
  Vector.ofFn fun i => vpmadd52Lane hi (a[i.val]'i.isLt) (b[i.val]'i.isLt) (c[i.val]'i.isLt)

/-- Coerce an integer into a type by splatting it across every lane. -/
def ofInt (z : ℤ) : (ty : LLVM.Ty) → TyDenote.toType ty
  | bitvec w => .value <| BitVec.ofInt w z
  | vector l e => Vector.replicate l (ofInt z e)

instance (ty : LLVM.Ty) : Coe ℤ (TyDenote.toType ty) where
  coe z := ofInt z ty

def inhabitant : (ty : LLVM.Ty) → TyDenote.toType ty
  | bitvec _ => (default : LLVM.IntW _)
  | vector l e => Vector.replicate l (inhabitant e)

instance (ty : LLVM.Ty) : Inhabited (TyDenote.toType ty) where
  default := inhabitant ty

-- TODO: this instance should not live here
instance : Repr (BitVec n) where
  reprPrec
    | v, n => reprPrec (BitVec.toInt v) n

end LLVM.Ty

/-! ### Operation Semantics -/

/-- The semantics of a binary operation, shared by the scalar `binary` and the
lane-wise `vectorBinary` so the two cannot drift apart. -/
def binaryDenote {w : Nat} : MOp.BinaryOp → LLVM.IntW w → LLVM.IntW w → LLVM.IntW w
  | .and       => fun x y => LLVM.and x y
  | .or flag   => fun x y => LLVM.or x y flag
  | .xor       => fun x y => LLVM.xor x y
  | .shl fs    => fun x y => LLVM.shl x y fs
  | .lshr flag => fun x y => LLVM.lshr x y flag
  | .ashr flag => fun x y => LLVM.ashr x y flag
  | .urem      => fun x y => LLVM.urem x y
  | .srem      => fun x y => LLVM.srem x y
  | .add fs    => fun x y => LLVM.add x y fs
  | .mul fs    => fun x y => LLVM.mul x y fs
  | .sub fs    => fun x y => LLVM.sub x y fs
  | .sdiv flag => fun x y => LLVM.sdiv x y flag
  | .udiv flag => fun x y => LLVM.udiv x y flag

@[simp]
def Op.denote (o : LLVM.Op) (op : HVector TyDenote.toType (DialectSignature.sig o)) :
    (TyDenote.toType (β := LLVM.Ty) o.outTy) :=
  match o with
  | LLVM.Op.const _ val    => const? _ val
  | LLVM.Op.poison t       => LLVM.Ty.poison t
  | LLVM.Op.constDense t vs => LLVM.Ty.dense t vs
  | LLVM.Op.insertelement _ _ _ =>
      LLVM.Ty.insertelement (op.getN 0 (by simp [DialectSignature.sig, signature]))
                            (op.getN 1 (by simp [DialectSignature.sig, signature]))
                            (op.getN 2 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.shufflevector _ _ mask =>
      LLVM.Ty.shufflevector mask (op.getN 0 (by simp [DialectSignature.sig, signature]))
                                 (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.vectorBinary l w bop =>
      -- the ascriptions force `⟦sig[i]⟧` to reduce to a `Vector`, which is what
      -- lets `GetElem` fire below
      let a : Vector (LLVM.IntW w) l := op.getN 0 (by simp [DialectSignature.sig, signature])
      let b : Vector (LLVM.IntW w) l := op.getN 1 (by simp [DialectSignature.sig, signature])
      Vector.ofFn fun i => binaryDenote bop (a[i.val]'i.isLt) (b[i.val]'i.isLt)
  | LLVM.Op.vpmadd52 hi _ =>
      LLVM.Ty.vpmadd52 hi (op.getN 0 (by simp [DialectSignature.sig, signature]))
                          (op.getN 1 (by simp [DialectSignature.sig, signature]))
                          (op.getN 2 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.copy _         =>               (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.freeze _       => LLVM.freeze   (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.not _          => LLVM.not      (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.neg _          => LLVM.neg      (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.trunc w w'    flags => LLVM.trunc w' (op.getN 0 (by simp [DialectSignature.sig, signature])) flags
  | LLVM.Op.zext w w' flag => LLVM.zext  w' (op.getN 0 (by simp [DialectSignature.sig, signature])) flag
  | LLVM.Op.sext w w'      => LLVM.sext  w' (op.getN 0 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.and _          => LLVM.and      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.or _ flag      => LLVM.or       (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  | LLVM.Op.xor _          => LLVM.xor      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.shl _ flags    => LLVM.shl      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  | LLVM.Op.lshr _ flag    => LLVM.lshr     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  | LLVM.Op.ashr _ flag    => LLVM.ashr     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  | LLVM.Op.sub _ flags    => LLVM.sub      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  | LLVM.Op.add _ flags    => LLVM.add      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  | LLVM.Op.mul _ flags    => LLVM.mul      (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flags
  | LLVM.Op.sdiv _ flag    => LLVM.sdiv     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  | LLVM.Op.udiv _ flag    => LLVM.udiv     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) flag
  | LLVM.Op.urem _         => LLVM.urem     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.srem _         => LLVM.srem     (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.icmp c _       => LLVM.icmp  c  (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature]))
  | LLVM.Op.select _       => LLVM.select   (op.getN 0 (by simp [DialectSignature.sig, signature])) (op.getN 1 (by simp [DialectSignature.sig, signature])) (op.getN 2 (by simp [DialectSignature.sig, signature]))

instance : DialectDenote LLVM := ⟨
  fun o args _ => [Op.denote o args]ₕ
⟩

end InstCombine
