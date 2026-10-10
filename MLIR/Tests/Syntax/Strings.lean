module

public import MLIR.Syntax.Elab
meta import MLIR.Semantics.Func
meta import MLIR.Semantics.GlobalInitializer

/-! # String constants, packed structs, and the syntax of newer imports: symbols with numeric
parts, `distinct` alias scopes, keywords in dialect attributes, an unlabeled entry block -/

namespace MLIR.Tests.Syntax.Strings

@[expose] public section

/-- A string: MLIR's escapes `\XX` and `\\`. -/
mlir_const_def greeting :=
"llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 1 : i64, constant, dso_local, global_type = !llvm.array<6 x i8>, linkage = #llvm.linkage<private>, sym_name = "greeting", unnamed_addr = 2 : i64, value = "\ED\\\22a\00\0A", visibility_ = 0 : i64}> ({
}) : () -> ()

example : greeting.t = .array 6 (.bv 8) := rfl

#guard greeting.lit.toList == [0xED, 0x5C, 0x22, 0x61, 0x00, 0x0A]

/-- rustc's panic `Location`, packed without padding: a file name's address, which the global
holds undefined, then line and column. -/
mlir_const_def location :=
"llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 8 : i64, constant, dso_local, global_type = !llvm.struct<packed (ptr, array<8 x i8>)>, linkage = #llvm.linkage<internal>, sym_name = "anon.042b818bc72209407b52bd0e4d6c8368.10", unnamed_addr = 2 : i64, visibility_ = 0 : i64}> ({
  %0 = "llvm.mlir.constant"() <{value = "W\00\00\00\DD\00\00\00"}> : () -> !llvm.array<8 x i8>
  %1 = "llvm.mlir.addressof"() <{global_name = @anon.042b818bc72209407b52bd0e4d6c8368.9}> : () -> !llvm.ptr
  %2 = "llvm.mlir.undef"() : () -> !llvm.struct<packed (ptr, array<8 x i8>)>
  %3 = "llvm.insertvalue"(%2, %1) <{position = array<i64: 0>}> : (!llvm.struct<packed (ptr, array<8 x i8>)>, !llvm.ptr) -> !llvm.struct<packed (ptr, array<8 x i8>)>
  %4 = "llvm.insertvalue"(%3, %0) <{position = array<i64: 1>}> : (!llvm.struct<packed (ptr, array<8 x i8>)>, !llvm.array<8 x i8>) -> !llvm.struct<packed (ptr, array<8 x i8>)>
  "llvm.return"(%4) : (!llvm.struct<packed (ptr, array<8 x i8>)>) -> ()
}) : () -> ()

example : location.t = .struct [.ptr, .array 8 (.bv 8)] := rfl

/-- sodium's `PAD`, packed bytes. -/
mlir_const_def pad :=
"llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 16 : i64, constant, dso_local, global_type = !llvm.struct<packed (i8, array<3 x i8>)>, linkage = #llvm.linkage<internal>, sym_name = "PAD", unnamed_addr = 2 : i64, visibility_ = 0 : i64}> ({
  %0 = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
  %1 = "llvm.mlir.zero"() : () -> !llvm.array<3 x i8>
  %2 = "llvm.mlir.undef"() : () -> !llvm.struct<packed (i8, array<3 x i8>)>
  %3 = "llvm.insertvalue"(%2, %0) <{position = array<i64: 0>}> : (!llvm.struct<packed (i8, array<3 x i8>)>, i8) -> !llvm.struct<packed (i8, array<3 x i8>)>
  %4 = "llvm.insertvalue"(%3, %1) <{position = array<i64: 1>}> : (!llvm.struct<packed (i8, array<3 x i8>)>, !llvm.array<3 x i8>) -> !llvm.struct<packed (i8, array<3 x i8>)>
  "llvm.return"(%4) : (!llvm.struct<packed (i8, array<3 x i8>)>) -> ()
}) : () -> ()

/-- A newer import's function: alias scopes, `private`, a symbol `anon.….1`, no entry label. -/
mlir_def readGreeting :=
#alias_scope_domain = #llvm.alias_scope_domain<id = distinct[0]<>, description = "readGreeting">
#alias_scope = #llvm.alias_scope<id = distinct[1]<>, domain = #alias_scope_domain, description = "readGreeting: argument 0">
"llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i32 (i64)>, linkage = #llvm.linkage<private>, sym_name = "readGreeting"}> ({
^bb0(%arg0: i64):
  %0 = "llvm.mlir.addressof"() <{global_name = @anon.13b8ab24e6986c1da96f68a50a4d6db2.1}> : () -> !llvm.ptr
  %1 = "llvm.getelementptr"(%0, %arg0) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
  %2 = "llvm.load"(%1) <{alias_scopes = [#alias_scope], alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
  "llvm.return"(%2) : (i32) -> ()
}) : () -> ()
  with @anon.13b8ab24e6986c1da96f68a50a4d6db2.1 := greeting

/-- Byte strings in a function, its entry block unlabeled. -/
mlir_def bytes := {
  %0 = "llvm.mlir.constant"() <{value = "W\00"}> : () -> !llvm.array<2 x i8>
  "llvm.br"()[^bb1] : () -> ()
^bb1:
  "llvm.return"(%0) : (!llvm.array<2 x i8>) -> ()
}

mlir_def readLocation := {
  %0 = "llvm.mlir.addressof"() <{global_name = @anon.042b818bc72209407b52bd0e4d6c8368.10}> : () -> !llvm.ptr
  "llvm.return"(%0) : (!llvm.ptr) -> ()
} with @anon.042b818bc72209407b52bd0e4d6c8368.10 := location

mlir_def readPad := {
  %0 = "llvm.mlir.addressof"() <{global_name = @PAD}> : () -> !llvm.ptr
  %1 = "llvm.load"(%0) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i32
  "llvm.return"(%1) : (i32) -> ()
} with @PAD := pad

end

/-! ## Execution tests -/

section Tests

/-- The four bytes from byte `i` of the greeting, or `none` for UB. -/
private def readGreetingOut (i : BitVec 64) : Option ⟦Ty.bv 32⟧ :=
  match readGreeting.eval 1 (readGreeting.args (.value i)) ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => some v
  | _ => none

#guard readGreetingOut 0 == some (.value 0x61225CED)
#guard readGreetingOut 2 == some (.value 0x0A006122)
#guard readGreetingOut 3 == none

#guard (match bytes.eval 2 .nil ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => v == Ty.wrap (t := .array 2 (.bv 8)) #v[0x57, 0]
  | _ => false)

-- a global holding a pointer: taking its address is UB
#guard (match readLocation.eval 1 .nil ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value _ => false
  | _ => true)

#guard (match readPad.eval 1 .nil ⟨⟨1⟩, ⟨∅⟩⟩ with
  | .value (some (.cons v .nil), _) => v == .value 0x80
  | _ => false)

end Tests

end MLIR.Tests.Syntax.Strings
