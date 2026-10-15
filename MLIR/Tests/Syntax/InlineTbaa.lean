module

public import MLIR.Syntax.Elab

/-! # TBAA tags written inline: accepted, then ignored -/

namespace MLIR.Tests.Syntax.InlineTbaa

@[expose] public section

mlir_def load_char := "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i8 (ptr)>, linkage = #llvm.linkage<external>, sym_name = "load_char", visibility_ = 0 : i64}> ({
^bb0(%arg0: !llvm.ptr):
  %0 = "llvm.load"(%arg0) <{alignment = 1 : i64, ordering = 0 : i64, tbaa = [#llvm.tbaa_tag<base_type = <id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, access_type = <id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, offset = 0>]}> : (!llvm.ptr) -> i8
  "llvm.return"(%0) : (i8) -> ()
}) : () -> ()

/-- A struct's descriptor nests member descriptors: `{<<id = …>, 0>, …}`. -/
mlir_def store_field := "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<void (ptr, i64)>, linkage = #llvm.linkage<external>, sym_name = "store_field", visibility_ = 0 : i64}> ({
^bb0(%arg0: !llvm.ptr, %arg1: i64):
  "llvm.store"(%arg1, %arg0) <{alignment = 8 : i64, ordering = 0 : i64, tbaa = [#llvm.tbaa_tag<base_type = <id = "pair", members = {<<id = "long", members = {<<id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, 0>}>, 0>, <<id = "long", members = {<<id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, 0>}>, 8>}>, access_type = <id = "long", members = {<<id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, 0>}>, offset = 0>]}> : (i64, !llvm.ptr) -> ()
  "llvm.return"() : () -> ()
}) : () -> ()

/-- A `memcpy`'s TBAA tag. -/
mlir_def copy_char := "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<void (ptr, ptr)>, linkage = #llvm.linkage<external>, sym_name = "copy_char", visibility_ = 0 : i64}> ({
^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
  %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  "llvm.intr.memcpy"(%arg0, %arg1, %0) <{isVolatile = false, tbaa = [#llvm.tbaa_tag<base_type = <id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, access_type = <id = "omnipotent char", members = {<#llvm.tbaa_root<id = "Simple C/C++ TBAA">, 0>}>, offset = 0>]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
  "llvm.return"() : () -> ()
}) : () -> ()

end

end MLIR.Tests.Syntax.InlineTbaa
