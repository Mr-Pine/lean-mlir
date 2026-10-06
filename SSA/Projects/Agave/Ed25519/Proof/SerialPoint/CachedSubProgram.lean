import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Lift

namespace Agave.Ed25519.SerialPoint
open LeanMLIR.RIR
section

/-! Pinned compiler region, with only literal GEP substitution and overflow
flag spelling normalization. These kernels return *completed* coordinates;
`CompletedPoint::as_extended` is a separate four-multiplication operation. -/
mlir_def cached_sub := {
^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
%0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
%1 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
%2 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
%3 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
%4 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
%5 = "llvm.mlir.constant"() <{value = 72 : i64}> : () -> i64
%6 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
%7 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
%8 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
%9 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
%10 = "llvm.mlir.constant"() <{value = 36028797018963664 : i64}> : () -> i64
%11 = "llvm.mlir.constant"() <{value = 36028797018963952 : i64}> : () -> i64
%12 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
%13 = "llvm.mlir.constant"() <{value = 2251799813685247 : i64}> : () -> i64
%14 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
%15 = "llvm.mlir.constant"() <{value = 120 : i64}> : () -> i64
%16 = "llvm.mlir.constant"() <{value = 80 : i64}> : () -> i64
%17 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
%18 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
%19 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
%20 = "llvm.mlir.constant"() <{value = 104 : i64}> : () -> i64
%21 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
%22 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
%23 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
%24 = "llvm.mlir.constant"() <{value = 144 : i64}> : () -> i64
%25 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
%26 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%27 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%28 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%29 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%30 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%31 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
"llvm.intr.lifetime.start"(%31) : (!llvm.ptr) -> ()
%32 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope2}> : () -> ()
%33 = "llvm.load"(%32) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%34 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
%35 = "llvm.load"(%34) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%36 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 56>}> : (!llvm.ptr) -> !llvm.ptr
%37 = "llvm.load"(%36) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%38 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 64>}> : (!llvm.ptr) -> !llvm.ptr
%39 = "llvm.load"(%38) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%40 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 72>}> : (!llvm.ptr) -> !llvm.ptr
%41 = "llvm.load"(%40) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%42 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%43 = "llvm.add"(%42, %33) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%44 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%45 = "llvm.load"(%44) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%46 = "llvm.add"(%45, %35) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%47 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%48 = "llvm.load"(%47) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%49 = "llvm.add"(%48, %37) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%50 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%51 = "llvm.load"(%50) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%52 = "llvm.add"(%51, %39) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%53 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%54 = "llvm.load"(%53) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%55 = "llvm.add"(%54, %41) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
"llvm.store"(%43, %31) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%56 = "llvm.getelementptr"(%31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%46, %56) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%57 = "llvm.getelementptr"(%31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%49, %57) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%58 = "llvm.getelementptr"(%31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%52, %58) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%59 = "llvm.getelementptr"(%31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%55, %59) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
%60 = "llvm.add"(%33, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%61 = "llvm.sub"(%60, %42) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%62 = "llvm.add"(%35, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%63 = "llvm.sub"(%62, %45) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%64 = "llvm.add"(%37, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%65 = "llvm.sub"(%64, %48) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%66 = "llvm.add"(%39, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%67 = "llvm.sub"(%66, %51) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%68 = "llvm.add"(%41, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%69 = "llvm.sub"(%68, %54) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%70 = "llvm.lshr"(%61, %12) : (i64, i64) -> i64
%71 = "llvm.lshr"(%63, %12) : (i64, i64) -> i64
%72 = "llvm.lshr"(%65, %12) : (i64, i64) -> i64
%73 = "llvm.lshr"(%67, %12) : (i64, i64) -> i64
%74 = "llvm.lshr"(%69, %12) : (i64, i64) -> i64
%75 = "llvm.and"(%61, %13) : (i64, i64) -> i64
%76 = "llvm.and"(%63, %13) : (i64, i64) -> i64
%77 = "llvm.and"(%65, %13) : (i64, i64) -> i64
%78 = "llvm.and"(%67, %13) : (i64, i64) -> i64
%79 = "llvm.and"(%69, %13) : (i64, i64) -> i64
%80 = "llvm.mul"(%74, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%81 = "llvm.add"(%80, %75) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%82 = "llvm.add"(%76, %70) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%83 = "llvm.add"(%77, %71) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%84 = "llvm.add"(%78, %72) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%85 = "llvm.add"(%79, %73) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
"llvm.store"(%81, %30) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%86 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%82, %86) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%87 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%83, %87) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%88 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%84, %88) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%89 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%85, %89) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%29) : (!llvm.ptr) -> ()
%90 = "llvm.getelementptr"(%arg2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.call"(%29, %31, %90) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%28) : (!llvm.ptr) -> ()
"llvm.call"(%28, %30, %arg2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
%91 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 120>}> : (!llvm.ptr) -> !llvm.ptr
%92 = "llvm.getelementptr"(%arg2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 120>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.call"(%27, %91, %92) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%26) : (!llvm.ptr) -> ()
%93 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 80>}> : (!llvm.ptr) -> !llvm.ptr
%94 = "llvm.getelementptr"(%arg2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 80>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.call"(%26, %93, %94) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
%95 = "llvm.load"(%26) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%96 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%97 = "llvm.load"(%96) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%98 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%99 = "llvm.load"(%98) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%100 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%101 = "llvm.load"(%100) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%102 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%103 = "llvm.load"(%102) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%104 = "llvm.shl"(%95, %17) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%105 = "llvm.shl"(%97, %17) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%106 = "llvm.shl"(%99, %17) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%107 = "llvm.shl"(%101, %17) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%108 = "llvm.shl"(%103, %17) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope11}> : () -> ()
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope12}> : () -> ()
%109 = "llvm.load"(%29) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%110 = "llvm.add"(%109, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%111 = "llvm.load"(%28) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%112 = "llvm.sub"(%110, %111) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%113 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%114 = "llvm.load"(%113) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%115 = "llvm.add"(%114, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%116 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%117 = "llvm.load"(%116) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%118 = "llvm.sub"(%115, %117) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%119 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%120 = "llvm.load"(%119) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%121 = "llvm.add"(%120, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%122 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%123 = "llvm.load"(%122) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%124 = "llvm.sub"(%121, %123) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%125 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%126 = "llvm.load"(%125) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%127 = "llvm.add"(%126, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%128 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%129 = "llvm.load"(%128) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%130 = "llvm.sub"(%127, %129) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%131 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%132 = "llvm.load"(%131) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%133 = "llvm.add"(%132, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%134 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%135 = "llvm.load"(%134) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%136 = "llvm.sub"(%133, %135) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%137 = "llvm.lshr"(%112, %12) : (i64, i64) -> i64
%138 = "llvm.lshr"(%118, %12) : (i64, i64) -> i64
%139 = "llvm.lshr"(%124, %12) : (i64, i64) -> i64
%140 = "llvm.lshr"(%130, %12) : (i64, i64) -> i64
%141 = "llvm.lshr"(%136, %12) : (i64, i64) -> i64
%142 = "llvm.and"(%112, %13) : (i64, i64) -> i64
%143 = "llvm.and"(%118, %13) : (i64, i64) -> i64
%144 = "llvm.and"(%124, %13) : (i64, i64) -> i64
%145 = "llvm.and"(%130, %13) : (i64, i64) -> i64
%146 = "llvm.and"(%136, %13) : (i64, i64) -> i64
%147 = "llvm.mul"(%141, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%148 = "llvm.add"(%147, %142) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%149 = "llvm.add"(%143, %137) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%150 = "llvm.add"(%144, %138) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%151 = "llvm.add"(%145, %139) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%152 = "llvm.add"(%146, %140) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%153 = "llvm.add"(%111, %109) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%154 = "llvm.add"(%117, %114) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%155 = "llvm.add"(%123, %120) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%156 = "llvm.add"(%129, %126) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%157 = "llvm.add"(%135, %132) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%158 = "llvm.add"(%104, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%159 = "llvm.load"(%27) <{alias_scopes = [#alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope16], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%160 = "llvm.sub"(%158, %159) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%161 = "llvm.add"(%105, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%162 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%163 = "llvm.load"(%162) <{alias_scopes = [#alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope16], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%164 = "llvm.sub"(%161, %163) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%165 = "llvm.add"(%106, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%166 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%167 = "llvm.load"(%166) <{alias_scopes = [#alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope16], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%168 = "llvm.sub"(%165, %167) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%169 = "llvm.add"(%107, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%170 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%171 = "llvm.load"(%170) <{alias_scopes = [#alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope16], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%172 = "llvm.sub"(%169, %171) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%173 = "llvm.add"(%108, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%174 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%175 = "llvm.load"(%174) <{alias_scopes = [#alias_scope14], alignment = 8 : i64, noalias_scopes = [#alias_scope15, #alias_scope16], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%176 = "llvm.sub"(%173, %175) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%177 = "llvm.lshr"(%160, %12) : (i64, i64) -> i64
%178 = "llvm.lshr"(%164, %12) : (i64, i64) -> i64
%179 = "llvm.lshr"(%168, %12) : (i64, i64) -> i64
%180 = "llvm.lshr"(%172, %12) : (i64, i64) -> i64
%181 = "llvm.lshr"(%176, %12) : (i64, i64) -> i64
%182 = "llvm.and"(%160, %13) : (i64, i64) -> i64
%183 = "llvm.and"(%164, %13) : (i64, i64) -> i64
%184 = "llvm.and"(%168, %13) : (i64, i64) -> i64
%185 = "llvm.and"(%172, %13) : (i64, i64) -> i64
%186 = "llvm.and"(%176, %13) : (i64, i64) -> i64
%187 = "llvm.mul"(%181, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%188 = "llvm.add"(%187, %182) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%189 = "llvm.add"(%183, %177) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%190 = "llvm.add"(%184, %178) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%191 = "llvm.add"(%185, %179) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%192 = "llvm.add"(%186, %180) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%193 = "llvm.add"(%159, %104) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%194 = "llvm.add"(%163, %105) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%195 = "llvm.add"(%167, %106) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%196 = "llvm.add"(%171, %107) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%197 = "llvm.add"(%175, %108) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
"llvm.store"(%148, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%198 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%149, %198) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%199 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%150, %199) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%200 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%151, %200) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%201 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%152, %201) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%202 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%153, %202) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%203 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%154, %203) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%204 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 56>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%155, %204) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%205 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 64>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%156, %205) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%206 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 72>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%157, %206) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%207 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 80>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%188, %207) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%208 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 88>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%189, %208) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%209 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 96>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%190, %209) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%210 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 104>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%191, %210) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%211 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 112>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%192, %211) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%212 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 120>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%193, %212) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%213 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 128>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%194, %213) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%214 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 136>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%195, %214) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%215 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 144>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%196, %215) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%216 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 152>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%197, %216) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%26) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%28) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%29) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%31) : (!llvm.ptr) -> ()
"llvm.return"() : () -> ()
} with @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul := SerialFieldMul.kernel

end
end Agave.Ed25519.SerialPoint
