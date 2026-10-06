import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Lift

namespace Agave.Ed25519.SerialPoint
open LeanMLIR.RIR
section

/-! Pinned compiler region, with only literal GEP substitution and overflow
flag spelling normalization. These kernels return *completed* coordinates;
`CompletedPoint::as_extended` is a separate four-multiplication operation. -/
mlir_def affine_add := {
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
%17 = "llvm.mlir.constant"() <{value = 88 : i64}> : () -> i64
%18 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
%19 = "llvm.mlir.constant"() <{value = 104 : i64}> : () -> i64
%20 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
%21 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
%22 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
%23 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
%24 = "llvm.mlir.constant"() <{value = 144 : i64}> : () -> i64
%25 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
%26 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%27 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%28 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%29 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
%30 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
"llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
%31 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope2}> : () -> ()
%32 = "llvm.load"(%31) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%33 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
%34 = "llvm.load"(%33) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%35 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 56>}> : (!llvm.ptr) -> !llvm.ptr
%36 = "llvm.load"(%35) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%37 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 64>}> : (!llvm.ptr) -> !llvm.ptr
%38 = "llvm.load"(%37) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%39 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 72>}> : (!llvm.ptr) -> !llvm.ptr
%40 = "llvm.load"(%39) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%41 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%42 = "llvm.add"(%41, %32) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%43 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%44 = "llvm.load"(%43) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%45 = "llvm.add"(%44, %34) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%46 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%47 = "llvm.load"(%46) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%48 = "llvm.add"(%47, %36) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%49 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%50 = "llvm.load"(%49) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%51 = "llvm.add"(%50, %38) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%52 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%53 = "llvm.load"(%52) <{alias_scopes = [#alias_scope3, #alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%54 = "llvm.add"(%53, %40) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
"llvm.store"(%42, %30) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%55 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%45, %55) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%56 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%48, %56) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%57 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%51, %57) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%58 = "llvm.getelementptr"(%30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%54, %58) <{alias_scopes = [#alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%29) : (!llvm.ptr) -> ()
%59 = "llvm.add"(%32, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%60 = "llvm.sub"(%59, %41) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%61 = "llvm.add"(%34, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%62 = "llvm.sub"(%61, %44) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%63 = "llvm.add"(%36, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%64 = "llvm.sub"(%63, %47) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%65 = "llvm.add"(%38, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%66 = "llvm.sub"(%65, %50) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%67 = "llvm.add"(%40, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%68 = "llvm.sub"(%67, %53) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%69 = "llvm.lshr"(%60, %12) : (i64, i64) -> i64
%70 = "llvm.lshr"(%62, %12) : (i64, i64) -> i64
%71 = "llvm.lshr"(%64, %12) : (i64, i64) -> i64
%72 = "llvm.lshr"(%66, %12) : (i64, i64) -> i64
%73 = "llvm.lshr"(%68, %12) : (i64, i64) -> i64
%74 = "llvm.and"(%60, %13) : (i64, i64) -> i64
%75 = "llvm.and"(%62, %13) : (i64, i64) -> i64
%76 = "llvm.and"(%64, %13) : (i64, i64) -> i64
%77 = "llvm.and"(%66, %13) : (i64, i64) -> i64
%78 = "llvm.and"(%68, %13) : (i64, i64) -> i64
%79 = "llvm.mul"(%73, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%80 = "llvm.add"(%79, %74) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%81 = "llvm.add"(%75, %69) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%82 = "llvm.add"(%76, %70) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%83 = "llvm.add"(%77, %71) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%84 = "llvm.add"(%78, %72) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
"llvm.store"(%80, %29) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%85 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%81, %85) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%86 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%82, %86) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%87 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%83, %87) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%88 = "llvm.getelementptr"(%29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%84, %88) <{alias_scopes = [#alias_scope5], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%28) : (!llvm.ptr) -> ()
"llvm.call"(%28, %30, %arg2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
%89 = "llvm.getelementptr"(%arg2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.call"(%27, %29, %89) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
"llvm.intr.lifetime.start"(%26) : (!llvm.ptr) -> ()
%90 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 120>}> : (!llvm.ptr) -> !llvm.ptr
%91 = "llvm.getelementptr"(%arg2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 80>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.call"(%26, %90, %91) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<40 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
%92 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 80>}> : (!llvm.ptr) -> !llvm.ptr
%93 = "llvm.load"(%92) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%94 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 88>}> : (!llvm.ptr) -> !llvm.ptr
%95 = "llvm.load"(%94) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%96 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 96>}> : (!llvm.ptr) -> !llvm.ptr
%97 = "llvm.load"(%96) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%98 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 104>}> : (!llvm.ptr) -> !llvm.ptr
%99 = "llvm.load"(%98) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%100 = "llvm.getelementptr"(%arg1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 112>}> : (!llvm.ptr) -> !llvm.ptr
%101 = "llvm.load"(%100) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope10], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%102 = "llvm.shl"(%93, %21) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%103 = "llvm.shl"(%95, %21) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%104 = "llvm.shl"(%97, %21) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%105 = "llvm.shl"(%99, %21) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%106 = "llvm.shl"(%101, %21) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope11}> : () -> ()
"llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope12}> : () -> ()
%107 = "llvm.load"(%28) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%108 = "llvm.add"(%107, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%109 = "llvm.load"(%27) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%110 = "llvm.sub"(%108, %109) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%111 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%112 = "llvm.load"(%111) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%113 = "llvm.add"(%112, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%114 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%115 = "llvm.load"(%114) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%116 = "llvm.sub"(%113, %115) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%117 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%118 = "llvm.load"(%117) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%119 = "llvm.add"(%118, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%120 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%121 = "llvm.load"(%120) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%122 = "llvm.sub"(%119, %121) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%123 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%124 = "llvm.load"(%123) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%125 = "llvm.add"(%124, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%126 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%127 = "llvm.load"(%126) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%128 = "llvm.sub"(%125, %127) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%129 = "llvm.getelementptr"(%28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%130 = "llvm.load"(%129) <{alias_scopes = [#alias_scope11], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope12], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%131 = "llvm.add"(%130, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%132 = "llvm.getelementptr"(%27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%133 = "llvm.load"(%132) <{alias_scopes = [#alias_scope12], alignment = 8 : i64, noalias_scopes = [#alias_scope13, #alias_scope11], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%134 = "llvm.sub"(%131, %133) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%135 = "llvm.lshr"(%110, %12) : (i64, i64) -> i64
%136 = "llvm.lshr"(%116, %12) : (i64, i64) -> i64
%137 = "llvm.lshr"(%122, %12) : (i64, i64) -> i64
%138 = "llvm.lshr"(%128, %12) : (i64, i64) -> i64
%139 = "llvm.lshr"(%134, %12) : (i64, i64) -> i64
%140 = "llvm.and"(%110, %13) : (i64, i64) -> i64
%141 = "llvm.and"(%116, %13) : (i64, i64) -> i64
%142 = "llvm.and"(%122, %13) : (i64, i64) -> i64
%143 = "llvm.and"(%128, %13) : (i64, i64) -> i64
%144 = "llvm.and"(%134, %13) : (i64, i64) -> i64
%145 = "llvm.mul"(%139, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%146 = "llvm.add"(%145, %140) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%147 = "llvm.add"(%141, %135) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%148 = "llvm.add"(%142, %136) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%149 = "llvm.add"(%143, %137) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%150 = "llvm.add"(%144, %138) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%151 = "llvm.add"(%109, %107) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%152 = "llvm.add"(%115, %112) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%153 = "llvm.add"(%121, %118) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%154 = "llvm.add"(%127, %124) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%155 = "llvm.add"(%133, %130) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%156 = "llvm.load"(%26) <{alias_scopes = [#alias_scope14, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%157 = "llvm.add"(%156, %102) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%158 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
%159 = "llvm.load"(%158) <{alias_scopes = [#alias_scope14, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%160 = "llvm.add"(%159, %103) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%161 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
%162 = "llvm.load"(%161) <{alias_scopes = [#alias_scope14, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%163 = "llvm.add"(%162, %104) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%164 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
%165 = "llvm.load"(%164) <{alias_scopes = [#alias_scope14, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%166 = "llvm.add"(%165, %105) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%167 = "llvm.getelementptr"(%26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
%168 = "llvm.load"(%167) <{alias_scopes = [#alias_scope14, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18], ordering = 0 : i64}> : (!llvm.ptr) -> i64
%169 = "llvm.add"(%168, %106) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%170 = "llvm.add"(%102, %10) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%171 = "llvm.sub"(%170, %156) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%172 = "llvm.add"(%103, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%173 = "llvm.sub"(%172, %159) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%174 = "llvm.add"(%104, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%175 = "llvm.sub"(%174, %162) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%176 = "llvm.add"(%105, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%177 = "llvm.sub"(%176, %165) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%178 = "llvm.add"(%106, %11) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%179 = "llvm.sub"(%178, %168) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
%180 = "llvm.lshr"(%171, %12) : (i64, i64) -> i64
%181 = "llvm.lshr"(%173, %12) : (i64, i64) -> i64
%182 = "llvm.lshr"(%175, %12) : (i64, i64) -> i64
%183 = "llvm.lshr"(%177, %12) : (i64, i64) -> i64
%184 = "llvm.lshr"(%179, %12) : (i64, i64) -> i64
%185 = "llvm.and"(%171, %13) : (i64, i64) -> i64
%186 = "llvm.and"(%173, %13) : (i64, i64) -> i64
%187 = "llvm.and"(%175, %13) : (i64, i64) -> i64
%188 = "llvm.and"(%177, %13) : (i64, i64) -> i64
%189 = "llvm.and"(%179, %13) : (i64, i64) -> i64
%190 = "llvm.mul"(%184, %14) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%191 = "llvm.add"(%190, %185) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%192 = "llvm.add"(%186, %180) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%193 = "llvm.add"(%187, %181) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%194 = "llvm.add"(%188, %182) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
%195 = "llvm.add"(%189, %183) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i64, i64) -> i64
"llvm.store"(%146, %arg0) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%196 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 8>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%147, %196) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%197 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 16>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%148, %197) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%198 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 24>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%149, %198) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%199 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 32>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%150, %199) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%200 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 40>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%151, %200) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%201 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 48>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%152, %201) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%202 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 56>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%153, %202) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%203 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 64>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%154, %203) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%204 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 72>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%155, %204) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%205 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 80>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%157, %205) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%206 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 88>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%160, %206) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%207 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 96>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%163, %207) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%208 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 104>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%166, %208) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%209 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 112>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%169, %209) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%210 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 120>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%191, %210) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%211 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 128>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%192, %211) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%212 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 136>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%193, %212) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%213 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 144>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%194, %213) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
%214 = "llvm.getelementptr"(%arg0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: 152>}> : (!llvm.ptr) -> !llvm.ptr
"llvm.store"(%195, %214) <{alignment = 8 : i64, ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%26) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%28) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%29) : (!llvm.ptr) -> ()
"llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
"llvm.return"() : () -> ()
} with @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul := SerialFieldMul.kernel

end
end Agave.Ed25519.SerialPoint
