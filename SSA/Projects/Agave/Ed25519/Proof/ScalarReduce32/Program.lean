module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab
public import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBoxProgram

/-!
Exact pinned 32-byte scalar reduction body. Regenerate with
`MLIR/import_scalar_reduce32.py`. This is the callee of Dalek.scalarReduce,
not base-field Reduce64 and not the wide SHA-512 scalar reduction.

All source instructions and flags are retained; the sole external call is
linked to its independently imported black_box body. Import success alone
does not prove the arithmetic result, absence of poison, or memory frame.
-/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
@[expose] public section

def sourceSymbol : String := "_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar6reduce"

execution_def program :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 4503599627370495 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 4302102966953709 : i128}> : () -> i128
    %25 = "llvm.mlir.constant"() <{value = 1049714374468698 : i128}> : () -> i128
    %26 = "llvm.mlir.constant"() <{value = 4503599278581019 : i128}> : () -> i128
    %27 = "llvm.mlir.constant"() <{value = 4503599627370495 : i128}> : () -> i128
    %28 = "llvm.mlir.constant"() <{value = 17592186044415 : i128}> : () -> i128
    %29 = "llvm.mlir.constant"() <{value = 1439961107955227 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 671914833335277 : i128}> : () -> i128
    %31 = "llvm.mlir.constant"() <{value = 52 : i128}> : () -> i128
    %32 = "llvm.mlir.constant"() <{value = 3916664325105025 : i128}> : () -> i128
    %33 = "llvm.mlir.constant"() <{value = 1367801 : i128}> : () -> i128
    %34 = "llvm.mlir.constant"() <{value = 44 : i128}> : () -> i128
    %35 = "llvm.mlir.constant"() <{value = -671914833335277 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = -3916664325105025 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = -1367801 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = -17592186044416 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 671914833335277 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 3916664325105025 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 1367801 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 17592186044416 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %47 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %48 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %49 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %50 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %51 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %52 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %53 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %54 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %55 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %56 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %57 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %58 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %59 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %60 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %61 = "llvm.mlir.constant"() <{value = 0 : i128}> : () -> i128
    %62 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %63 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %64 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %65 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %66 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %67 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %68 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %69 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %70 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %71 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %72 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %73 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %74 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %75 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %76 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %77 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %78 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %79 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %80 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %81 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %82 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %83 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %84 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %85 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %86 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %87 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %88 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %89 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %90 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %91 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %92 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %93 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %94 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%90) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%91) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%92) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%93) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%94) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    "llvm.intr.lifetime.start"(%72) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%73) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%74) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%75) : (!llvm.ptr) -> ()
    %95 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %96 = "llvm.zext"(%95) : (i32) -> i64
    %97 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %98 = "llvm.load"(%97) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %99 = "llvm.zext"(%98) : (i8) -> i64
    %100 = "llvm.shl"(%99, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %101 = "llvm.or"(%100, %96) <{isDisjoint}> : (i64, i64) -> i64
    %102 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %103 = "llvm.load"(%102) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %104 = "llvm.zext"(%103) : (i8) -> i64
    %105 = "llvm.shl"(%104, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %106 = "llvm.or"(%101, %105) <{isDisjoint}> : (i64, i64) -> i64
    %107 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %108 = "llvm.load"(%107) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %109 = "llvm.zext"(%108) : (i8) -> i64
    %110 = "llvm.shl"(%109, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %111 = "llvm.or"(%106, %110) <{isDisjoint}> : (i64, i64) -> i64
    %112 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %113 = "llvm.load"(%112) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %114 = "llvm.zext"(%113) : (i8) -> i64
    %115 = "llvm.shl"(%114, %8) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %116 = "llvm.or"(%115, %111) <{isDisjoint}> : (i64, i64) -> i64
    %117 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %118 = "llvm.load"(%117) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %119 = "llvm.zext"(%118) : (i32) -> i64
    %120 = "llvm.getelementptr"(%arg1, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %121 = "llvm.load"(%120) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %122 = "llvm.zext"(%121) : (i8) -> i64
    %123 = "llvm.shl"(%122, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %124 = "llvm.or"(%123, %119) <{isDisjoint}> : (i64, i64) -> i64
    %125 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %126 = "llvm.load"(%125) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %127 = "llvm.zext"(%126) : (i8) -> i64
    %128 = "llvm.shl"(%127, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %129 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %130 = "llvm.load"(%129) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %131 = "llvm.zext"(%130) : (i16) -> i64
    %132 = "llvm.shl"(%131, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %133 = "llvm.or"(%132, %128) <{isDisjoint}> : (i64, i64) -> i64
    %134 = "llvm.or"(%133, %124) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%134, %73) <{alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %135 = "llvm.getelementptr"(%arg1, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %136 = "llvm.load"(%135) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %137 = "llvm.zext"(%136) : (i16) -> i64
    %138 = "llvm.getelementptr"(%arg1, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %139 = "llvm.load"(%138) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %140 = "llvm.zext"(%139) : (i8) -> i64
    %141 = "llvm.shl"(%140, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %142 = "llvm.or"(%141, %137) <{isDisjoint}> : (i64, i64) -> i64
    %143 = "llvm.getelementptr"(%arg1, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %144 = "llvm.load"(%143) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %145 = "llvm.zext"(%144) : (i8) -> i64
    %146 = "llvm.shl"(%145, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %147 = "llvm.or"(%142, %146) <{isDisjoint}> : (i64, i64) -> i64
    %148 = "llvm.getelementptr"(%arg1, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %149 = "llvm.load"(%148) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %150 = "llvm.zext"(%149) : (i32) -> i64
    %151 = "llvm.shl"(%150, %2) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %152 = "llvm.or"(%151, %147) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%152, %74) <{alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %153 = "llvm.getelementptr"(%arg1, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %154 = "llvm.load"(%153) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %155 = "llvm.zext"(%154) : (i8) -> i64
    %156 = "llvm.getelementptr"(%arg1, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %157 = "llvm.load"(%156) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %158 = "llvm.zext"(%157) : (i8) -> i64
    %159 = "llvm.shl"(%158, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %160 = "llvm.or"(%159, %155) <{isDisjoint}> : (i64, i64) -> i64
    %161 = "llvm.getelementptr"(%arg1, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %162 = "llvm.load"(%161) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %163 = "llvm.zext"(%162) : (i32) -> i64
    %164 = "llvm.shl"(%163, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %165 = "llvm.getelementptr"(%arg1, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %166 = "llvm.load"(%165) <{alias_scopes = [#alias_scope1, #alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %167 = "llvm.zext"(%166) : (i16) -> i64
    %168 = "llvm.shl"(%167, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %169 = "llvm.or"(%168, %164) <{isDisjoint}> : (i64, i64) -> i64
    %170 = "llvm.or"(%169, %160) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%170, %75) <{alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %72) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%21, %73) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%21, %74) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%21, %75) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope2, #alias_scope1, #alias_scope3, #alias_scope], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %171 = "llvm.lshr"(%169, %13) <{isExact}> : (i64, i64) -> i64
    %172 = "llvm.intr.fshl"(%160, %152, %22) : (i64, i64, i64) -> i64
    %173 = "llvm.intr.fshl"(%147, %133, %16) : (i64, i64, i64) -> i64
    %174 = "llvm.and"(%173, %23) : (i64, i64) -> i64
    %175 = "llvm.intr.fshl"(%124, %116, %10) : (i64, i64, i64) -> i64
    %176 = "llvm.and"(%111, %23) : (i64, i64) -> i64
    "llvm.intr.lifetime.end"(%72) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%73) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%74) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%75) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%81) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%82) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%83) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%84) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%85) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%86) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%87) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%88) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%89) : (!llvm.ptr) -> ()
    %177 = "llvm.zext"(%176) <{nonNeg}> : (i64) -> i128
    %178 = "llvm.mul"(%177, %24) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%178, %81) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %179 = "llvm.mul"(%177, %25) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %180 = "llvm.zext"(%175) <{nonNeg}> : (i64) -> i128
    %181 = "llvm.mul"(%180, %24) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %182 = "llvm.add"(%181, %179) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%182, %82) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %183 = "llvm.mul"(%177, %26) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %184 = "llvm.mul"(%180, %25) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %185 = "llvm.add"(%184, %183) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %186 = "llvm.zext"(%174) <{nonNeg}> : (i64) -> i128
    %187 = "llvm.mul"(%186, %24) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %188 = "llvm.add"(%185, %187) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%188, %83) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %189 = "llvm.mul"(%177, %27) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %190 = "llvm.mul"(%180, %26) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %191 = "llvm.add"(%190, %189) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %192 = "llvm.mul"(%186, %25) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %193 = "llvm.add"(%191, %192) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %194 = "llvm.zext"(%172) <{nonNeg}> : (i64) -> i128
    %195 = "llvm.mul"(%194, %24) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %196 = "llvm.add"(%193, %195) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%196, %84) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %197 = "llvm.mul"(%177, %28) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %198 = "llvm.mul"(%180, %27) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %199 = "llvm.add"(%198, %197) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %200 = "llvm.mul"(%186, %26) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %201 = "llvm.add"(%199, %200) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %202 = "llvm.mul"(%194, %25) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %203 = "llvm.add"(%201, %202) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %204 = "llvm.zext"(%171) <{nonNeg}> : (i64) -> i128
    %205 = "llvm.mul"(%204, %24) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %206 = "llvm.add"(%203, %205) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%206, %85) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %207 = "llvm.mul"(%180, %28) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %208 = "llvm.mul"(%186, %27) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %209 = "llvm.add"(%208, %207) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %210 = "llvm.mul"(%194, %26) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %211 = "llvm.add"(%209, %210) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %212 = "llvm.mul"(%204, %25) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %213 = "llvm.add"(%211, %212) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%213, %86) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %214 = "llvm.mul"(%186, %28) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %215 = "llvm.mul"(%194, %27) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %216 = "llvm.add"(%215, %214) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %217 = "llvm.mul"(%204, %26) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %218 = "llvm.add"(%216, %217) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%218, %87) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %219 = "llvm.mul"(%194, %28) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %220 = "llvm.mul"(%204, %27) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %221 = "llvm.add"(%220, %219) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%221, %88) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %222 = "llvm.mul"(%204, %28) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    "llvm.store"(%222, %89) <{alias_scopes = [#alias_scope6], alignment = 16 : i64, noalias_scopes = [#alias_scope7, #alias_scope8], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%76) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%77) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%78) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%79) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%80) : (!llvm.ptr) -> ()
    %223 = "llvm.trunc"(%178) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %224 = "llvm.mul"(%223, %29) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %225 = "llvm.and"(%224, %23) : (i64, i64) -> i64
    %226 = "llvm.zext"(%225) <{nonNeg}> : (i64) -> i128
    %227 = "llvm.mul"(%226, %30) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %228 = "llvm.add"(%227, %178) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %229 = "llvm.lshr"(%228, %31) : (i128, i128) -> i128
    %230 = "llvm.mul"(%226, %32) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %231 = "llvm.add"(%230, %182) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %232 = "llvm.add"(%231, %229) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %233 = "llvm.trunc"(%232) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %234 = "llvm.mul"(%233, %29) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %235 = "llvm.and"(%234, %23) : (i64, i64) -> i64
    %236 = "llvm.zext"(%235) <{nonNeg}> : (i64) -> i128
    %237 = "llvm.mul"(%236, %30) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %238 = "llvm.add"(%237, %232) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %239 = "llvm.lshr"(%238, %31) : (i128, i128) -> i128
    %240 = "llvm.mul"(%226, %33) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %241 = "llvm.mul"(%236, %32) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %242 = "llvm.add"(%188, %240) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %243 = "llvm.add"(%242, %241) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %244 = "llvm.add"(%243, %239) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %245 = "llvm.trunc"(%244) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %246 = "llvm.mul"(%245, %29) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %247 = "llvm.and"(%246, %23) : (i64, i64) -> i64
    %248 = "llvm.zext"(%247) <{nonNeg}> : (i64) -> i128
    %249 = "llvm.mul"(%248, %30) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %250 = "llvm.add"(%249, %244) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %251 = "llvm.lshr"(%250, %31) : (i128, i128) -> i128
    %252 = "llvm.mul"(%236, %33) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %253 = "llvm.mul"(%248, %32) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %254 = "llvm.add"(%252, %196) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %255 = "llvm.add"(%254, %253) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %256 = "llvm.add"(%255, %251) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %257 = "llvm.trunc"(%256) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %258 = "llvm.mul"(%257, %29) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %259 = "llvm.and"(%258, %23) : (i64, i64) -> i64
    %260 = "llvm.zext"(%259) <{nonNeg}> : (i64) -> i128
    %261 = "llvm.mul"(%260, %30) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %262 = "llvm.add"(%261, %256) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %263 = "llvm.lshr"(%262, %31) : (i128, i128) -> i128
    %264 = "llvm.shl"(%226, %34) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %265 = "llvm.mul"(%248, %33) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %266 = "llvm.mul"(%260, %32) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %267 = "llvm.add"(%206, %264) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %268 = "llvm.add"(%267, %265) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %269 = "llvm.add"(%268, %266) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %270 = "llvm.add"(%269, %263) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %271 = "llvm.trunc"(%270) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %272 = "llvm.mul"(%271, %29) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %273 = "llvm.and"(%272, %23) : (i64, i64) -> i64
    %274 = "llvm.zext"(%273) <{nonNeg}> : (i64) -> i128
    %275 = "llvm.mul"(%274, %30) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %276 = "llvm.add"(%275, %270) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %277 = "llvm.lshr"(%276, %31) : (i128, i128) -> i128
    %278 = "llvm.shl"(%236, %34) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %279 = "llvm.mul"(%260, %33) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %280 = "llvm.mul"(%274, %32) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %281 = "llvm.add"(%213, %278) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %282 = "llvm.add"(%281, %279) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %283 = "llvm.add"(%282, %280) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %284 = "llvm.add"(%283, %277) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %285 = "llvm.trunc"(%284) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %286 = "llvm.and"(%285, %23) : (i64, i64) -> i64
    %287 = "llvm.lshr"(%284, %31) : (i128, i128) -> i128
    %288 = "llvm.shl"(%248, %34) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %289 = "llvm.mul"(%274, %33) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %290 = "llvm.add"(%288, %218) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %291 = "llvm.add"(%290, %289) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %292 = "llvm.add"(%291, %287) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %293 = "llvm.trunc"(%292) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %294 = "llvm.and"(%293, %23) : (i64, i64) -> i64
    %295 = "llvm.lshr"(%292, %31) : (i128, i128) -> i128
    %296 = "llvm.shl"(%260, %34) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %297 = "llvm.add"(%296, %221) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %298 = "llvm.add"(%297, %295) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %299 = "llvm.trunc"(%298) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %300 = "llvm.and"(%299, %23) : (i64, i64) -> i64
    %301 = "llvm.lshr"(%298, %31) : (i128, i128) -> i128
    %302 = "llvm.shl"(%274, %34) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %303 = "llvm.add"(%302, %222) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %304 = "llvm.add"(%303, %301) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %305 = "llvm.trunc"(%304) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %306 = "llvm.and"(%305, %23) : (i64, i64) -> i64
    %307 = "llvm.lshr"(%304, %31) : (i128, i128) -> i128
    %308 = "llvm.trunc"(%307) <{overflowFlags = 3 : i32}> : (i128) -> i64
    %309 = "llvm.add"(%286, %35) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %310 = "llvm.and"(%309, %23) : (i64, i64) -> i64
    %311 = "llvm.ashr"(%309, %36) : (i64, i64) -> i64
    %312 = "llvm.add"(%311, %37) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %313 = "llvm.add"(%312, %294) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %314 = "llvm.and"(%313, %23) : (i64, i64) -> i64
    %315 = "llvm.ashr"(%313, %36) : (i64, i64) -> i64
    %316 = "llvm.add"(%315, %38) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %317 = "llvm.add"(%316, %300) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %318 = "llvm.and"(%317, %23) : (i64, i64) -> i64
    %319 = "llvm.ashr"(%317, %36) : (i64, i64) -> i64
    %320 = "llvm.add"(%306, %319) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %321 = "llvm.and"(%320, %23) : (i64, i64) -> i64
    %322 = "llvm.ashr"(%320, %36) : (i64, i64) -> i64
    %323 = "llvm.add"(%308, %39) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %324 = "llvm.add"(%323, %322) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %325 = "llvm.lshr"(%324, %36) : (i64, i64) -> i64
    %326 = "llvm.trunc"(%325) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %327 = "llvm.call"(%326) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, noalias_scopes = [#alias_scope9], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %328 = "llvm.zext"(%327) : (i8) -> i64
    %329 = "llvm.sub"(%21, %328) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %330 = "llvm.and"(%329, %40) : (i64, i64) -> i64
    %331 = "llvm.add"(%310, %330) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %332 = "llvm.and"(%331, %23) : (i64, i64) -> i64
    %333 = "llvm.and"(%329, %41) : (i64, i64) -> i64
    %334 = "llvm.lshr"(%331, %42) : (i64, i64) -> i64
    %335 = "llvm.add"(%334, %333) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %336 = "llvm.add"(%335, %314) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %337 = "llvm.and"(%336, %23) : (i64, i64) -> i64
    %338 = "llvm.and"(%329, %43) : (i64, i64) -> i64
    %339 = "llvm.lshr"(%336, %42) : (i64, i64) -> i64
    %340 = "llvm.add"(%318, %338) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %341 = "llvm.add"(%340, %339) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %342 = "llvm.and"(%341, %23) : (i64, i64) -> i64
    %343 = "llvm.lshr"(%341, %42) : (i64, i64) -> i64
    %344 = "llvm.add"(%343, %321) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %345 = "llvm.and"(%344, %23) : (i64, i64) -> i64
    %346 = "llvm.and"(%329, %44) : (i64, i64) -> i64
    %347 = "llvm.lshr"(%344, %42) : (i64, i64) -> i64
    %348 = "llvm.add"(%324, %346) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %349 = "llvm.add"(%348, %347) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %350 = "llvm.and"(%349, %23) : (i64, i64) -> i64
    "llvm.store"(%332, %76) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope12, #alias_scope9], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%337, %77) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope12, #alias_scope9], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%342, %78) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope12, #alias_scope9], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%345, %79) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope12, #alias_scope9], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%350, %80) <{alias_scopes = [#alias_scope10], alignment = 8 : i64, noalias_scopes = [#alias_scope11, #alias_scope12, #alias_scope9], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %351 = "llvm.trunc"(%331) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %352 = "llvm.lshr"(%331, %9) : (i64, i64) -> i64
    %353 = "llvm.trunc"(%352) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %354 = "llvm.lshr"(%331, %13) : (i64, i64) -> i64
    %355 = "llvm.trunc"(%354) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %356 = "llvm.lshr"(%331, %16) : (i64, i64) -> i64
    %357 = "llvm.trunc"(%356) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %358 = "llvm.lshr"(%331, %2) : (i64, i64) -> i64
    %359 = "llvm.trunc"(%358) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %360 = "llvm.lshr"(%331, %4) : (i64, i64) -> i64
    %361 = "llvm.trunc"(%360) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %362 = "llvm.lshr"(%332, %6) : (i64, i64) -> i64
    %363 = "llvm.shl"(%337, %1) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %364 = "llvm.or"(%363, %362) <{isDisjoint}> : (i64, i64) -> i64
    %365 = "llvm.trunc"(%364) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %366 = "llvm.lshr"(%336, %1) : (i64, i64) -> i64
    %367 = "llvm.trunc"(%366) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %368 = "llvm.lshr"(%336, %10) : (i64, i64) -> i64
    %369 = "llvm.trunc"(%368) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %370 = "llvm.lshr"(%336, %17) : (i64, i64) -> i64
    %371 = "llvm.trunc"(%370) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %372 = "llvm.lshr"(%336, %45) : (i64, i64) -> i64
    %373 = "llvm.trunc"(%372) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %374 = "llvm.lshr"(%336, %22) : (i64, i64) -> i64
    %375 = "llvm.trunc"(%374) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %376 = "llvm.lshr"(%336, %46) : (i64, i64) -> i64
    %377 = "llvm.trunc"(%376) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %378 = "llvm.trunc"(%341) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %379 = "llvm.lshr"(%341, %9) : (i64, i64) -> i64
    %380 = "llvm.trunc"(%379) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %381 = "llvm.lshr"(%341, %13) : (i64, i64) -> i64
    %382 = "llvm.trunc"(%381) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %383 = "llvm.lshr"(%341, %16) : (i64, i64) -> i64
    %384 = "llvm.trunc"(%383) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %385 = "llvm.lshr"(%341, %2) : (i64, i64) -> i64
    %386 = "llvm.trunc"(%385) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %387 = "llvm.lshr"(%341, %4) : (i64, i64) -> i64
    %388 = "llvm.trunc"(%387) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %389 = "llvm.lshr"(%342, %6) : (i64, i64) -> i64
    %390 = "llvm.shl"(%344, %1) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %391 = "llvm.or"(%390, %389) <{isDisjoint}> : (i64, i64) -> i64
    %392 = "llvm.trunc"(%391) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %393 = "llvm.lshr"(%344, %1) : (i64, i64) -> i64
    %394 = "llvm.trunc"(%393) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %395 = "llvm.lshr"(%344, %10) : (i64, i64) -> i64
    %396 = "llvm.trunc"(%395) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %397 = "llvm.lshr"(%344, %17) : (i64, i64) -> i64
    %398 = "llvm.trunc"(%397) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %399 = "llvm.lshr"(%344, %45) : (i64, i64) -> i64
    %400 = "llvm.trunc"(%399) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %401 = "llvm.lshr"(%344, %22) : (i64, i64) -> i64
    %402 = "llvm.trunc"(%401) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %403 = "llvm.lshr"(%344, %46) : (i64, i64) -> i64
    %404 = "llvm.trunc"(%403) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %405 = "llvm.trunc"(%349) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %406 = "llvm.lshr"(%349, %9) : (i64, i64) -> i64
    %407 = "llvm.trunc"(%406) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %408 = "llvm.lshr"(%349, %13) : (i64, i64) -> i64
    %409 = "llvm.trunc"(%408) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %410 = "llvm.lshr"(%349, %16) : (i64, i64) -> i64
    %411 = "llvm.trunc"(%410) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %412 = "llvm.lshr"(%349, %2) : (i64, i64) -> i64
    %413 = "llvm.trunc"(%412) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %414 = "llvm.lshr"(%349, %4) : (i64, i64) -> i64
    %415 = "llvm.trunc"(%414) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%351, %arg0) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %416 = "llvm.getelementptr"(%arg0, %47) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%353, %416) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %417 = "llvm.getelementptr"(%arg0, %48) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%355, %417) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %418 = "llvm.getelementptr"(%arg0, %49) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%357, %418) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %419 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%359, %419) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %420 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%361, %420) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %421 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%365, %421) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %422 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%367, %422) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %423 = "llvm.getelementptr"(%arg0, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%369, %423) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %424 = "llvm.getelementptr"(%arg0, %50) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%371, %424) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %425 = "llvm.getelementptr"(%arg0, %51) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%373, %425) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %426 = "llvm.getelementptr"(%arg0, %52) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%375, %426) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %427 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%377, %427) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %428 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%378, %428) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %429 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%380, %429) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %430 = "llvm.getelementptr"(%arg0, %53) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%382, %430) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %431 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%384, %431) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %432 = "llvm.getelementptr"(%arg0, %54) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%386, %432) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %433 = "llvm.getelementptr"(%arg0, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%388, %433) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %434 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%392, %434) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %435 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%394, %435) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %436 = "llvm.getelementptr"(%arg0, %55) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%396, %436) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %437 = "llvm.getelementptr"(%arg0, %56) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%398, %437) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %438 = "llvm.getelementptr"(%arg0, %57) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%400, %438) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %439 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%402, %439) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %440 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%404, %440) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %441 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%405, %441) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %442 = "llvm.getelementptr"(%arg0, %58) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%407, %442) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %443 = "llvm.getelementptr"(%arg0, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%409, %443) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %444 = "llvm.getelementptr"(%arg0, %59) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%411, %444) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %445 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%413, %445) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %446 = "llvm.getelementptr"(%arg0, %60) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%415, %446) <{alias_scopes = [#alias_scope13], alignment = 1 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%67) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%68) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%69) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%70) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%71) : (!llvm.ptr) -> ()
    "llvm.store"(%21, %67) <{alias_scopes = [#alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %68) <{alias_scopes = [#alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %69) <{alias_scopes = [#alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %70) <{alias_scopes = [#alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %71) <{alias_scopes = [#alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope16], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %447 = "llvm.load"(%67) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%447, %90) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %448 = "llvm.load"(%68) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%448, %91) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %449 = "llvm.load"(%69) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%449, %92) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %450 = "llvm.load"(%70) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%450, %93) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %451 = "llvm.load"(%71) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%451, %94) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%67) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%68) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%69) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%70) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%71) : (!llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %81) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %82) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %83) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %84) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %85) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %86) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %87) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %88) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%61, %89) <{alias_scopes = [#alias_scope17], alignment = 16 : i64, noalias_scopes = [#alias_scope18], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.start"(%62) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%63) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%64) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%65) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%66) : (!llvm.ptr) -> ()
    "llvm.store"(%21, %62) <{alias_scopes = [#alias_scope19], alignment = 8 : i64, noalias_scopes = [#alias_scope20], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %63) <{alias_scopes = [#alias_scope19], alignment = 8 : i64, noalias_scopes = [#alias_scope20], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %64) <{alias_scopes = [#alias_scope19], alignment = 8 : i64, noalias_scopes = [#alias_scope20], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %65) <{alias_scopes = [#alias_scope19], alignment = 8 : i64, noalias_scopes = [#alias_scope20], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%21, %66) <{alias_scopes = [#alias_scope19], alignment = 8 : i64, noalias_scopes = [#alias_scope20], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %452 = "llvm.load"(%62) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%452, %76) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %453 = "llvm.load"(%63) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%453, %77) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %454 = "llvm.load"(%64) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%454, %78) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %455 = "llvm.load"(%65) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%455, %79) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %456 = "llvm.load"(%66) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%456, %80) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%62) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%63) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%64) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%65) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%66) : (!llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.end"(%76) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%77) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%78) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%79) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%80) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%81) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%82) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%83) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%84) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%85) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%86) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%87) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%88) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%89) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%90) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%91) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%92) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%93) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%94) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 :=
  Encoding.Decompress.Execution.BlackBox.program.call

theorem block_count : program.n = 1 := rfl

end
end Agave.Ed25519.ScalarReduce32.Execution
