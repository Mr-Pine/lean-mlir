module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned subgroup scalar regions. Regenerate with MLIR/import_scalar_wide.py.

Only required symbol-name quoting changes the source spelling. `execution_def`
checks successful RIR translation, including calls and globals; it
does not supply any primitive's semantics or prove an execution result.
Original scalar wide and Montgomery bodies, including zeroization; not base-field Reduce64.
-/

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR
@[expose] public section

namespace ScalarWide

structure Primitives where
  /-- Exact external symbol `_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul`. -/
  montgomeryMul : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- Exact external symbol `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`. -/
  blackBoxByte : Vals [.bv 8] → EffectM (Vals [.bv 8])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul" => some ⟨[.ptr, .ptr, .ptr], [], p.montgomeryMul⟩
  | "_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519" => some ⟨[.bv 8], [.bv 8], p.blackBoxByte⟩
  | _ => none

structure Globals where
  /-- `alloc_595ed8f9b6c4f781a4a1d10db150f124`; initializer and mutability are separate memory obligations. -/
  address0 : Pointer
  /-- `alloc_b0a0adc7a7ee3d20b0509962c17b23d6`; initializer and mutability are separate memory obligations. -/
  address1 : Pointer

def Globals.resolve (g : Globals) : String → Option Pointer
  | "alloc_595ed8f9b6c4f781a4a1d10db150f124" => some g.address0
  | "alloc_b0a0adc7a7ee3d20b0509962c17b23d6" => some g.address1
  | _ => none

execution_def program (p : Primitives) (g : Globals) :=
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
    %18 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 33 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 46 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 54 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 58 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 59 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 60 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 62 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 4503599627370495 : i64}> : () -> i64
    %39 = "llvm.mlir.addressof"() <{global_name = @alloc_595ed8f9b6c4f781a4a1d10db150f124}> : () -> !llvm.ptr
    %40 = "llvm.mlir.addressof"() <{global_name = @alloc_b0a0adc7a7ee3d20b0509962c17b23d6}> : () -> !llvm.ptr
    %41 = "llvm.mlir.constant"() <{value = -671914833335277 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = -3916664325105025 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = -1367801 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = -17592186044416 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %47 = "llvm.mlir.constant"() <{value = 671914833335277 : i64}> : () -> i64
    %48 = "llvm.mlir.constant"() <{value = 3916664325105025 : i64}> : () -> i64
    %49 = "llvm.mlir.constant"() <{value = 1367801 : i64}> : () -> i64
    %50 = "llvm.mlir.constant"() <{value = 17592186044416 : i64}> : () -> i64
    %51 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %52 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %53 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %54 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %55 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %56 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %57 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %58 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %59 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %60 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %61 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %62 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %63 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %64 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %65 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %66 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %67 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %68 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %69 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %70 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %71 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %72 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %73 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %74 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %75 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %76 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %77 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %78 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %79 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %80 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %81 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %82 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %83 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %84 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %85 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %86 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %87 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    %88 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = i64}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%84) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%85) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%86) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%87) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%88) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    "llvm.intr.lifetime.start"(%76) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%77) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%78) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%79) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%80) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%81) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%82) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%83) : (!llvm.ptr) -> ()
    %89 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %90 = "llvm.zext"(%89) : (i32) -> i64
    %91 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %92 = "llvm.load"(%91) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %93 = "llvm.zext"(%92) : (i8) -> i64
    %94 = "llvm.shl"(%93, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %95 = "llvm.or"(%94, %90) <{isDisjoint}> : (i64, i64) -> i64
    %96 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %97 = "llvm.load"(%96) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %98 = "llvm.zext"(%97) : (i8) -> i64
    %99 = "llvm.shl"(%98, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %100 = "llvm.or"(%95, %99) <{isDisjoint}> : (i64, i64) -> i64
    %101 = "llvm.getelementptr"(%arg1, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %102 = "llvm.load"(%101) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %103 = "llvm.zext"(%102) : (i8) -> i64
    %104 = "llvm.shl"(%103, %6) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %105 = "llvm.or"(%100, %104) <{isDisjoint}> : (i64, i64) -> i64
    %106 = "llvm.getelementptr"(%arg1, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %107 = "llvm.load"(%106) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %108 = "llvm.zext"(%107) : (i8) -> i64
    %109 = "llvm.shl"(%108, %8) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %110 = "llvm.or"(%109, %105) <{isDisjoint}> : (i64, i64) -> i64
    %111 = "llvm.getelementptr"(%arg1, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %112 = "llvm.load"(%111) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %113 = "llvm.zext"(%112) : (i32) -> i64
    %114 = "llvm.getelementptr"(%arg1, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %115 = "llvm.load"(%114) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %116 = "llvm.zext"(%115) : (i8) -> i64
    %117 = "llvm.shl"(%116, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %118 = "llvm.or"(%117, %113) <{isDisjoint}> : (i64, i64) -> i64
    %119 = "llvm.getelementptr"(%arg1, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %120 = "llvm.load"(%119) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %121 = "llvm.zext"(%120) : (i8) -> i64
    %122 = "llvm.shl"(%121, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %123 = "llvm.getelementptr"(%arg1, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %124 = "llvm.load"(%123) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %125 = "llvm.zext"(%124) : (i16) -> i64
    %126 = "llvm.shl"(%125, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %127 = "llvm.or"(%122, %126) <{isDisjoint}> : (i64, i64) -> i64
    %128 = "llvm.or"(%127, %118) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%128, %77) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %129 = "llvm.getelementptr"(%arg1, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %130 = "llvm.load"(%129) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %131 = "llvm.zext"(%130) : (i16) -> i64
    %132 = "llvm.getelementptr"(%arg1, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %133 = "llvm.load"(%132) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %134 = "llvm.zext"(%133) : (i8) -> i64
    %135 = "llvm.shl"(%134, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %136 = "llvm.or"(%135, %131) <{isDisjoint}> : (i64, i64) -> i64
    %137 = "llvm.getelementptr"(%arg1, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %138 = "llvm.load"(%137) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %139 = "llvm.zext"(%138) : (i8) -> i64
    %140 = "llvm.shl"(%139, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %141 = "llvm.or"(%136, %140) <{isDisjoint}> : (i64, i64) -> i64
    %142 = "llvm.getelementptr"(%arg1, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %143 = "llvm.load"(%142) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %144 = "llvm.zext"(%143) : (i16) -> i64
    %145 = "llvm.shl"(%144, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %146 = "llvm.getelementptr"(%arg1, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %147 = "llvm.load"(%146) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %148 = "llvm.zext"(%147) : (i16) -> i64
    %149 = "llvm.shl"(%148, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %150 = "llvm.or"(%145, %149) <{isDisjoint}> : (i64, i64) -> i64
    %151 = "llvm.or"(%150, %141) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%151, %78) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %152 = "llvm.getelementptr"(%arg1, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %153 = "llvm.load"(%152) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %154 = "llvm.zext"(%153) : (i8) -> i64
    %155 = "llvm.getelementptr"(%arg1, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %156 = "llvm.load"(%155) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %157 = "llvm.zext"(%156) : (i8) -> i64
    %158 = "llvm.shl"(%157, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %159 = "llvm.or"(%158, %154) <{isDisjoint}> : (i64, i64) -> i64
    %160 = "llvm.getelementptr"(%arg1, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %161 = "llvm.load"(%160) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %162 = "llvm.zext"(%161) : (i16) -> i64
    %163 = "llvm.shl"(%162, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %164 = "llvm.getelementptr"(%arg1, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %165 = "llvm.load"(%164) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %166 = "llvm.zext"(%165) : (i16) -> i64
    %167 = "llvm.shl"(%166, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %168 = "llvm.or"(%163, %167) <{isDisjoint}> : (i64, i64) -> i64
    %169 = "llvm.getelementptr"(%arg1, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %170 = "llvm.load"(%169) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %171 = "llvm.zext"(%170) : (i16) -> i64
    %172 = "llvm.shl"(%171, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %173 = "llvm.or"(%168, %172) <{isDisjoint}> : (i64, i64) -> i64
    %174 = "llvm.or"(%173, %159) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%174, %79) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %175 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %176 = "llvm.load"(%175) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %177 = "llvm.zext"(%176) : (i8) -> i64
    %178 = "llvm.getelementptr"(%arg1, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %179 = "llvm.load"(%178) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %180 = "llvm.zext"(%179) : (i8) -> i64
    %181 = "llvm.shl"(%180, %9) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %182 = "llvm.getelementptr"(%arg1, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %183 = "llvm.load"(%182) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %184 = "llvm.zext"(%183) : (i16) -> i64
    %185 = "llvm.shl"(%184, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %186 = "llvm.or"(%181, %185) <{isDisjoint}> : (i64, i64) -> i64
    %187 = "llvm.getelementptr"(%arg1, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %188 = "llvm.load"(%187) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %189 = "llvm.zext"(%188) : (i16) -> i64
    %190 = "llvm.shl"(%189, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %191 = "llvm.or"(%186, %190) <{isDisjoint}> : (i64, i64) -> i64
    %192 = "llvm.getelementptr"(%arg1, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %193 = "llvm.load"(%192) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %194 = "llvm.zext"(%193) : (i16) -> i64
    %195 = "llvm.shl"(%194, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %196 = "llvm.or"(%191, %195) <{isDisjoint}> : (i64, i64) -> i64
    %197 = "llvm.or"(%196, %177) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%197, %80) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %198 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %199 = "llvm.load"(%198) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i32
    %200 = "llvm.zext"(%199) : (i32) -> i64
    %201 = "llvm.getelementptr"(%arg1, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %202 = "llvm.load"(%201) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %203 = "llvm.zext"(%202) : (i8) -> i64
    %204 = "llvm.shl"(%203, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %205 = "llvm.or"(%204, %200) <{isDisjoint}> : (i64, i64) -> i64
    %206 = "llvm.getelementptr"(%arg1, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %207 = "llvm.load"(%206) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %208 = "llvm.zext"(%207) : (i8) -> i64
    %209 = "llvm.shl"(%208, %4) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %210 = "llvm.or"(%205, %209) <{isDisjoint}> : (i64, i64) -> i64
    %211 = "llvm.getelementptr"(%arg1, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %212 = "llvm.load"(%211) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %213 = "llvm.zext"(%212) : (i16) -> i64
    %214 = "llvm.shl"(%213, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %215 = "llvm.or"(%214, %210) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%215, %81) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %216 = "llvm.getelementptr"(%arg1, %6) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %217 = "llvm.load"(%216) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %218 = "llvm.zext"(%217) : (i16) -> i64
    %219 = "llvm.getelementptr"(%arg1, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %220 = "llvm.load"(%219) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %221 = "llvm.zext"(%220) : (i8) -> i64
    %222 = "llvm.shl"(%221, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %223 = "llvm.or"(%222, %218) <{isDisjoint}> : (i64, i64) -> i64
    %224 = "llvm.getelementptr"(%arg1, %31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %225 = "llvm.load"(%224) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %226 = "llvm.zext"(%225) : (i8) -> i64
    %227 = "llvm.shl"(%226, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %228 = "llvm.or"(%223, %227) <{isDisjoint}> : (i64, i64) -> i64
    %229 = "llvm.getelementptr"(%arg1, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %230 = "llvm.load"(%229) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %231 = "llvm.zext"(%230) : (i16) -> i64
    %232 = "llvm.shl"(%231, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %233 = "llvm.getelementptr"(%arg1, %33) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %234 = "llvm.load"(%233) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %235 = "llvm.zext"(%234) : (i16) -> i64
    %236 = "llvm.shl"(%235, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %237 = "llvm.or"(%232, %236) <{isDisjoint}> : (i64, i64) -> i64
    %238 = "llvm.or"(%237, %228) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%238, %82) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %239 = "llvm.getelementptr"(%arg1, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %240 = "llvm.load"(%239) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %241 = "llvm.zext"(%240) : (i16) -> i64
    %242 = "llvm.getelementptr"(%arg1, %34) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %243 = "llvm.load"(%242) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %244 = "llvm.zext"(%243) : (i8) -> i64
    %245 = "llvm.shl"(%244, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %246 = "llvm.or"(%245, %241) <{isDisjoint}> : (i64, i64) -> i64
    %247 = "llvm.getelementptr"(%arg1, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %248 = "llvm.load"(%247) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %249 = "llvm.zext"(%248) : (i8) -> i64
    %250 = "llvm.shl"(%249, %16) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %251 = "llvm.getelementptr"(%arg1, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %252 = "llvm.load"(%251) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %253 = "llvm.zext"(%252) : (i16) -> i64
    %254 = "llvm.shl"(%253, %2) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %255 = "llvm.or"(%250, %254) <{isDisjoint}> : (i64, i64) -> i64
    %256 = "llvm.getelementptr"(%arg1, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %257 = "llvm.load"(%256) <{alias_scopes = [#alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope], ordering = 0 : i64}> : (!llvm.ptr) -> i16
    %258 = "llvm.zext"(%257) : (i16) -> i64
    %259 = "llvm.shl"(%258, %6) <{overflowFlags = 2 : i32}> : (i64, i64) -> i64
    %260 = "llvm.or"(%255, %259) <{isDisjoint}> : (i64, i64) -> i64
    %261 = "llvm.or"(%260, %246) <{isDisjoint}> : (i64, i64) -> i64
    "llvm.store"(%261, %83) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%75) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%74) : (!llvm.ptr) -> ()
    %262 = "llvm.and"(%105, %38) : (i64, i64) -> i64
    "llvm.store"(%262, %75) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %263 = "llvm.intr.fshl"(%118, %110, %10) : (i64, i64, i64) -> i64
    %264 = "llvm.getelementptr"(%75, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%263, %264) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %265 = "llvm.intr.fshl"(%141, %127, %16) : (i64, i64, i64) -> i64
    %266 = "llvm.getelementptr"(%75, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %267 = "llvm.and"(%265, %38) : (i64, i64) -> i64
    "llvm.store"(%267, %266) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %268 = "llvm.intr.fshl"(%159, %151, %25) : (i64, i64, i64) -> i64
    %269 = "llvm.getelementptr"(%75, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%268, %269) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %270 = "llvm.intr.fshl"(%177, %173, %6) : (i64, i64, i64) -> i64
    %271 = "llvm.getelementptr"(%75, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %272 = "llvm.and"(%270, %38) : (i64, i64) -> i64
    "llvm.store"(%272, %271) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %273 = "llvm.lshr"(%197, %1) : (i64, i64) -> i64
    %274 = "llvm.and"(%273, %38) : (i64, i64) -> i64
    "llvm.store"(%274, %74) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %275 = "llvm.intr.fshl"(%210, %195, %9) : (i64, i64, i64) -> i64
    %276 = "llvm.getelementptr"(%74, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %277 = "llvm.and"(%275, %38) : (i64, i64) -> i64
    "llvm.store"(%277, %276) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %278 = "llvm.intr.fshl"(%228, %215, %17) : (i64, i64, i64) -> i64
    %279 = "llvm.getelementptr"(%74, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%278, %279) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %280 = "llvm.intr.fshl"(%246, %237, %2) : (i64, i64, i64) -> i64
    %281 = "llvm.getelementptr"(%74, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %282 = "llvm.and"(%280, %38) : (i64, i64) -> i64
    "llvm.store"(%282, %281) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %283 = "llvm.getelementptr"(%74, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %284 = "llvm.lshr"(%261, %17) : (i64, i64) -> i64
    "llvm.store"(%284, %283) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%73) : (!llvm.ptr) -> ()
    "llvm.call"(%73, %75, %39) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, noalias_scopes = [#alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%75, %73, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%73) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%72) : (!llvm.ptr) -> ()
    "llvm.call"(%72, %74, %40) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, noalias_scopes = [#alias_scope], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%74, %72, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope, #alias_scope1]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%72) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope2}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope3}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope4}> : () -> ()
    %285 = "llvm.load"(%74) <{alias_scopes = [#alias_scope3], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %286 = "llvm.load"(%75) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %287 = "llvm.add"(%286, %285) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %288 = "llvm.and"(%287, %38) : (i64, i64) -> i64
    %289 = "llvm.load"(%276) <{alias_scopes = [#alias_scope3], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %290 = "llvm.load"(%264) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %291 = "llvm.lshr"(%287, %32) : (i64, i64) -> i64
    %292 = "llvm.add"(%291, %289) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %293 = "llvm.add"(%292, %290) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %294 = "llvm.and"(%293, %38) : (i64, i64) -> i64
    %295 = "llvm.load"(%279) <{alias_scopes = [#alias_scope3], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %296 = "llvm.load"(%266) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %297 = "llvm.lshr"(%293, %32) : (i64, i64) -> i64
    %298 = "llvm.add"(%296, %295) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %299 = "llvm.add"(%298, %297) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %300 = "llvm.and"(%299, %38) : (i64, i64) -> i64
    %301 = "llvm.load"(%281) <{alias_scopes = [#alias_scope3], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %302 = "llvm.load"(%269) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %303 = "llvm.lshr"(%299, %32) : (i64, i64) -> i64
    %304 = "llvm.add"(%302, %301) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %305 = "llvm.add"(%304, %303) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %306 = "llvm.and"(%305, %38) : (i64, i64) -> i64
    %307 = "llvm.load"(%283) <{alias_scopes = [#alias_scope3], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %308 = "llvm.load"(%271) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %309 = "llvm.lshr"(%305, %32) : (i64, i64) -> i64
    %310 = "llvm.add"(%308, %307) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %311 = "llvm.add"(%310, %309) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %312 = "llvm.and"(%311, %38) : (i64, i64) -> i64
    %313 = "llvm.add"(%288, %41) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %314 = "llvm.and"(%313, %38) : (i64, i64) -> i64
    %315 = "llvm.ashr"(%313, %42) : (i64, i64) -> i64
    %316 = "llvm.add"(%315, %43) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %317 = "llvm.add"(%316, %294) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %318 = "llvm.and"(%317, %38) : (i64, i64) -> i64
    %319 = "llvm.ashr"(%317, %42) : (i64, i64) -> i64
    %320 = "llvm.add"(%300, %44) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %321 = "llvm.add"(%320, %319) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %322 = "llvm.and"(%321, %38) : (i64, i64) -> i64
    %323 = "llvm.ashr"(%321, %42) : (i64, i64) -> i64
    %324 = "llvm.add"(%323, %306) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %325 = "llvm.and"(%324, %38) : (i64, i64) -> i64
    %326 = "llvm.ashr"(%324, %42) : (i64, i64) -> i64
    %327 = "llvm.add"(%312, %45) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %328 = "llvm.add"(%327, %326) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %329 = "llvm.lshr"(%328, %42) : (i64, i64) -> i64
    %330 = "llvm.trunc"(%329) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %331 = "llvm.call"(%330) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %332 = "llvm.zext"(%331) : (i8) -> i64
    %333 = "llvm.sub"(%46, %332) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %334 = "llvm.and"(%333, %47) : (i64, i64) -> i64
    %335 = "llvm.add"(%334, %314) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %336 = "llvm.and"(%335, %38) : (i64, i64) -> i64
    %337 = "llvm.and"(%333, %48) : (i64, i64) -> i64
    %338 = "llvm.lshr"(%335, %32) : (i64, i64) -> i64
    %339 = "llvm.add"(%337, %318) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %340 = "llvm.add"(%339, %338) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %341 = "llvm.and"(%340, %38) : (i64, i64) -> i64
    %342 = "llvm.and"(%333, %49) : (i64, i64) -> i64
    %343 = "llvm.lshr"(%340, %32) : (i64, i64) -> i64
    %344 = "llvm.add"(%342, %322) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %345 = "llvm.add"(%344, %343) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %346 = "llvm.and"(%345, %38) : (i64, i64) -> i64
    %347 = "llvm.lshr"(%345, %32) : (i64, i64) -> i64
    %348 = "llvm.add"(%347, %325) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %349 = "llvm.and"(%348, %38) : (i64, i64) -> i64
    %350 = "llvm.and"(%333, %50) : (i64, i64) -> i64
    %351 = "llvm.lshr"(%348, %32) : (i64, i64) -> i64
    %352 = "llvm.add"(%328, %350) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %353 = "llvm.add"(%352, %351) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %354 = "llvm.and"(%353, %38) : (i64, i64) -> i64
    "llvm.store"(%336, %84) <{alias_scopes = [#alias_scope5, #alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7, #alias_scope3, #alias_scope4, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%341, %85) <{alias_scopes = [#alias_scope5, #alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7, #alias_scope3, #alias_scope4, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%346, %86) <{alias_scopes = [#alias_scope5, #alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7, #alias_scope3, #alias_scope4, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%349, %87) <{alias_scopes = [#alias_scope5, #alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7, #alias_scope3, #alias_scope4, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%354, %88) <{alias_scopes = [#alias_scope5, #alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope6, #alias_scope7, #alias_scope3, #alias_scope4, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%46, %76) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %77) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %78) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %79) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %80) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %81) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %82) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%46, %83) <{alias_scopes = [#alias_scope8], alignment = 8 : i64, noalias_scopes = [#alias_scope9, #alias_scope, #alias_scope1], ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.start"(%71) : (!llvm.ptr) -> ()
    "llvm.intr.memset"(%71, %51, %4) <{alias_scopes = [#alias_scope10], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope11, #alias_scope, #alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%75, %71, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull}, {llvm.align = 8 : i64, llvm.nonnull}, {}], isVolatile = true, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%71) : (!llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.start"(%70) : (!llvm.ptr) -> ()
    "llvm.intr.memset"(%70, %51, %4) <{alias_scopes = [#alias_scope12], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope13, #alias_scope, #alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%74, %70, %4) <{arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 40 : i64, llvm.nonnull}, {llvm.align = 8 : i64, llvm.nonnull}, {}], isVolatile = true, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%70) : (!llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.end"(%74) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%75) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%76) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%77) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%78) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%79) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%80) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%81) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%82) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%83) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope14}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope15}> : () -> ()
    %355 = "llvm.load"(%84) <{alias_scopes = [#alias_scope16, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %356 = "llvm.trunc"(%355) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %357 = "llvm.lshr"(%355, %9) : (i64, i64) -> i64
    %358 = "llvm.trunc"(%357) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %359 = "llvm.lshr"(%355, %13) : (i64, i64) -> i64
    %360 = "llvm.trunc"(%359) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %361 = "llvm.lshr"(%355, %16) : (i64, i64) -> i64
    %362 = "llvm.trunc"(%361) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %363 = "llvm.lshr"(%355, %2) : (i64, i64) -> i64
    %364 = "llvm.trunc"(%363) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %365 = "llvm.lshr"(%355, %4) : (i64, i64) -> i64
    %366 = "llvm.trunc"(%365) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %367 = "llvm.lshr"(%355, %6) : (i64, i64) -> i64
    %368 = "llvm.load"(%85) <{alias_scopes = [#alias_scope16, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %369 = "llvm.shl"(%368, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %370 = "llvm.or"(%369, %367) : (i64, i64) -> i64
    %371 = "llvm.trunc"(%370) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %372 = "llvm.lshr"(%368, %1) : (i64, i64) -> i64
    %373 = "llvm.trunc"(%372) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %374 = "llvm.lshr"(%368, %10) : (i64, i64) -> i64
    %375 = "llvm.trunc"(%374) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %376 = "llvm.lshr"(%368, %17) : (i64, i64) -> i64
    %377 = "llvm.trunc"(%376) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %378 = "llvm.lshr"(%368, %21) : (i64, i64) -> i64
    %379 = "llvm.trunc"(%378) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %380 = "llvm.lshr"(%368, %25) : (i64, i64) -> i64
    %381 = "llvm.trunc"(%380) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %382 = "llvm.lshr"(%368, %27) : (i64, i64) -> i64
    %383 = "llvm.trunc"(%382) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %384 = "llvm.load"(%86) <{alias_scopes = [#alias_scope16, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %385 = "llvm.trunc"(%384) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %386 = "llvm.lshr"(%384, %9) : (i64, i64) -> i64
    %387 = "llvm.trunc"(%386) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %388 = "llvm.lshr"(%384, %13) : (i64, i64) -> i64
    %389 = "llvm.trunc"(%388) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %390 = "llvm.lshr"(%384, %16) : (i64, i64) -> i64
    %391 = "llvm.trunc"(%390) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %392 = "llvm.lshr"(%384, %2) : (i64, i64) -> i64
    %393 = "llvm.trunc"(%392) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %394 = "llvm.lshr"(%384, %4) : (i64, i64) -> i64
    %395 = "llvm.trunc"(%394) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %396 = "llvm.lshr"(%384, %6) : (i64, i64) -> i64
    %397 = "llvm.load"(%87) <{alias_scopes = [#alias_scope16, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %398 = "llvm.shl"(%397, %1) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %399 = "llvm.or"(%398, %396) : (i64, i64) -> i64
    %400 = "llvm.trunc"(%399) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %401 = "llvm.lshr"(%397, %1) : (i64, i64) -> i64
    %402 = "llvm.trunc"(%401) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %403 = "llvm.lshr"(%397, %10) : (i64, i64) -> i64
    %404 = "llvm.trunc"(%403) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %405 = "llvm.lshr"(%397, %17) : (i64, i64) -> i64
    %406 = "llvm.trunc"(%405) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %407 = "llvm.lshr"(%397, %21) : (i64, i64) -> i64
    %408 = "llvm.trunc"(%407) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %409 = "llvm.lshr"(%397, %25) : (i64, i64) -> i64
    %410 = "llvm.trunc"(%409) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %411 = "llvm.lshr"(%397, %27) : (i64, i64) -> i64
    %412 = "llvm.trunc"(%411) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %413 = "llvm.load"(%88) <{alias_scopes = [#alias_scope16, #alias_scope15], alignment = 8 : i64, noalias_scopes = [#alias_scope17, #alias_scope14], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %414 = "llvm.trunc"(%413) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %415 = "llvm.lshr"(%413, %9) : (i64, i64) -> i64
    %416 = "llvm.trunc"(%415) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %417 = "llvm.lshr"(%413, %13) : (i64, i64) -> i64
    %418 = "llvm.trunc"(%417) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %419 = "llvm.lshr"(%413, %16) : (i64, i64) -> i64
    %420 = "llvm.trunc"(%419) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %421 = "llvm.lshr"(%413, %2) : (i64, i64) -> i64
    %422 = "llvm.trunc"(%421) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %423 = "llvm.lshr"(%413, %4) : (i64, i64) -> i64
    %424 = "llvm.trunc"(%423) <{overflowFlags = 0 : i32}> : (i64) -> i8
    "llvm.store"(%356, %arg0) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %425 = "llvm.getelementptr"(%arg0, %52) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%358, %425) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %426 = "llvm.getelementptr"(%arg0, %53) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%360, %426) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %427 = "llvm.getelementptr"(%arg0, %54) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%362, %427) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %428 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%364, %428) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %429 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%366, %429) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %430 = "llvm.getelementptr"(%arg0, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%371, %430) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %431 = "llvm.getelementptr"(%arg0, %7) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%373, %431) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %432 = "llvm.getelementptr"(%arg0, %9) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%375, %432) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %433 = "llvm.getelementptr"(%arg0, %55) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%377, %433) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %434 = "llvm.getelementptr"(%arg0, %56) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%379, %434) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %435 = "llvm.getelementptr"(%arg0, %57) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%381, %435) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %436 = "llvm.getelementptr"(%arg0, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%383, %436) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %437 = "llvm.getelementptr"(%arg0, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%385, %437) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %438 = "llvm.getelementptr"(%arg0, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%387, %438) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %439 = "llvm.getelementptr"(%arg0, %58) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%389, %439) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %440 = "llvm.getelementptr"(%arg0, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%391, %440) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %441 = "llvm.getelementptr"(%arg0, %59) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%393, %441) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %442 = "llvm.getelementptr"(%arg0, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%395, %442) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %443 = "llvm.getelementptr"(%arg0, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%400, %443) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %444 = "llvm.getelementptr"(%arg0, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%402, %444) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %445 = "llvm.getelementptr"(%arg0, %60) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%404, %445) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %446 = "llvm.getelementptr"(%arg0, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%406, %446) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %447 = "llvm.getelementptr"(%arg0, %61) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%408, %447) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %448 = "llvm.getelementptr"(%arg0, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%410, %448) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %449 = "llvm.getelementptr"(%arg0, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%412, %449) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %450 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%414, %450) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %451 = "llvm.getelementptr"(%arg0, %62) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%416, %451) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %452 = "llvm.getelementptr"(%arg0, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%418, %452) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %453 = "llvm.getelementptr"(%arg0, %63) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%420, %453) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %454 = "llvm.getelementptr"(%arg0, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%422, %454) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %455 = "llvm.getelementptr"(%arg0, %64) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%424, %455) <{alias_scopes = [#alias_scope14], alignment = 1 : i64, noalias_scopes = [#alias_scope15], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%65) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%66) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%67) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%68) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%69) : (!llvm.ptr) -> ()
    "llvm.store"(%46, %65) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%46, %66) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%46, %67) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%46, %68) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%46, %69) <{alias_scopes = [#alias_scope18], alignment = 8 : i64, noalias_scopes = [#alias_scope19], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %456 = "llvm.load"(%65) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%456, %84) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %457 = "llvm.load"(%66) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%457, %85) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %458 = "llvm.load"(%67) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%458, %86) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %459 = "llvm.load"(%68) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%459, %87) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    %460 = "llvm.load"(%69) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (!llvm.ptr) -> i64
    "llvm.store"(%460, %88) <{alignment = 8 : i64, ordering = 0 : i64, volatile_}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%65) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%66) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%67) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%68) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%69) : (!llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.end"(%84) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%85) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%86) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%87) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%88) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvMs2_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u646scalarNtB5_8Scalar5214montgomery_mul := p.montgomeryMul,
  @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 := p.blackBoxByte
globals @alloc_595ed8f9b6c4f781a4a1d10db150f124 := g.address0,
  @alloc_b0a0adc7a7ee3d20b0509962c17b23d6 := g.address1

theorem block_count (p : Primitives) (g : Globals) : (program p g).n = 1 := rfl

end ScalarWide

namespace ScalarMontgomeryMul

structure Primitives where
  /-- Exact external symbol `_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519`. -/
  blackBoxByte : Vals [.bv 8] → EffectM (Vals [.bv 8])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519" => some ⟨[.bv 8], [.bv 8], p.blackBoxByte⟩
  | _ => none

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 1439961107955227 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 4503599627370495 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 671914833335277 : i128}> : () -> i128
    %8 = "llvm.mlir.constant"() <{value = 52 : i128}> : () -> i128
    %9 = "llvm.mlir.constant"() <{value = 3916664325105025 : i128}> : () -> i128
    %10 = "llvm.mlir.constant"() <{value = 1367801 : i128}> : () -> i128
    %11 = "llvm.mlir.constant"() <{value = 44 : i128}> : () -> i128
    %12 = "llvm.mlir.constant"() <{value = -671914833335277 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = -3916664325105025 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = -1367801 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = -17592186044416 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 671914833335277 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 3916664325105025 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 1367801 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 17592186044416 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 0 : i128}> : () -> i128
    %24 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %25 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %26 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %27 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %28 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %29 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %30 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %31 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    %32 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = i128}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%24) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%25) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%26) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%27) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%28) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%29) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%30) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%31) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%32) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope2}> : () -> ()
    %33 = "llvm.load"(%arg1) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %34 = "llvm.load"(%arg2) <{alias_scopes = [#alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %35 = "llvm.zext"(%33) : (i64) -> i128
    %36 = "llvm.zext"(%34) : (i64) -> i128
    %37 = "llvm.mul"(%36, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %38 = "llvm.getelementptr"(%arg2, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %39 = "llvm.load"(%38) <{alias_scopes = [#alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %40 = "llvm.zext"(%39) : (i64) -> i128
    %41 = "llvm.mul"(%40, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %42 = "llvm.getelementptr"(%arg1, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %43 = "llvm.load"(%42) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %44 = "llvm.zext"(%43) : (i64) -> i128
    %45 = "llvm.mul"(%44, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %46 = "llvm.add"(%45, %41) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%46, %25) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %47 = "llvm.getelementptr"(%arg2, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %48 = "llvm.load"(%47) <{alias_scopes = [#alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %49 = "llvm.zext"(%48) : (i64) -> i128
    %50 = "llvm.mul"(%49, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %51 = "llvm.mul"(%44, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %52 = "llvm.add"(%50, %51) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %53 = "llvm.getelementptr"(%arg1, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %54 = "llvm.load"(%53) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %55 = "llvm.zext"(%54) : (i64) -> i128
    %56 = "llvm.mul"(%55, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %57 = "llvm.add"(%52, %56) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%57, %26) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %58 = "llvm.getelementptr"(%arg2, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %59 = "llvm.load"(%58) <{alias_scopes = [#alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %60 = "llvm.zext"(%59) : (i64) -> i128
    %61 = "llvm.mul"(%60, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %62 = "llvm.mul"(%49, %44) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %63 = "llvm.mul"(%55, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %64 = "llvm.getelementptr"(%arg1, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %65 = "llvm.load"(%64) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %66 = "llvm.zext"(%65) : (i64) -> i128
    %67 = "llvm.mul"(%66, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %68 = "llvm.add"(%63, %62) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %69 = "llvm.add"(%68, %61) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %70 = "llvm.add"(%69, %67) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%70, %27) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %71 = "llvm.getelementptr"(%arg2, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %72 = "llvm.load"(%71) <{alias_scopes = [#alias_scope2], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %73 = "llvm.zext"(%72) : (i64) -> i128
    %74 = "llvm.mul"(%73, %35) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %75 = "llvm.mul"(%60, %44) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %76 = "llvm.mul"(%55, %49) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %77 = "llvm.mul"(%66, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %78 = "llvm.getelementptr"(%arg1, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %79 = "llvm.load"(%78) <{alias_scopes = [#alias_scope1], alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope2], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %80 = "llvm.zext"(%79) : (i64) -> i128
    %81 = "llvm.mul"(%80, %36) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %82 = "llvm.add"(%75, %76) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %83 = "llvm.add"(%82, %77) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %84 = "llvm.add"(%83, %74) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %85 = "llvm.add"(%84, %81) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%85, %28) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %86 = "llvm.mul"(%73, %44) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %87 = "llvm.mul"(%60, %55) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %88 = "llvm.mul"(%66, %49) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %89 = "llvm.mul"(%80, %40) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %90 = "llvm.add"(%88, %87) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %91 = "llvm.add"(%90, %86) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %92 = "llvm.add"(%91, %89) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%92, %29) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %93 = "llvm.mul"(%73, %55) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %94 = "llvm.mul"(%66, %60) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %95 = "llvm.add"(%93, %94) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %96 = "llvm.mul"(%80, %49) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %97 = "llvm.add"(%95, %96) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%97, %30) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %98 = "llvm.mul"(%73, %66) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %99 = "llvm.mul"(%80, %60) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    %100 = "llvm.add"(%99, %98) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    "llvm.store"(%100, %31) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %101 = "llvm.mul"(%80, %73) <{overflowFlags = 2 : i32}> : (i128, i128) -> i128
    "llvm.store"(%101, %32) <{alias_scopes = [#alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope1, #alias_scope2], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    %102 = "llvm.trunc"(%37) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %103 = "llvm.mul"(%102, %5) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %104 = "llvm.and"(%103, %6) : (i64, i64) -> i64
    %105 = "llvm.zext"(%104) <{nonNeg}> : (i64) -> i128
    %106 = "llvm.mul"(%105, %7) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %107 = "llvm.add"(%106, %37) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %108 = "llvm.lshr"(%107, %8) : (i128, i128) -> i128
    %109 = "llvm.mul"(%105, %9) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %110 = "llvm.add"(%109, %46) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %111 = "llvm.add"(%110, %108) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %112 = "llvm.trunc"(%111) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %113 = "llvm.mul"(%112, %5) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %114 = "llvm.and"(%113, %6) : (i64, i64) -> i64
    %115 = "llvm.zext"(%114) <{nonNeg}> : (i64) -> i128
    %116 = "llvm.mul"(%115, %7) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %117 = "llvm.add"(%116, %111) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %118 = "llvm.lshr"(%117, %8) : (i128, i128) -> i128
    %119 = "llvm.mul"(%105, %10) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %120 = "llvm.mul"(%115, %9) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %121 = "llvm.add"(%57, %119) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %122 = "llvm.add"(%121, %120) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %123 = "llvm.add"(%122, %118) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %124 = "llvm.trunc"(%123) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %125 = "llvm.mul"(%124, %5) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %126 = "llvm.and"(%125, %6) : (i64, i64) -> i64
    %127 = "llvm.zext"(%126) <{nonNeg}> : (i64) -> i128
    %128 = "llvm.mul"(%127, %7) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %129 = "llvm.add"(%128, %123) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %130 = "llvm.lshr"(%129, %8) : (i128, i128) -> i128
    %131 = "llvm.mul"(%115, %10) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %132 = "llvm.mul"(%127, %9) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %133 = "llvm.add"(%131, %70) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %134 = "llvm.add"(%133, %132) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %135 = "llvm.add"(%134, %130) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %136 = "llvm.trunc"(%135) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %137 = "llvm.mul"(%136, %5) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %138 = "llvm.and"(%137, %6) : (i64, i64) -> i64
    %139 = "llvm.zext"(%138) <{nonNeg}> : (i64) -> i128
    %140 = "llvm.mul"(%139, %7) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %141 = "llvm.add"(%140, %135) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %142 = "llvm.lshr"(%141, %8) : (i128, i128) -> i128
    %143 = "llvm.shl"(%105, %11) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %144 = "llvm.mul"(%127, %10) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %145 = "llvm.mul"(%139, %9) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %146 = "llvm.add"(%85, %143) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %147 = "llvm.add"(%146, %144) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %148 = "llvm.add"(%147, %145) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %149 = "llvm.add"(%148, %142) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %150 = "llvm.trunc"(%149) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %151 = "llvm.mul"(%150, %5) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %152 = "llvm.and"(%151, %6) : (i64, i64) -> i64
    %153 = "llvm.zext"(%152) <{nonNeg}> : (i64) -> i128
    %154 = "llvm.mul"(%153, %7) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %155 = "llvm.add"(%154, %149) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %156 = "llvm.lshr"(%155, %8) : (i128, i128) -> i128
    %157 = "llvm.shl"(%115, %11) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %158 = "llvm.mul"(%139, %10) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %159 = "llvm.mul"(%153, %9) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %160 = "llvm.add"(%157, %92) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %161 = "llvm.add"(%160, %158) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %162 = "llvm.add"(%161, %159) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %163 = "llvm.add"(%162, %156) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %164 = "llvm.trunc"(%163) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %165 = "llvm.and"(%164, %6) : (i64, i64) -> i64
    %166 = "llvm.lshr"(%163, %8) : (i128, i128) -> i128
    %167 = "llvm.shl"(%127, %11) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %168 = "llvm.mul"(%153, %10) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %169 = "llvm.add"(%167, %97) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %170 = "llvm.add"(%169, %168) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %171 = "llvm.add"(%170, %166) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %172 = "llvm.trunc"(%171) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %173 = "llvm.and"(%172, %6) : (i64, i64) -> i64
    %174 = "llvm.lshr"(%171, %8) : (i128, i128) -> i128
    %175 = "llvm.shl"(%139, %11) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %176 = "llvm.add"(%175, %100) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %177 = "llvm.add"(%176, %174) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %178 = "llvm.trunc"(%177) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %179 = "llvm.and"(%178, %6) : (i64, i64) -> i64
    %180 = "llvm.lshr"(%177, %8) : (i128, i128) -> i128
    %181 = "llvm.shl"(%153, %11) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %182 = "llvm.add"(%181, %101) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %183 = "llvm.add"(%182, %180) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %184 = "llvm.trunc"(%183) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %185 = "llvm.and"(%184, %6) : (i64, i64) -> i64
    %186 = "llvm.lshr"(%183, %8) : (i128, i128) -> i128
    %187 = "llvm.trunc"(%186) <{overflowFlags = 0 : i32}> : (i128) -> i64
    %188 = "llvm.add"(%165, %12) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %189 = "llvm.and"(%188, %6) : (i64, i64) -> i64
    %190 = "llvm.ashr"(%188, %13) : (i64, i64) -> i64
    %191 = "llvm.add"(%190, %14) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %192 = "llvm.add"(%191, %173) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %193 = "llvm.and"(%192, %6) : (i64, i64) -> i64
    %194 = "llvm.ashr"(%192, %13) : (i64, i64) -> i64
    %195 = "llvm.add"(%194, %15) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %196 = "llvm.add"(%195, %179) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %197 = "llvm.and"(%196, %6) : (i64, i64) -> i64
    %198 = "llvm.ashr"(%196, %13) : (i64, i64) -> i64
    %199 = "llvm.add"(%185, %198) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %200 = "llvm.and"(%199, %6) : (i64, i64) -> i64
    %201 = "llvm.ashr"(%199, %13) : (i64, i64) -> i64
    %202 = "llvm.add"(%187, %16) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %203 = "llvm.add"(%202, %201) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %204 = "llvm.lshr"(%203, %13) : (i64, i64) -> i64
    %205 = "llvm.trunc"(%204) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %206 = "llvm.call"(%205) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}], callee = @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = none, inaccessibleMem = readwrite, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_inline, no_unwind, noalias_scopes = [#alias_scope3], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 1, 0>, res_attrs = [{llvm.noundef}]}> : (i8) -> i8
    %207 = "llvm.zext"(%206) : (i8) -> i64
    %208 = "llvm.sub"(%17, %207) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %209 = "llvm.and"(%208, %18) : (i64, i64) -> i64
    %210 = "llvm.add"(%189, %209) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %211 = "llvm.and"(%210, %6) : (i64, i64) -> i64
    %212 = "llvm.and"(%208, %19) : (i64, i64) -> i64
    %213 = "llvm.lshr"(%210, %20) : (i64, i64) -> i64
    %214 = "llvm.add"(%213, %212) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %215 = "llvm.add"(%214, %193) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %216 = "llvm.and"(%215, %6) : (i64, i64) -> i64
    %217 = "llvm.and"(%208, %21) : (i64, i64) -> i64
    %218 = "llvm.lshr"(%215, %20) : (i64, i64) -> i64
    %219 = "llvm.add"(%197, %217) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %220 = "llvm.add"(%219, %218) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %221 = "llvm.and"(%220, %6) : (i64, i64) -> i64
    %222 = "llvm.lshr"(%220, %20) : (i64, i64) -> i64
    %223 = "llvm.add"(%222, %200) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %224 = "llvm.and"(%223, %6) : (i64, i64) -> i64
    %225 = "llvm.and"(%208, %22) : (i64, i64) -> i64
    %226 = "llvm.lshr"(%223, %20) : (i64, i64) -> i64
    %227 = "llvm.add"(%203, %225) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %228 = "llvm.add"(%227, %226) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %229 = "llvm.and"(%228, %6) : (i64, i64) -> i64
    "llvm.store"(%211, %arg0) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope6, #alias_scope3], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %230 = "llvm.getelementptr"(%arg0, %1) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%216, %230) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope6, #alias_scope3], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %231 = "llvm.getelementptr"(%arg0, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%221, %231) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope6, #alias_scope3], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %232 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%224, %232) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope6, #alias_scope3], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %233 = "llvm.getelementptr"(%arg0, %4) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%229, %233) <{alias_scopes = [#alias_scope4], alignment = 8 : i64, noalias_scopes = [#alias_scope5, #alias_scope6, #alias_scope3], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%23, %24) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %25) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %26) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %27) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %28) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %29) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %30) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %31) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%23, %32) <{alias_scopes = [#alias_scope7], alignment = 16 : i64, noalias_scopes = [#alias_scope8], ordering = 0 : i64, volatile_}> : (i128, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.end"(%24) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%25) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%26) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%27) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%28) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%29) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%30) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%31) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%32) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519 := p.blackBoxByte

theorem block_count (p : Primitives) : (program p).n = 1 := rfl

end ScalarMontgomeryMul

end
end Agave.Ed25519.Verifier.Execution
