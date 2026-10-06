module

public import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionElab

/-! Exact pinned verifier regions. Regenerate with MLIR/import_sha512.py.

Only required symbol-name quoting changes the source spelling. `execution_def`
checks successful RIR translation, including calls and globals; it
does not supply any primitive's semantics or prove an execution result.
This is the original `scalar_from_sha512` body, including zeroization.
-/

namespace Agave.Ed25519.Verifier.Execution

open LeanMLIR.RIR
@[expose] public section

namespace SHA512Finalization

structure Primitives where
  /-- Exact external symbol `_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512`. -/
  sha512Compress : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])
  /-- Exact external symbol `_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide`. -/
  reduceWide : Vals [.ptr, .ptr] → EffectM (Vals [])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512" => some ⟨[.ptr, .ptr, .bv 64], [], p.sha512Compress⟩
  | "_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide" => some ⟨[.ptr, .ptr], [], p.reduceWide⟩
  | _ => none

execution_def program (p : Primitives) :=
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 208 : i64}> : () -> i64
    %2 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %5 = "llvm.mlir.constant"() <{value = 192 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 10 : i128}> : () -> i128
    %7 = "llvm.mlir.constant"() <{value = 3 : i128}> : () -> i128
    %8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %9 = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    %10 = "llvm.mlir.constant"() <{value = 112 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %13 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 144 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 168 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 176 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = 184 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 24 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 40 : i64}> : () -> i64
    %24 = "llvm.mlir.constant"() <{value = 48 : i64}> : () -> i64
    %25 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %26 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %27 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %28 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %29 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %30 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %31 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %32 = "llvm.mlir.constant"() <{value = 9 : i64}> : () -> i64
    %33 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %34 = "llvm.mlir.constant"() <{value = 11 : i64}> : () -> i64
    %35 = "llvm.mlir.constant"() <{value = 12 : i64}> : () -> i64
    %36 = "llvm.mlir.constant"() <{value = 13 : i64}> : () -> i64
    %37 = "llvm.mlir.constant"() <{value = 14 : i64}> : () -> i64
    %38 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %39 = "llvm.mlir.constant"() <{value = 17 : i64}> : () -> i64
    %40 = "llvm.mlir.constant"() <{value = 18 : i64}> : () -> i64
    %41 = "llvm.mlir.constant"() <{value = 19 : i64}> : () -> i64
    %42 = "llvm.mlir.constant"() <{value = 20 : i64}> : () -> i64
    %43 = "llvm.mlir.constant"() <{value = 21 : i64}> : () -> i64
    %44 = "llvm.mlir.constant"() <{value = 22 : i64}> : () -> i64
    %45 = "llvm.mlir.constant"() <{value = 23 : i64}> : () -> i64
    %46 = "llvm.mlir.constant"() <{value = 25 : i64}> : () -> i64
    %47 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %48 = "llvm.mlir.constant"() <{value = 27 : i64}> : () -> i64
    %49 = "llvm.mlir.constant"() <{value = 28 : i64}> : () -> i64
    %50 = "llvm.mlir.constant"() <{value = 29 : i64}> : () -> i64
    %51 = "llvm.mlir.constant"() <{value = 30 : i64}> : () -> i64
    %52 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %53 = "llvm.mlir.constant"() <{value = 33 : i64}> : () -> i64
    %54 = "llvm.mlir.constant"() <{value = 34 : i64}> : () -> i64
    %55 = "llvm.mlir.constant"() <{value = 35 : i64}> : () -> i64
    %56 = "llvm.mlir.constant"() <{value = 36 : i64}> : () -> i64
    %57 = "llvm.mlir.constant"() <{value = 37 : i64}> : () -> i64
    %58 = "llvm.mlir.constant"() <{value = 38 : i64}> : () -> i64
    %59 = "llvm.mlir.constant"() <{value = 39 : i64}> : () -> i64
    %60 = "llvm.mlir.constant"() <{value = 41 : i64}> : () -> i64
    %61 = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %62 = "llvm.mlir.constant"() <{value = 43 : i64}> : () -> i64
    %63 = "llvm.mlir.constant"() <{value = 44 : i64}> : () -> i64
    %64 = "llvm.mlir.constant"() <{value = 45 : i64}> : () -> i64
    %65 = "llvm.mlir.constant"() <{value = 46 : i64}> : () -> i64
    %66 = "llvm.mlir.constant"() <{value = 47 : i64}> : () -> i64
    %67 = "llvm.mlir.constant"() <{value = 49 : i64}> : () -> i64
    %68 = "llvm.mlir.constant"() <{value = 50 : i64}> : () -> i64
    %69 = "llvm.mlir.constant"() <{value = 51 : i64}> : () -> i64
    %70 = "llvm.mlir.constant"() <{value = 52 : i64}> : () -> i64
    %71 = "llvm.mlir.constant"() <{value = 53 : i64}> : () -> i64
    %72 = "llvm.mlir.constant"() <{value = 54 : i64}> : () -> i64
    %73 = "llvm.mlir.constant"() <{value = 55 : i64}> : () -> i64
    %74 = "llvm.mlir.constant"() <{value = 57 : i64}> : () -> i64
    %75 = "llvm.mlir.constant"() <{value = 58 : i64}> : () -> i64
    %76 = "llvm.mlir.constant"() <{value = 59 : i64}> : () -> i64
    %77 = "llvm.mlir.constant"() <{value = 60 : i64}> : () -> i64
    %78 = "llvm.mlir.constant"() <{value = 61 : i64}> : () -> i64
    %79 = "llvm.mlir.constant"() <{value = 62 : i64}> : () -> i64
    %80 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %81 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<128 x i8>}> : (i32) -> !llvm.ptr
    %82 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<128 x i8>}> : (i32) -> !llvm.ptr
    %83 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<128 x i8>}> : (i32) -> !llvm.ptr
    %84 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<128 x i8>}> : (i32) -> !llvm.ptr
    %85 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<64 x i8>}> : (i32) -> !llvm.ptr
    %86 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<208 x i8>}> : (i32) -> !llvm.ptr
    %87 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %88 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %89 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %90 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %91 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %92 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %93 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %94 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %95 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %96 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %97 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %98 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %99 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %100 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %101 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %102 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %103 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %104 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %105 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %106 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %107 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %108 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %109 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %110 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %111 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %112 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %113 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %114 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %115 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %116 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %117 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %118 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %119 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %120 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %121 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %122 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %123 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %124 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %125 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %126 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %127 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %128 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %129 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %130 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %131 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %132 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %133 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %134 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %135 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %136 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %137 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %138 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %139 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %140 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %141 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %142 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %143 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %144 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %145 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %146 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %147 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %148 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %149 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    %150 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = i8}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%87) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%88) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%89) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%90) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%91) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%92) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%93) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%94) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%95) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%96) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%97) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%98) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%99) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%100) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%101) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%102) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%103) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%104) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%105) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%106) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%107) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%108) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%109) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%110) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%111) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%112) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%113) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%114) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%115) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%116) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%117) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%118) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%119) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%120) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%121) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%122) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%123) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%124) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%125) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%126) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%127) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%128) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%129) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%130) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%131) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%132) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%133) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%134) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%135) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%136) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%137) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%138) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%139) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%140) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%141) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%142) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%143) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%144) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%145) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%146) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%147) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%148) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%149) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%150) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%86) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%86, %arg1, %1) <{arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 16 : i64, llvm.dereferenceable = 208 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %151 = "llvm.getelementptr"(%86, %2) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope1}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope2}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope3}> : () -> ()
    "llvm.intr.lifetime.start"(%84) : (!llvm.ptr) -> ()
    %152 = "llvm.getelementptr"(%86, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %153 = "llvm.load"(%152) <{alias_scopes = [#alias_scope3, #alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %154 = "llvm.icmp"(%153, %4) <{predicate = 4 : i64}> : (i8, i8) -> i1
    "llvm.intr.assume"(%154) <{op_bundle_sizes = array<i32>, op_bundle_tags = []}> : (i1) -> ()
    %155 = "llvm.zext"(%153) <{nonNeg}> : (i8) -> i128
    %156 = "llvm.getelementptr"(%86, %5) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %157 = "llvm.load"(%156) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i128
    %158 = "llvm.shl"(%157, %6) <{overflowFlags = 0 : i32}> : (i128, i128) -> i128
    %159 = "llvm.shl"(%155, %7) <{overflowFlags = 3 : i32}> : (i128, i128) -> i128
    %160 = "llvm.or"(%158, %159) <{isDisjoint}> : (i128, i128) -> i128
    %161 = "llvm.intr.bswap"(%160) : (i128) -> i128
    %162 = "llvm.zext"(%153) <{nonNeg}> : (i8) -> i64
    "llvm.intr.memset"(%84, %8, %2) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%84, %86, %162) <{arg_attrs = [{llvm.align = 1 : i64, llvm.nonnull}, {llvm.align = 16 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.readonly}, {llvm.range = #llvm.constant_range<i64, 0, -9223372036854775808>}], isVolatile = false, noalias_scopes = [#alias_scope2, #alias_scope4, #alias_scope, #alias_scope5]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %163 = "llvm.getelementptr"(%84, %162) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%9, %163) <{alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %164 = "llvm.xor"(%162, %10) : (i64, i64) -> i64
    %165 = "llvm.icmp"(%164, %11) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%165)[^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:  // pred: ^bb0
    "llvm.intr.lifetime.start"(%83) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%83, %84, %2) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.call"(%151, %83, %12) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope6, #alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%83) : (!llvm.ptr) -> ()
    "llvm.intr.memset"(%84, %8, %10) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5]}> : (!llvm.ptr, i8, i64) -> ()
    %166 = "llvm.getelementptr"(%84, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%161, %166) <{alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%82) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%82, %84, %2) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.call"(%151, %82, %12) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope7, #alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%82) : (!llvm.ptr) -> ()
    "llvm.br"()[^bb3] : () -> ()
  ^bb2:  // pred: ^bb0
    %167 = "llvm.getelementptr"(%84, %10) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%161, %167) <{alignment = 1 : i64, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (i128, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%81) : (!llvm.ptr) -> ()
    "llvm.intr.memcpy"(%81, %84, %2) <{arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 128 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope2, #alias_scope3, #alias_scope4, #alias_scope, #alias_scope1, #alias_scope5]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.call"(%151, %81, %12) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 16 : i64, llvm.dereferenceable = 80 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.noundef}], callee = @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512, fastmathFlags = #llvm.fastmath<none>, no_unwind, noalias_scopes = [#alias_scope8, #alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%81) : (!llvm.ptr) -> ()
    "llvm.br"()[^bb3] : () -> ()
  ^bb3:  // 2 preds: ^bb1, ^bb2
    "llvm.store"(%8, %152) <{alias_scopes = [#alias_scope9, #alias_scope3, #alias_scope1], alignment = 1 : i64, noalias_scopes = [#alias_scope10, #alias_scope11, #alias_scope2, #alias_scope4, #alias_scope, #alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %168 = "llvm.load"(%151) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %169 = "llvm.intr.bswap"(%168) : (i64) -> i64
    %170 = "llvm.getelementptr"(%86, %13) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %171 = "llvm.load"(%170) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %172 = "llvm.intr.bswap"(%171) : (i64) -> i64
    %173 = "llvm.getelementptr"(%86, %14) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %174 = "llvm.load"(%173) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %175 = "llvm.intr.bswap"(%174) : (i64) -> i64
    %176 = "llvm.getelementptr"(%86, %15) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %177 = "llvm.load"(%176) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %178 = "llvm.intr.bswap"(%177) : (i64) -> i64
    %179 = "llvm.getelementptr"(%86, %16) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %180 = "llvm.load"(%179) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %181 = "llvm.intr.bswap"(%180) : (i64) -> i64
    %182 = "llvm.getelementptr"(%86, %17) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %183 = "llvm.load"(%182) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %184 = "llvm.intr.bswap"(%183) : (i64) -> i64
    %185 = "llvm.getelementptr"(%86, %18) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %186 = "llvm.load"(%185) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 16 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %187 = "llvm.intr.bswap"(%186) : (i64) -> i64
    %188 = "llvm.getelementptr"(%86, %19) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %189 = "llvm.load"(%188) <{alias_scopes = [#alias_scope2, #alias_scope], alignment = 8 : i64, noalias_scopes = [#alias_scope3, #alias_scope4, #alias_scope1, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %190 = "llvm.intr.bswap"(%189) : (i64) -> i64
    "llvm.intr.lifetime.end"(%84) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%86) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%85) : (!llvm.ptr) -> ()
    "llvm.store"(%169, %85) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %191 = "llvm.getelementptr"(%85, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%172, %191) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %192 = "llvm.getelementptr"(%85, %11) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%175, %192) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %193 = "llvm.getelementptr"(%85, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%178, %193) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %194 = "llvm.getelementptr"(%85, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%181, %194) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %195 = "llvm.getelementptr"(%85, %23) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%184, %195) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %196 = "llvm.getelementptr"(%85, %24) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%187, %196) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %197 = "llvm.getelementptr"(%85, %25) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%190, %197) <{alias_scopes = [#alias_scope12, #alias_scope13], alignment = 8 : i64, noalias_scopes = [#alias_scope14], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.call"(%arg0, %85) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<32 x i8>}, {llvm.dereferenceable = 64 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide, fastmathFlags = #llvm.fastmath<none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%8, %87) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %88) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %89) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %90) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %91) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %92) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %93) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %94) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %95) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %96) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %97) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %98) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %99) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %100) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %101) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %102) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %103) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %104) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %105) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %106) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %107) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %108) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %109) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %110) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %111) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %112) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %113) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %114) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %115) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %116) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %117) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %118) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %119) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %120) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %121) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %122) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %123) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %124) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %125) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %126) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %127) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %128) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %129) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %130) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %131) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %132) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %133) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %134) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %135) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %136) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %137) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %138) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %139) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %140) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %141) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %142) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %143) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %144) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %145) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %146) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %147) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %148) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %149) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%8, %150) <{alias_scopes = [#alias_scope15], alignment = 1 : i64, ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %85) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %198 = "llvm.getelementptr"(%85, %12) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %198) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %199 = "llvm.getelementptr"(%85, %26) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %199) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %200 = "llvm.getelementptr"(%85, %27) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %200) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %201 = "llvm.getelementptr"(%85, %28) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %201) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %202 = "llvm.getelementptr"(%85, %29) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %202) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %203 = "llvm.getelementptr"(%85, %30) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %203) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %204 = "llvm.getelementptr"(%85, %31) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %204) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %191) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %205 = "llvm.getelementptr"(%85, %32) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %205) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %206 = "llvm.getelementptr"(%85, %33) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %206) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %207 = "llvm.getelementptr"(%85, %34) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %207) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %208 = "llvm.getelementptr"(%85, %35) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %208) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %209 = "llvm.getelementptr"(%85, %36) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %209) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %210 = "llvm.getelementptr"(%85, %37) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %210) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %211 = "llvm.getelementptr"(%85, %38) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %211) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %192) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %212 = "llvm.getelementptr"(%85, %39) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %212) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %213 = "llvm.getelementptr"(%85, %40) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %213) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %214 = "llvm.getelementptr"(%85, %41) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %214) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %215 = "llvm.getelementptr"(%85, %42) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %215) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %216 = "llvm.getelementptr"(%85, %43) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %216) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %217 = "llvm.getelementptr"(%85, %44) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %217) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %218 = "llvm.getelementptr"(%85, %45) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %218) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %193) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %219 = "llvm.getelementptr"(%85, %46) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %219) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %220 = "llvm.getelementptr"(%85, %47) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %220) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %221 = "llvm.getelementptr"(%85, %48) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %221) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %222 = "llvm.getelementptr"(%85, %49) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %222) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %223 = "llvm.getelementptr"(%85, %50) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %223) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %224 = "llvm.getelementptr"(%85, %51) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %224) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %225 = "llvm.getelementptr"(%85, %52) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %225) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %194) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %226 = "llvm.getelementptr"(%85, %53) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %226) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %227 = "llvm.getelementptr"(%85, %54) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %227) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %228 = "llvm.getelementptr"(%85, %55) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %228) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %229 = "llvm.getelementptr"(%85, %56) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %229) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %230 = "llvm.getelementptr"(%85, %57) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %230) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %231 = "llvm.getelementptr"(%85, %58) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %231) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %232 = "llvm.getelementptr"(%85, %59) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %232) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %195) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %233 = "llvm.getelementptr"(%85, %60) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %233) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %234 = "llvm.getelementptr"(%85, %61) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %234) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %235 = "llvm.getelementptr"(%85, %62) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %235) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %236 = "llvm.getelementptr"(%85, %63) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %236) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %237 = "llvm.getelementptr"(%85, %64) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %237) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %238 = "llvm.getelementptr"(%85, %65) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %238) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %239 = "llvm.getelementptr"(%85, %66) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %239) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %196) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %240 = "llvm.getelementptr"(%85, %67) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %240) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %241 = "llvm.getelementptr"(%85, %68) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %241) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %242 = "llvm.getelementptr"(%85, %69) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %242) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %243 = "llvm.getelementptr"(%85, %70) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %243) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %244 = "llvm.getelementptr"(%85, %71) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %244) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %245 = "llvm.getelementptr"(%85, %72) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %245) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %246 = "llvm.getelementptr"(%85, %73) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %246) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.store"(%8, %197) <{alias_scopes = [#alias_scope16], alignment = 8 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %247 = "llvm.getelementptr"(%85, %74) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %247) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %248 = "llvm.getelementptr"(%85, %75) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %248) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %249 = "llvm.getelementptr"(%85, %76) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %249) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %250 = "llvm.getelementptr"(%85, %77) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %250) <{alias_scopes = [#alias_scope16], alignment = 4 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %251 = "llvm.getelementptr"(%85, %78) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %251) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %252 = "llvm.getelementptr"(%85, %79) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %252) <{alias_scopes = [#alias_scope16], alignment = 2 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    %253 = "llvm.getelementptr"(%85, %80) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%8, %253) <{alias_scopes = [#alias_scope16], alignment = 1 : i64, noalias_scopes = [#alias_scope17], ordering = 0 : i64, volatile_}> : (i8, !llvm.ptr) -> ()
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.intr.lifetime.end"(%85) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%87) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%88) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%89) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%90) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%91) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%92) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%93) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%94) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%95) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%96) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%97) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%98) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%99) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%100) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%101) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%102) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%103) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%104) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%105) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%106) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%107) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%108) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%109) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%110) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%111) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%112) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%113) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%114) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%115) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%116) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%117) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%118) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%119) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%120) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%121) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%122) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%123) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%124) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%125) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%126) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%127) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%128) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%129) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%130) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%131) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%132) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%133) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%134) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%135) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%136) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%137) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%138) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%139) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%140) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%141) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%142) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%143) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%144) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%145) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%146) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%147) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%148) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%149) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%150) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}
with @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512 := p.sha512Compress,
  @_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide := p.reduceWide

theorem block_count (p : Primitives) : (program p).n = 4 := rfl

end SHA512Finalization

end
end Agave.Ed25519.Verifier.Execution
