module

public import SSA.Projects.RIR.Syntax.Elab

/-! Complete pinned compiler CFG, copied without instruction changes.
Regenerate using import_cfg.py. The source MLIR and all source constants
remain in MLIR/generated; the extraction manifest records provenance.

`program` is a checked import attempt, not a successful-refinement theorem.
Each external primitive has its exact call-site signature and each global
address is explicit. Primitive behavior, memory separation, table contents,
allocation invariants and termination remain independent proof obligations.
-/

namespace Agave.Ed25519.DoubleBase.Avx2CFG

open LeanMLIR.RIR
@[expose] public section

structure Primitives where
  /-- `_RNvXNvXsk_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsINtNtBg_6window15NafLookupTable5NtB8_11CachedPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtBg_7edwards12EdwardsPointE4fromB1c_NtB2_13___Impl_from__10__impl_from` -/
  call0 : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D` -/
  call1 : Vals [.ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul` -/
  call2 : Vals [.ptr, .ptr, .ptr] → EffectM (Vals [])
  /-- `_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check` -/
  call3 : Vals [.bv 64, .bv 64, .ptr] → EffectM (Vals [])

def Primitives.resolve (p : Primitives) : String → Option Callee
  | "_RNvXNvXsk_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsINtNtBg_6window15NafLookupTable5NtB8_11CachedPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtBg_7edwards12EdwardsPointE4fromB1c_NtB2_13___Impl_from__10__impl_from" => some ⟨[.ptr, .ptr], [], p.call0⟩
  | "_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D" => some ⟨[.ptr, .ptr], [], p.call1⟩
  | "_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul" => some ⟨[.ptr, .ptr, .ptr], [], p.call2⟩
  | "_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check" => some ⟨[.bv 64, .bv 64, .ptr], [], p.call3⟩
  | _ => none

structure Globals where
  /-- `alloc_a8fabae8f73f66aef6660ad7c9447c5d`; its source initializer must be present in memory. -/
  address0 : Pointer
  /-- `alloc_f7b128ba219626851d37833adc9e2368`; its source initializer must be present in memory. -/
  address1 : Pointer
  /-- `_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE`; its source initializer must be present in memory. -/
  address2 : Pointer

def Globals.resolve (g : Globals) : String → Option Pointer
  | "alloc_a8fabae8f73f66aef6660ad7c9447c5d" => some g.address0
  | "alloc_f7b128ba219626851d37833adc9e2368" => some g.address1
  | "_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE" => some g.address2
  | _ => none

def region : MLIR.Region := mlir_region%
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr, %arg2: !llvm.ptr, %arg3: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %2 = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i64
    %3 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %4 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %5 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %6 = "llvm.mlir.constant"() <{value = 63 : i64}> : () -> i64
    %7 = "llvm.mlir.constant"() <{value = 59 : i64}> : () -> i64
    %8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %9 = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    %10 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %11 = "llvm.mlir.constant"() <{value = 15 : i64}> : () -> i64
    %12 = "llvm.mlir.constant"() <{value = -32 : i8}> : () -> i8
    %13 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %14 = "llvm.mlir.constant"() <{value = 251 : i64}> : () -> i64
    %15 = "llvm.mlir.constant"() <{value = 56 : i64}> : () -> i64
    %16 = "llvm.mlir.constant"() <{value = 255 : i64}> : () -> i64
    %17 = "llvm.mlir.constant"() <{value = 127 : i64}> : () -> i64
    %18 = "llvm.mlir.constant"() <{value = 248 : i64}> : () -> i64
    %19 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %20 = "llvm.mlir.constant"() <{value = 64 : i64}> : () -> i64
    %21 = "llvm.mlir.constant"() <{value = 96 : i64}> : () -> i64
    %22 = "llvm.mlir.constant"() <{value = 128 : i64}> : () -> i64
    %23 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %24 = "llvm.mlir.constant"() <{value = dense<0> : vector<8xi32>}> : () -> vector<8xi32>
    %25 = "llvm.mlir.constant"() <{value = dense<[0, 1, 0, 0, 1, 0, 0, 0]> : vector<8xi32>}> : () -> vector<8xi32>
    %26 = "llvm.mlir.poison"() : () -> vector<8xi32>
    %27 = "llvm.mlir.constant"() <{value = dense<1> : vector<8xi32>}> : () -> vector<8xi32>
    %28 = "llvm.mlir.poison"() : () -> i32
    %29 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %30 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %31 = "llvm.insertelement"(%29, %23, %30) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %33 = "llvm.insertelement"(%31, %23, %32) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %34 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %35 = "llvm.insertelement"(%33, %23, %34) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %36 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %37 = "llvm.insertelement"(%35, %23, %36) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %38 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %39 = "llvm.insertelement"(%37, %28, %38) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %40 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %41 = "llvm.insertelement"(%39, %28, %40) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %42 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %43 = "llvm.insertelement"(%41, %28, %42) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %44 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %45 = "llvm.insertelement"(%43, %28, %44) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %46 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %47 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %48 = "llvm.insertelement"(%46, %28, %47) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %49 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %50 = "llvm.insertelement"(%48, %23, %49) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %51 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %52 = "llvm.insertelement"(%50, %28, %51) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %53 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %54 = "llvm.insertelement"(%52, %23, %53) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %55 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %56 = "llvm.insertelement"(%54, %23, %55) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %57 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %58 = "llvm.insertelement"(%56, %28, %57) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %59 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %60 = "llvm.insertelement"(%58, %23, %59) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %61 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %62 = "llvm.insertelement"(%60, %28, %61) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %63 = "llvm.mlir.constant"() <{value = 67108862 : i32}> : () -> i32
    %64 = "llvm.mlir.constant"() <{value = 134217690 : i32}> : () -> i32
    %65 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %66 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %67 = "llvm.insertelement"(%65, %28, %66) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %68 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %69 = "llvm.insertelement"(%67, %64, %68) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %70 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %71 = "llvm.insertelement"(%69, %28, %70) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %72 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %73 = "llvm.insertelement"(%71, %63, %72) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %74 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %75 = "llvm.insertelement"(%73, %64, %74) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %76 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %77 = "llvm.insertelement"(%75, %28, %76) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %78 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %79 = "llvm.insertelement"(%77, %63, %78) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %80 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %81 = "llvm.insertelement"(%79, %28, %80) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %82 = "llvm.mlir.constant"() <{value = 134217726 : i32}> : () -> i32
    %83 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %84 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %85 = "llvm.insertelement"(%83, %28, %84) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %86 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %87 = "llvm.insertelement"(%85, %82, %86) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %88 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %89 = "llvm.insertelement"(%87, %28, %88) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %90 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %91 = "llvm.insertelement"(%89, %63, %90) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %92 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %93 = "llvm.insertelement"(%91, %82, %92) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %94 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %95 = "llvm.insertelement"(%93, %28, %94) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %96 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %97 = "llvm.insertelement"(%95, %63, %96) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %98 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %99 = "llvm.insertelement"(%97, %28, %98) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %100 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %101 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %102 = "llvm.insertelement"(%100, %23, %101) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %103 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %104 = "llvm.insertelement"(%102, %28, %103) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %105 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %106 = "llvm.insertelement"(%104, %23, %105) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %107 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %108 = "llvm.insertelement"(%106, %28, %107) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %109 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %110 = "llvm.insertelement"(%108, %28, %109) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %111 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %112 = "llvm.insertelement"(%110, %23, %111) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %113 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %114 = "llvm.insertelement"(%112, %28, %113) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %115 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %116 = "llvm.insertelement"(%114, %23, %115) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %117 = "llvm.mlir.constant"() <{value = 16 : i8}> : () -> i8
    %118 = "llvm.mlir.addressof"() <{global_name = @alloc_a8fabae8f73f66aef6660ad7c9447c5d}> : () -> !llvm.ptr
    %119 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %120 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %121 = "llvm.insertelement"(%119, %64, %120) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %122 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %123 = "llvm.insertelement"(%121, %28, %122) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %124 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %125 = "llvm.insertelement"(%123, %63, %124) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %126 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %127 = "llvm.insertelement"(%125, %28, %126) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %128 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %129 = "llvm.insertelement"(%127, %28, %128) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %130 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %131 = "llvm.insertelement"(%129, %28, %130) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %132 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %133 = "llvm.insertelement"(%131, %28, %132) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %134 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %135 = "llvm.insertelement"(%133, %28, %134) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %136 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %137 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %138 = "llvm.insertelement"(%136, %82, %137) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %139 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %140 = "llvm.insertelement"(%138, %28, %139) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %141 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %142 = "llvm.insertelement"(%140, %63, %141) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %143 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %144 = "llvm.insertelement"(%142, %28, %143) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %145 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %146 = "llvm.insertelement"(%144, %28, %145) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %147 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %148 = "llvm.insertelement"(%146, %28, %147) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %149 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %150 = "llvm.insertelement"(%148, %28, %149) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %151 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %152 = "llvm.insertelement"(%150, %28, %151) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %153 = "llvm.mlir.constant"() <{value = 160 : i64}> : () -> i64
    %154 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %155 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %156 = "llvm.insertelement"(%154, %64, %155) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %157 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %158 = "llvm.insertelement"(%156, %28, %157) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %159 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %160 = "llvm.insertelement"(%158, %63, %159) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %161 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %162 = "llvm.insertelement"(%160, %28, %161) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %163 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %164 = "llvm.insertelement"(%162, %64, %163) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %165 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %166 = "llvm.insertelement"(%164, %28, %165) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %167 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %168 = "llvm.insertelement"(%166, %63, %167) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %169 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %170 = "llvm.insertelement"(%168, %28, %169) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %171 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %172 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %173 = "llvm.insertelement"(%171, %82, %172) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %174 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %175 = "llvm.insertelement"(%173, %28, %174) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %176 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %177 = "llvm.insertelement"(%175, %63, %176) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %178 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %179 = "llvm.insertelement"(%177, %28, %178) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %180 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %181 = "llvm.insertelement"(%179, %82, %180) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %182 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %183 = "llvm.insertelement"(%181, %28, %182) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %184 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %185 = "llvm.insertelement"(%183, %63, %184) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %186 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %187 = "llvm.insertelement"(%185, %28, %186) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %188 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %189 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %190 = "llvm.insertelement"(%188, %28, %189) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %191 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %192 = "llvm.insertelement"(%190, %28, %191) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %193 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %194 = "llvm.insertelement"(%192, %28, %193) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %195 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %196 = "llvm.insertelement"(%194, %28, %195) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %197 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %198 = "llvm.insertelement"(%196, %28, %197) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %199 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %200 = "llvm.insertelement"(%198, %64, %199) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %201 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %202 = "llvm.insertelement"(%200, %28, %201) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %203 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %204 = "llvm.insertelement"(%202, %63, %203) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %205 = "llvm.mlir.undef"() : () -> vector<8xi32>
    %206 = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %207 = "llvm.insertelement"(%205, %28, %206) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %208 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %209 = "llvm.insertelement"(%207, %28, %208) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %210 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %211 = "llvm.insertelement"(%209, %28, %210) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %212 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %213 = "llvm.insertelement"(%211, %28, %212) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %214 = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %215 = "llvm.insertelement"(%213, %28, %214) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %216 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %217 = "llvm.insertelement"(%215, %82, %216) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %218 = "llvm.mlir.constant"() <{value = 6 : i32}> : () -> i32
    %219 = "llvm.insertelement"(%217, %28, %218) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %220 = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %221 = "llvm.insertelement"(%219, %63, %220) : (vector<8xi32>, i32, i32) -> vector<8xi32>
    %222 = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %223 = "llvm.mlir.addressof"() <{global_name = @alloc_f7b128ba219626851d37833adc9e2368}> : () -> !llvm.ptr
    %224 = "llvm.mlir.addressof"() <{global_name = @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE}> : () -> !llvm.ptr
    %225 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %226 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %227 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %228 = "llvm.mlir.constant"() <{value = 26 : i64}> : () -> i64
    %229 = "llvm.mlir.constant"() <{value = dense<26> : vector<2xi64>}> : () -> vector<2xi64>
    %230 = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %231 = "llvm.mlir.constant"() <{value = dense<26> : vector<4xi64>}> : () -> vector<4xi64>
    %232 = "llvm.mlir.constant"() <{value = 72 : i64}> : () -> i64
    %233 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %234 = "llvm.mlir.constant"() <{value = 104 : i64}> : () -> i64
    %235 = "llvm.mlir.constant"() <{value = 136 : i64}> : () -> i64
    %236 = "llvm.mlir.constant"() <{value = 152 : i64}> : () -> i64
    %237 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %238 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %239 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %240 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %241 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %242 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %243 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %244 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %245 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %246 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %247 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %248 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %249 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %250 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %251 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %252 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %253 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %254 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %255 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %256 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %257 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %258 = "llvm.alloca"(%0) <{alignment = 8 : i64, elem_type = !llvm.array<40 x i8>}> : (i32) -> !llvm.ptr
    %259 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %260 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %261 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %262 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %263 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<160 x i8>}> : (i32) -> !llvm.ptr
    %264 = "llvm.alloca"(%0) <{alignment = 32 : i64, elem_type = !llvm.array<1280 x i8>}> : (i32) -> !llvm.ptr
    %265 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<256 x i8>}> : (i32) -> !llvm.ptr
    %266 = "llvm.alloca"(%0) <{alignment = 1 : i64, elem_type = !llvm.array<256 x i8>}> : (i32) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%266) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope}> : () -> ()
    "llvm.intr.memset"(%266, %1, %2) <{alias_scopes = [#alias_scope], arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 256 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope1]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.lifetime.start"(%258) : (!llvm.ptr) -> ()
    %267 = "llvm.getelementptr"(%258, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%4, %267) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%258, %arg1, %3) <{alias_scopes = [#alias_scope2, #alias_scope3], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%4, %4)[^bb1] : (i64, i64) -> ()
  ^bb1(%268: i64, %269: i64):  // 2 preds: ^bb0, ^bb6
    "llvm.br"(%268)[^bb2] : (i64) -> ()
  ^bb2(%270: i64):  // 2 preds: ^bb1, ^bb5
    %271 = "llvm.lshr"(%270, %5) : (i64, i64) -> i64
    %272 = "llvm.and"(%270, %6) : (i64, i64) -> i64
    %273 = "llvm.icmp"(%272, %7) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %274 = "llvm.getelementptr"(%258, %271) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %275 = "llvm.load"(%274) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %276 = "llvm.lshr"(%275, %272) : (i64, i64) -> i64
    "llvm.cond_br"(%273, %276)[^bb4, ^bb3] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb3:  // pred: ^bb2
    %277 = "llvm.getelementptr"(%274, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %278 = "llvm.load"(%277) <{alignment = 8 : i64, noalias_scopes = [#alias_scope, #alias_scope1], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %279 = "llvm.sub"(%4, %270) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %280 = "llvm.and"(%279, %6) : (i64, i64) -> i64
    %281 = "llvm.shl"(%278, %280) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %282 = "llvm.or"(%281, %276) : (i64, i64) -> i64
    "llvm.br"(%282)[^bb4] : (i64) -> ()
  ^bb4(%283: i64):  // 2 preds: ^bb2, ^bb3
    %284 = "llvm.and"(%283, %9) : (i64, i64) -> i64
    %285 = "llvm.add"(%284, %269) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %286 = "llvm.and"(%285, %10) : (i64, i64) -> i64
    %287 = "llvm.icmp"(%286, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%287)[^bb5, ^bb6] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb5:  // pred: ^bb4
    %288 = "llvm.add"(%270, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %289 = "llvm.icmp"(%288, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%289, %288)[^bb7, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb6:  // pred: ^bb4
    %290 = "llvm.icmp"(%285, %11) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %291 = "llvm.trunc"(%285) <{overflowFlags = 3 : i32}> : (i64) -> i8
    %292 = "llvm.select"(%290, %12, %1) <{fastmathFlags = #llvm.fastmath<none>}> : (i1, i8, i8) -> i8
    %293 = "llvm.add"(%292, %291) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %294 = "llvm.zext"(%290) : (i1) -> i64
    %295 = "llvm.getelementptr"(%266, %270) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%293, %295) <{alias_scopes = [#alias_scope], alignment = 1 : i64, noalias_scopes = [#alias_scope1], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %296 = "llvm.add"(%270, %13) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %297 = "llvm.icmp"(%270, %14) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%297, %296, %294)[^bb1, ^bb7] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i64, i64) -> ()
  ^bb7:  // 2 preds: ^bb5, ^bb6
    "llvm.intr.lifetime.end"(%258) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%265) : (!llvm.ptr) -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope4}> : () -> ()
    "llvm.intr.memset"(%265, %1, %2) <{alias_scopes = [#alias_scope4], arg_attrs = [{llvm.align = 1 : i64, llvm.dereferenceable = 256 : i64, llvm.nonnull, llvm.noundef}, {}, {}], isVolatile = false, noalias_scopes = [#alias_scope5]}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.lifetime.start"(%257) : (!llvm.ptr) -> ()
    %298 = "llvm.getelementptr"(%257, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%4, %298) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%257, %arg3, %3) <{alias_scopes = [#alias_scope6, #alias_scope7], arg_attrs = [{llvm.align = 8 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 1 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef, llvm.readonly}, {}], isVolatile = false, noalias_scopes = [#alias_scope4]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.br"(%4, %4)[^bb8] : (i64, i64) -> ()
  ^bb8(%299: i64, %300: i64):  // 2 preds: ^bb7, ^bb13
    "llvm.br"(%299)[^bb9] : (i64) -> ()
  ^bb9(%301: i64):  // 2 preds: ^bb8, ^bb12
    %302 = "llvm.lshr"(%301, %5) : (i64, i64) -> i64
    %303 = "llvm.and"(%301, %6) : (i64, i64) -> i64
    %304 = "llvm.icmp"(%303, %15) <{predicate = 6 : i64}> : (i64, i64) -> i1
    %305 = "llvm.getelementptr"(%257, %302) <{elem_type = i64, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %306 = "llvm.load"(%305) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %307 = "llvm.lshr"(%306, %303) : (i64, i64) -> i64
    "llvm.cond_br"(%304, %307)[^bb11, ^bb10] <{operandSegmentSizes = array<i32: 1, 1, 0>}> : (i1, i64) -> ()
  ^bb10:  // pred: ^bb9
    %308 = "llvm.getelementptr"(%305, %8) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %309 = "llvm.load"(%308) <{alignment = 8 : i64, noalias_scopes = [#alias_scope4, #alias_scope5], ordering = 0 : i64}> : (!llvm.ptr) -> i64
    %310 = "llvm.sub"(%4, %301) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %311 = "llvm.and"(%310, %6) : (i64, i64) -> i64
    %312 = "llvm.shl"(%309, %311) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %313 = "llvm.or"(%312, %307) : (i64, i64) -> i64
    "llvm.br"(%313)[^bb11] : (i64) -> ()
  ^bb11(%314: i64):  // 2 preds: ^bb9, ^bb10
    %315 = "llvm.and"(%314, %16) : (i64, i64) -> i64
    %316 = "llvm.add"(%315, %300) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %317 = "llvm.and"(%316, %10) : (i64, i64) -> i64
    %318 = "llvm.icmp"(%317, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%318)[^bb12, ^bb13] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb12:  // pred: ^bb11
    %319 = "llvm.add"(%301, %10) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %320 = "llvm.icmp"(%319, %2) <{predicate = 0 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%320, %319)[^bb14, ^bb9] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb13:  // pred: ^bb11
    %321 = "llvm.icmp"(%316, %17) <{predicate = 8 : i64}> : (i64, i64) -> i1
    %322 = "llvm.trunc"(%316) <{overflowFlags = 0 : i32}> : (i64) -> i8
    %323 = "llvm.zext"(%321) : (i1) -> i64
    %324 = "llvm.getelementptr"(%265, %301) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%322, %324) <{alias_scopes = [#alias_scope4], alignment = 1 : i64, noalias_scopes = [#alias_scope5], ordering = 0 : i64}> : (i8, !llvm.ptr) -> ()
    %325 = "llvm.add"(%301, %8) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %326 = "llvm.icmp"(%301, %18) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "llvm.cond_br"(%326, %325, %323)[^bb8, ^bb14] <{operandSegmentSizes = array<i32: 1, 2, 0>}> : (i1, i64, i64) -> ()
  ^bb14:  // 2 preds: ^bb12, ^bb13
    "llvm.intr.lifetime.end"(%257) : (!llvm.ptr) -> ()
    "llvm.br"(%2)[^bb16] : (i64) -> ()
  ^bb15:  // 2 preds: ^bb16, ^bb17
    "llvm.intr.lifetime.start"(%264) : (!llvm.ptr) -> ()
    "llvm.call"(%264, %arg2) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 1280 : i64, llvm.noalias, llvm.nocapture, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<1280 x i8>}, {llvm.align = 8 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsk_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsINtNtBg_6window15NafLookupTable5NtB8_11CachedPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtBg_7edwards12EdwardsPointE4fromB1c_NtB2_13___Impl_from__10__impl_from, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %327 = "llvm.getelementptr"(%256, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %328 = "llvm.getelementptr"(%256, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %329 = "llvm.getelementptr"(%256, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %330 = "llvm.getelementptr"(%256, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %331 = "llvm.getelementptr"(%255, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %332 = "llvm.getelementptr"(%255, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %333 = "llvm.getelementptr"(%255, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %334 = "llvm.getelementptr"(%255, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %335 = "llvm.getelementptr"(%263, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %336 = "llvm.getelementptr"(%263, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %337 = "llvm.getelementptr"(%263, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %338 = "llvm.getelementptr"(%263, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %339 = "llvm.getelementptr"(%249, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %340 = "llvm.getelementptr"(%249, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %341 = "llvm.getelementptr"(%249, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %342 = "llvm.getelementptr"(%249, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %343 = "llvm.getelementptr"(%247, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %344 = "llvm.getelementptr"(%247, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %345 = "llvm.getelementptr"(%247, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %346 = "llvm.getelementptr"(%247, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %347 = "llvm.getelementptr"(%246, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %348 = "llvm.getelementptr"(%246, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %349 = "llvm.getelementptr"(%246, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %350 = "llvm.getelementptr"(%246, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %351 = "llvm.getelementptr"(%262, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %352 = "llvm.getelementptr"(%262, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %353 = "llvm.getelementptr"(%262, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %354 = "llvm.getelementptr"(%262, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %355 = "llvm.getelementptr"(%254, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %356 = "llvm.getelementptr"(%254, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %357 = "llvm.getelementptr"(%254, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %358 = "llvm.getelementptr"(%254, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %359 = "llvm.getelementptr"(%253, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %360 = "llvm.getelementptr"(%253, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %361 = "llvm.getelementptr"(%253, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %362 = "llvm.getelementptr"(%253, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %363 = "llvm.getelementptr"(%251, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %364 = "llvm.getelementptr"(%251, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %365 = "llvm.getelementptr"(%251, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %366 = "llvm.getelementptr"(%251, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %367 = "llvm.getelementptr"(%250, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %368 = "llvm.getelementptr"(%250, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %369 = "llvm.getelementptr"(%250, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %370 = "llvm.getelementptr"(%250, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %371 = "llvm.getelementptr"(%261, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %372 = "llvm.getelementptr"(%261, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %373 = "llvm.getelementptr"(%261, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %374 = "llvm.getelementptr"(%261, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %375 = "llvm.getelementptr"(%240, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %376 = "llvm.getelementptr"(%240, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %377 = "llvm.getelementptr"(%240, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %378 = "llvm.getelementptr"(%240, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %379 = "llvm.getelementptr"(%238, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %380 = "llvm.getelementptr"(%238, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %381 = "llvm.getelementptr"(%238, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %382 = "llvm.getelementptr"(%238, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %383 = "llvm.getelementptr"(%237, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %384 = "llvm.getelementptr"(%237, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %385 = "llvm.getelementptr"(%237, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %386 = "llvm.getelementptr"(%237, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %387 = "llvm.getelementptr"(%260, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %388 = "llvm.getelementptr"(%260, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %389 = "llvm.getelementptr"(%260, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %390 = "llvm.getelementptr"(%260, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %391 = "llvm.getelementptr"(%245, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %392 = "llvm.getelementptr"(%245, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %393 = "llvm.getelementptr"(%245, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %394 = "llvm.getelementptr"(%245, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %395 = "llvm.getelementptr"(%244, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %396 = "llvm.getelementptr"(%244, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %397 = "llvm.getelementptr"(%244, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %398 = "llvm.getelementptr"(%244, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %399 = "llvm.getelementptr"(%242, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %400 = "llvm.getelementptr"(%242, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %401 = "llvm.getelementptr"(%242, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %402 = "llvm.getelementptr"(%242, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %403 = "llvm.getelementptr"(%241, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %404 = "llvm.getelementptr"(%241, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %405 = "llvm.getelementptr"(%241, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %406 = "llvm.getelementptr"(%241, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %407 = "llvm.getelementptr"(%259, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %408 = "llvm.getelementptr"(%259, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %409 = "llvm.getelementptr"(%259, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %410 = "llvm.getelementptr"(%259, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.br"(%24, %24, %24, %25, %24, %412)[^bb18] : (vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, i64) -> ()
  ^bb16(%411: i64):  // 2 preds: ^bb14, ^bb17
    %412 = "llvm.add"(%411, %19) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    %413 = "llvm.getelementptr"(%266, %412) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %414 = "llvm.load"(%413) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %415 = "llvm.icmp"(%414, %1) <{predicate = 0 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%415)[^bb17, ^bb15] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb17:  // pred: ^bb16
    %416 = "llvm.getelementptr"(%265, %412) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %417 = "llvm.load"(%416) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %418 = "llvm.icmp"(%417, %1) <{predicate = 1 : i64}> : (i8, i8) -> i1
    %419 = "llvm.icmp"(%412, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %420 = "llvm.or"(%418, %419) : (i1, i1) -> i1
    "llvm.cond_br"(%420, %412)[^bb15, ^bb16] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb18(%421: vector<8xi32>, %422: vector<8xi32>, %423: vector<8xi32>, %424: vector<8xi32>, %425: vector<8xi32>, %426: i64):  // 2 preds: ^bb15, ^bb30
    "llvm.intr.lifetime.start"(%263) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%256) : (!llvm.ptr) -> ()
    %427 = "llvm.shufflevector"(%424, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %428 = "llvm.shufflevector"(%423, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %429 = "llvm.shufflevector"(%422, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %430 = "llvm.shufflevector"(%421, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %431 = "llvm.shufflevector"(%425, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%255) : (!llvm.ptr) -> ()
    %432 = "llvm.shufflevector"(%424, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %433 = "llvm.shufflevector"(%423, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %434 = "llvm.shufflevector"(%422, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %435 = "llvm.shufflevector"(%421, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %436 = "llvm.shufflevector"(%425, %26) <{mask = array<i32: -1, -1, -1, -1, -1, 0, -1, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %437 = "llvm.add"(%432, %427) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %438 = "llvm.add"(%433, %428) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %439 = "llvm.add"(%434, %429) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %440 = "llvm.add"(%435, %430) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %441 = "llvm.add"(%436, %431) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %442 = "llvm.shufflevector"(%424, %437) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %443 = "llvm.shufflevector"(%423, %438) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %444 = "llvm.shufflevector"(%422, %439) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %445 = "llvm.shufflevector"(%421, %440) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %446 = "llvm.shufflevector"(%425, %441) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%442, %256) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%443, %327) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%444, %328) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%445, %329) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%446, %330) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.call"(%255, %256) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.sret = !llvm.array<160 x i8>}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D, fastmathFlags = #llvm.fastmath<none>, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope8, #alias_scope9], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!llvm.ptr, !llvm.ptr) -> ()
    %447 = "llvm.load"(%255) <{alias_scopes = [#alias_scope10], alignment = 32 : i64, noalias_scopes = [#alias_scope11, #alias_scope8, #alias_scope9], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %448 = "llvm.load"(%331) <{alias_scopes = [#alias_scope10], alignment = 32 : i64, noalias_scopes = [#alias_scope11, #alias_scope8, #alias_scope9], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %449 = "llvm.load"(%332) <{alias_scopes = [#alias_scope10], alignment = 32 : i64, noalias_scopes = [#alias_scope11, #alias_scope8, #alias_scope9], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %450 = "llvm.load"(%333) <{alias_scopes = [#alias_scope10], alignment = 32 : i64, noalias_scopes = [#alias_scope11, #alias_scope8, #alias_scope9], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %451 = "llvm.shufflevector"(%447, %26) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %452 = "llvm.shufflevector"(%448, %26) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %453 = "llvm.shufflevector"(%449, %26) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %454 = "llvm.shufflevector"(%450, %26) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %455 = "llvm.load"(%334) <{alias_scopes = [#alias_scope10], alignment = 32 : i64, noalias_scopes = [#alias_scope11, #alias_scope8, #alias_scope9], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %456 = "llvm.shufflevector"(%455, %26) <{mask = array<i32: 0, 0, 2, 2, 0, 0, 2, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %457 = "llvm.shufflevector"(%447, %26) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %458 = "llvm.shufflevector"(%448, %26) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %459 = "llvm.shufflevector"(%449, %26) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %460 = "llvm.shufflevector"(%450, %26) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %461 = "llvm.shufflevector"(%455, %26) <{mask = array<i32: 1, 1, 3, 3, 1, 1, 3, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %462 = "llvm.shl"(%447, %27) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %463 = "llvm.shl"(%448, %27) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %464 = "llvm.shl"(%449, %27) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %465 = "llvm.shl"(%450, %27) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %466 = "llvm.shl"(%455, %27) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %467 = "llvm.shufflevector"(%45, %462) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %468 = "llvm.shufflevector"(%45, %463) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %469 = "llvm.shufflevector"(%45, %464) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %470 = "llvm.shufflevector"(%45, %465) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %471 = "llvm.shufflevector"(%45, %466) <{mask = array<i32: 0, 1, 2, 3, 12, -1, 14, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %472 = "llvm.shufflevector"(%467, %447) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %473 = "llvm.shufflevector"(%468, %448) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %474 = "llvm.shufflevector"(%469, %449) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %475 = "llvm.shufflevector"(%470, %450) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %476 = "llvm.shufflevector"(%471, %455) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %477 = "llvm.shufflevector"(%457, %62) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %478 = "llvm.shufflevector"(%458, %62) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %479 = "llvm.shufflevector"(%459, %62) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %480 = "llvm.shufflevector"(%460, %62) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %481 = "llvm.shufflevector"(%461, %62) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %482 = "llvm.sub"(%81, %457) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %483 = "llvm.sub"(%99, %458) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %484 = "llvm.sub"(%99, %459) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %485 = "llvm.sub"(%99, %460) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %486 = "llvm.sub"(%99, %461) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %487 = "llvm.shufflevector"(%116, %482) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %488 = "llvm.shufflevector"(%116, %483) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %489 = "llvm.shufflevector"(%116, %484) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %490 = "llvm.shufflevector"(%116, %485) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %491 = "llvm.shufflevector"(%116, %486) <{mask = array<i32: 0, 9, 2, 11, 12, 5, 14, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %492 = "llvm.add"(%477, %451) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %493 = "llvm.add"(%492, %472) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %494 = "llvm.add"(%493, %487) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %495 = "llvm.add"(%478, %452) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %496 = "llvm.add"(%495, %473) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %497 = "llvm.add"(%496, %488) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %498 = "llvm.add"(%479, %453) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %499 = "llvm.add"(%498, %474) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %500 = "llvm.add"(%499, %489) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %501 = "llvm.add"(%480, %454) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %502 = "llvm.add"(%501, %475) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %503 = "llvm.add"(%502, %490) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %504 = "llvm.add"(%481, %456) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %505 = "llvm.add"(%504, %476) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %506 = "llvm.add"(%505, %491) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %507 = "llvm.shufflevector"(%494, %26) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %508 = "llvm.shufflevector"(%497, %26) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %509 = "llvm.shufflevector"(%500, %26) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %510 = "llvm.shufflevector"(%503, %26) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %511 = "llvm.shufflevector"(%506, %26) <{mask = array<i32: 5, 1, 7, 3, 1, 5, 3, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%507, %255) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%508, %331) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%509, %332) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%510, %333) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%511, %334) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    %512 = "llvm.shufflevector"(%494, %26) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %513 = "llvm.shufflevector"(%497, %26) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %514 = "llvm.shufflevector"(%500, %26) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %515 = "llvm.shufflevector"(%503, %26) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %516 = "llvm.shufflevector"(%506, %26) <{mask = array<i32: 4, 0, 6, 2, 4, 0, 6, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%512, %256) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%513, %327) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%514, %328) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%515, %329) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%516, %330) <{alignment = 32 : i64, noalias_scopes = [#alias_scope8, #alias_scope9], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.call"(%263, %256, %255) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope9], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%255) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%256) : (!llvm.ptr) -> ()
    %517 = "llvm.load"(%263) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %518 = "llvm.load"(%335) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %519 = "llvm.load"(%336) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %520 = "llvm.load"(%337) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %521 = "llvm.load"(%338) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.end"(%263) : (!llvm.ptr) -> ()
    %522 = "llvm.getelementptr"(%266, %426) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %523 = "llvm.load"(%522) <{alias_scopes = [#alias_scope12], alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %524 = "llvm.intr.scmp"(%523, %1) : (i8, i8) -> i8
    "llvm.switch"(%524, %520, %519, %518, %517, %521)[^bb19, ^bb20, ^bb26, ^bb23] <{case_operand_segments = array<i32: 0, 5, 0>, case_values = dense<[-1, 0, 1]> : vector<3xi8>, operandSegmentSizes = array<i32: 1, 0, 5>}> : (i8, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>) -> ()
  ^bb19:  // 2 preds: ^bb18, ^bb26
    "llvm.unreachable"() : () -> ()
  ^bb20:  // pred: ^bb18
    "llvm.intr.lifetime.start"(%261) : (!llvm.ptr) -> ()
    %525 = "llvm.sub"(%1, %523) <{overflowFlags = 0 : i32}> : (i8, i8) -> i8
    %526 = "llvm.sext"(%525) : (i8) -> i64
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope13}> : () -> ()
    "llvm.intr.experimental.noalias.scope.decl"() <{scope = #alias_scope14}> : () -> ()
    %527 = "llvm.lshr"(%526, %10) : (i64, i64) -> i64
    %528 = "llvm.icmp"(%525, %117) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%528)[^bb22, ^bb21] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb21:  // pred: ^bb20
    "llvm.call"(%527, %8, %118) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, noalias_scopes = [#alias_scope13, #alias_scope14], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb22:  // pred: ^bb20
    %529 = "llvm.getelementptr"(%264, %527) <{elem_type = !llvm.struct<"backend::vector::avx2::edwards::CachedPoint", (struct<"backend::vector::avx2::field::FieldElement2625x4", (array<5 x vector<4xi64>>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %530 = "llvm.load"(%529) <{alias_scopes = [#alias_scope13, #alias_scope14], alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %531 = "llvm.getelementptr"(%529, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %532 = "llvm.load"(%531) <{alias_scopes = [#alias_scope13, #alias_scope14], alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %533 = "llvm.getelementptr"(%529, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %534 = "llvm.load"(%533) <{alias_scopes = [#alias_scope13, #alias_scope14], alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %535 = "llvm.getelementptr"(%529, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %536 = "llvm.load"(%535) <{alias_scopes = [#alias_scope13, #alias_scope14], alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %537 = "llvm.getelementptr"(%529, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %538 = "llvm.load"(%537) <{alias_scopes = [#alias_scope13, #alias_scope14], alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%254) : (!llvm.ptr) -> ()
    %539 = "llvm.shufflevector"(%530, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %540 = "llvm.shufflevector"(%532, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %541 = "llvm.shufflevector"(%534, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %542 = "llvm.shufflevector"(%536, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %543 = "llvm.shufflevector"(%538, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %544 = "llvm.sub"(%204, %539) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %545 = "llvm.sub"(%221, %540) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %546 = "llvm.sub"(%221, %541) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %547 = "llvm.sub"(%221, %542) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %548 = "llvm.sub"(%221, %543) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %549 = "llvm.shufflevector"(%539, %544) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %550 = "llvm.shufflevector"(%540, %545) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %551 = "llvm.shufflevector"(%541, %546) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %552 = "llvm.shufflevector"(%542, %547) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %553 = "llvm.shufflevector"(%543, %548) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%549, %254) <{alias_scopes = [#alias_scope15], alignment = 32 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%550, %355) <{alias_scopes = [#alias_scope15], alignment = 32 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%551, %356) <{alias_scopes = [#alias_scope15], alignment = 32 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%552, %357) <{alias_scopes = [#alias_scope15], alignment = 32 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%553, %358) <{alias_scopes = [#alias_scope15], alignment = 32 : i64, noalias_scopes = [#alias_scope16, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%253) : (!llvm.ptr) -> ()
    %554 = "llvm.shufflevector"(%517, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %555 = "llvm.shufflevector"(%518, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %556 = "llvm.shufflevector"(%519, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %557 = "llvm.shufflevector"(%520, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %558 = "llvm.shufflevector"(%521, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %559 = "llvm.sub"(%135, %517) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %560 = "llvm.sub"(%152, %518) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %561 = "llvm.sub"(%152, %519) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %562 = "llvm.sub"(%152, %520) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %563 = "llvm.sub"(%152, %521) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %564 = "llvm.shufflevector"(%559, %517) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %565 = "llvm.shufflevector"(%560, %518) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %566 = "llvm.shufflevector"(%561, %519) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %567 = "llvm.shufflevector"(%562, %520) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %568 = "llvm.shufflevector"(%563, %521) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %569 = "llvm.add"(%564, %554) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %570 = "llvm.add"(%565, %555) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %571 = "llvm.add"(%566, %556) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %572 = "llvm.add"(%567, %557) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %573 = "llvm.add"(%568, %558) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %574 = "llvm.shufflevector"(%569, %517) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %575 = "llvm.shufflevector"(%570, %518) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %576 = "llvm.shufflevector"(%571, %519) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %577 = "llvm.shufflevector"(%572, %520) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %578 = "llvm.shufflevector"(%573, %521) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%574, %253) <{alignment = 32 : i64, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%575, %359) <{alignment = 32 : i64, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%576, %360) <{alignment = 32 : i64, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%577, %361) <{alignment = 32 : i64, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%578, %362) <{alignment = 32 : i64, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%252) : (!llvm.ptr) -> ()
    "llvm.call"(%252, %253, %254) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope17, #alias_scope18, #alias_scope19], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%253, %252, %153) <{arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%252) : (!llvm.ptr) -> ()
    %579 = "llvm.load"(%253) <{alias_scopes = [#alias_scope23], alignment = 32 : i64, noalias_scopes = [#alias_scope24, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %580 = "llvm.load"(%359) <{alias_scopes = [#alias_scope23], alignment = 32 : i64, noalias_scopes = [#alias_scope24, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %581 = "llvm.load"(%360) <{alias_scopes = [#alias_scope23], alignment = 32 : i64, noalias_scopes = [#alias_scope24, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %582 = "llvm.load"(%361) <{alias_scopes = [#alias_scope23], alignment = 32 : i64, noalias_scopes = [#alias_scope24, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %583 = "llvm.shufflevector"(%579, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %584 = "llvm.shufflevector"(%580, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %585 = "llvm.shufflevector"(%581, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %586 = "llvm.shufflevector"(%582, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %587 = "llvm.load"(%362) <{alias_scopes = [#alias_scope23], alignment = 32 : i64, noalias_scopes = [#alias_scope24, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %588 = "llvm.shufflevector"(%587, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %589 = "llvm.shufflevector"(%579, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %590 = "llvm.shufflevector"(%580, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %591 = "llvm.shufflevector"(%581, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %592 = "llvm.shufflevector"(%582, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %593 = "llvm.shufflevector"(%587, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %594 = "llvm.sub"(%170, %583) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %595 = "llvm.sub"(%187, %584) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %596 = "llvm.sub"(%187, %585) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %597 = "llvm.sub"(%187, %586) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %598 = "llvm.sub"(%187, %588) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %599 = "llvm.shufflevector"(%594, %583) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %600 = "llvm.shufflevector"(%595, %584) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %601 = "llvm.shufflevector"(%596, %585) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %602 = "llvm.shufflevector"(%597, %586) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %603 = "llvm.shufflevector"(%598, %588) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %604 = "llvm.add"(%599, %589) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %605 = "llvm.add"(%600, %590) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %606 = "llvm.add"(%601, %591) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %607 = "llvm.add"(%602, %592) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %608 = "llvm.add"(%603, %593) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%251) : (!llvm.ptr) -> ()
    %609 = "llvm.shufflevector"(%604, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %610 = "llvm.shufflevector"(%605, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %611 = "llvm.shufflevector"(%606, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %612 = "llvm.shufflevector"(%607, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %613 = "llvm.shufflevector"(%608, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%609, %251) <{alias_scopes = [#alias_scope25], alignment = 32 : i64, noalias_scopes = [#alias_scope26, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%610, %363) <{alias_scopes = [#alias_scope25], alignment = 32 : i64, noalias_scopes = [#alias_scope26, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%611, %364) <{alias_scopes = [#alias_scope25], alignment = 32 : i64, noalias_scopes = [#alias_scope26, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%612, %365) <{alias_scopes = [#alias_scope25], alignment = 32 : i64, noalias_scopes = [#alias_scope26, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%613, %366) <{alias_scopes = [#alias_scope25], alignment = 32 : i64, noalias_scopes = [#alias_scope26, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%250) : (!llvm.ptr) -> ()
    %614 = "llvm.shufflevector"(%604, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %615 = "llvm.shufflevector"(%605, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %616 = "llvm.shufflevector"(%606, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %617 = "llvm.shufflevector"(%607, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %618 = "llvm.shufflevector"(%608, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%614, %250) <{alias_scopes = [#alias_scope27], alignment = 32 : i64, noalias_scopes = [#alias_scope28, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%615, %367) <{alias_scopes = [#alias_scope27], alignment = 32 : i64, noalias_scopes = [#alias_scope28, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%616, %368) <{alias_scopes = [#alias_scope27], alignment = 32 : i64, noalias_scopes = [#alias_scope28, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%617, %369) <{alias_scopes = [#alias_scope27], alignment = 32 : i64, noalias_scopes = [#alias_scope28, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%618, %370) <{alias_scopes = [#alias_scope27], alignment = 32 : i64, noalias_scopes = [#alias_scope28, #alias_scope20, #alias_scope21, #alias_scope22, #alias_scope17, #alias_scope18, #alias_scope19], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.call"(%261, %251, %250) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope21, #alias_scope22, #alias_scope18, #alias_scope19], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%250) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%251) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%253) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%254) : (!llvm.ptr) -> ()
    %619 = "llvm.load"(%261) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %620 = "llvm.load"(%371) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %621 = "llvm.load"(%372) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %622 = "llvm.load"(%373) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %623 = "llvm.load"(%374) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.end"(%261) : (!llvm.ptr) -> ()
    "llvm.br"(%622, %621, %620, %619, %623)[^bb26] : (vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>) -> ()
  ^bb23:  // pred: ^bb18
    "llvm.intr.lifetime.start"(%262) : (!llvm.ptr) -> ()
    %624 = "llvm.sext"(%523) : (i8) -> i64
    %625 = "llvm.lshr"(%624, %10) : (i64, i64) -> i64
    %626 = "llvm.icmp"(%523, %117) <{predicate = 6 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%626)[^bb25, ^bb24] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb24:  // pred: ^bb23
    "llvm.call"(%625, %8, %118) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, noalias_scopes = [#alias_scope29, #alias_scope30], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb25:  // pred: ^bb23
    %627 = "llvm.getelementptr"(%264, %625) <{elem_type = !llvm.struct<"backend::vector::avx2::edwards::CachedPoint", (struct<"backend::vector::avx2::field::FieldElement2625x4", (array<5 x vector<4xi64>>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%249) : (!llvm.ptr) -> ()
    %628 = "llvm.shufflevector"(%517, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %629 = "llvm.shufflevector"(%518, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %630 = "llvm.shufflevector"(%519, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %631 = "llvm.shufflevector"(%520, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %632 = "llvm.shufflevector"(%521, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %633 = "llvm.sub"(%135, %517) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %634 = "llvm.sub"(%152, %518) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %635 = "llvm.sub"(%152, %519) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %636 = "llvm.sub"(%152, %520) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %637 = "llvm.sub"(%152, %521) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %638 = "llvm.shufflevector"(%633, %517) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %639 = "llvm.shufflevector"(%634, %518) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %640 = "llvm.shufflevector"(%635, %519) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %641 = "llvm.shufflevector"(%636, %520) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %642 = "llvm.shufflevector"(%637, %521) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %643 = "llvm.add"(%638, %628) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %644 = "llvm.add"(%639, %629) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %645 = "llvm.add"(%640, %630) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %646 = "llvm.add"(%641, %631) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %647 = "llvm.add"(%642, %632) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %648 = "llvm.shufflevector"(%643, %517) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %649 = "llvm.shufflevector"(%644, %518) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %650 = "llvm.shufflevector"(%645, %519) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %651 = "llvm.shufflevector"(%646, %520) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %652 = "llvm.shufflevector"(%647, %521) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%648, %249) <{alignment = 32 : i64, noalias_scopes = [#alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%649, %339) <{alignment = 32 : i64, noalias_scopes = [#alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%650, %340) <{alignment = 32 : i64, noalias_scopes = [#alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%651, %341) <{alignment = 32 : i64, noalias_scopes = [#alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%652, %342) <{alignment = 32 : i64, noalias_scopes = [#alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%248) : (!llvm.ptr) -> ()
    "llvm.call"(%248, %249, %627) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%249, %248, %153) <{arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope31, #alias_scope32, #alias_scope33]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%248) : (!llvm.ptr) -> ()
    %653 = "llvm.load"(%249) <{alias_scopes = [#alias_scope34], alignment = 32 : i64, noalias_scopes = [#alias_scope35, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %654 = "llvm.load"(%339) <{alias_scopes = [#alias_scope34], alignment = 32 : i64, noalias_scopes = [#alias_scope35, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %655 = "llvm.load"(%340) <{alias_scopes = [#alias_scope34], alignment = 32 : i64, noalias_scopes = [#alias_scope35, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %656 = "llvm.load"(%341) <{alias_scopes = [#alias_scope34], alignment = 32 : i64, noalias_scopes = [#alias_scope35, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %657 = "llvm.shufflevector"(%653, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %658 = "llvm.shufflevector"(%654, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %659 = "llvm.shufflevector"(%655, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %660 = "llvm.shufflevector"(%656, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %661 = "llvm.load"(%342) <{alias_scopes = [#alias_scope34], alignment = 32 : i64, noalias_scopes = [#alias_scope35, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %662 = "llvm.shufflevector"(%661, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %663 = "llvm.shufflevector"(%653, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %664 = "llvm.shufflevector"(%654, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %665 = "llvm.shufflevector"(%655, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %666 = "llvm.shufflevector"(%656, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %667 = "llvm.shufflevector"(%661, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %668 = "llvm.sub"(%170, %657) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %669 = "llvm.sub"(%187, %658) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %670 = "llvm.sub"(%187, %659) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %671 = "llvm.sub"(%187, %660) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %672 = "llvm.sub"(%187, %662) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %673 = "llvm.shufflevector"(%668, %657) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %674 = "llvm.shufflevector"(%669, %658) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %675 = "llvm.shufflevector"(%670, %659) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %676 = "llvm.shufflevector"(%671, %660) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %677 = "llvm.shufflevector"(%672, %662) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %678 = "llvm.add"(%673, %663) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %679 = "llvm.add"(%674, %664) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %680 = "llvm.add"(%675, %665) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %681 = "llvm.add"(%676, %666) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %682 = "llvm.add"(%677, %667) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%247) : (!llvm.ptr) -> ()
    %683 = "llvm.shufflevector"(%678, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %684 = "llvm.shufflevector"(%679, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %685 = "llvm.shufflevector"(%680, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %686 = "llvm.shufflevector"(%681, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %687 = "llvm.shufflevector"(%682, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%683, %247) <{alias_scopes = [#alias_scope36], alignment = 32 : i64, noalias_scopes = [#alias_scope37, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%684, %343) <{alias_scopes = [#alias_scope36], alignment = 32 : i64, noalias_scopes = [#alias_scope37, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%685, %344) <{alias_scopes = [#alias_scope36], alignment = 32 : i64, noalias_scopes = [#alias_scope37, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%686, %345) <{alias_scopes = [#alias_scope36], alignment = 32 : i64, noalias_scopes = [#alias_scope37, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%687, %346) <{alias_scopes = [#alias_scope36], alignment = 32 : i64, noalias_scopes = [#alias_scope37, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%246) : (!llvm.ptr) -> ()
    %688 = "llvm.shufflevector"(%678, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %689 = "llvm.shufflevector"(%679, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %690 = "llvm.shufflevector"(%680, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %691 = "llvm.shufflevector"(%681, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %692 = "llvm.shufflevector"(%682, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%688, %246) <{alias_scopes = [#alias_scope38], alignment = 32 : i64, noalias_scopes = [#alias_scope39, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%689, %347) <{alias_scopes = [#alias_scope38], alignment = 32 : i64, noalias_scopes = [#alias_scope39, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%690, %348) <{alias_scopes = [#alias_scope38], alignment = 32 : i64, noalias_scopes = [#alias_scope39, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%691, %349) <{alias_scopes = [#alias_scope38], alignment = 32 : i64, noalias_scopes = [#alias_scope39, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%692, %350) <{alias_scopes = [#alias_scope38], alignment = 32 : i64, noalias_scopes = [#alias_scope39, #alias_scope31, #alias_scope32, #alias_scope33], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.call"(%262, %247, %246) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope32, #alias_scope33], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%246) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%247) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%249) : (!llvm.ptr) -> ()
    %693 = "llvm.load"(%262) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %694 = "llvm.load"(%351) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %695 = "llvm.load"(%352) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %696 = "llvm.load"(%353) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %697 = "llvm.load"(%354) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.end"(%262) : (!llvm.ptr) -> ()
    "llvm.br"(%696, %695, %694, %693, %697)[^bb26] : (vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>) -> ()
  ^bb26(%698: vector<8xi32>, %699: vector<8xi32>, %700: vector<8xi32>, %701: vector<8xi32>, %702: vector<8xi32>):  // 3 preds: ^bb18, ^bb22, ^bb25
    %703 = "llvm.getelementptr"(%265, %426) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %704 = "llvm.load"(%703) <{alias_scopes = [#alias_scope40], alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    %705 = "llvm.intr.scmp"(%704, %1) : (i8, i8) -> i8
    "llvm.switch"(%705, %698, %699, %700, %701, %702)[^bb19, ^bb27, ^bb30, ^bb31] <{case_operand_segments = array<i32: 0, 5, 0>, case_values = dense<[-1, 0, 1]> : vector<3xi8>, operandSegmentSizes = array<i32: 1, 0, 5>}> : (i8, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>) -> ()
  ^bb27:  // pred: ^bb26
    "llvm.intr.lifetime.start"(%259) : (!llvm.ptr) -> ()
    %706 = "llvm.sub"(%1, %704) <{overflowFlags = 0 : i32}> : (i8, i8) -> i8
    %707 = "llvm.sext"(%706) : (i8) -> i64
    %708 = "llvm.lshr"(%707, %10) : (i64, i64) -> i64
    %709 = "llvm.icmp"(%706, %222) <{predicate = 4 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%709)[^bb29, ^bb28] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb28:  // pred: ^bb27
    "llvm.call"(%708, %20, %223) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, noalias_scopes = [#alias_scope41], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb29:  // pred: ^bb27
    %710 = "llvm.getelementptr"(%224, %708) <{elem_type = !llvm.struct<"backend::vector::avx2::edwards::CachedPoint", (struct<"backend::vector::avx2::field::FieldElement2625x4", (array<5 x vector<4xi64>>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %711 = "llvm.load"(%710) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %712 = "llvm.getelementptr"(%710, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %713 = "llvm.load"(%712) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %714 = "llvm.getelementptr"(%710, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %715 = "llvm.load"(%714) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %716 = "llvm.getelementptr"(%710, %21) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %717 = "llvm.load"(%716) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %718 = "llvm.getelementptr"(%710, %22) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %719 = "llvm.load"(%718) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%245) : (!llvm.ptr) -> ()
    %720 = "llvm.shufflevector"(%711, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %721 = "llvm.shufflevector"(%713, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %722 = "llvm.shufflevector"(%715, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %723 = "llvm.shufflevector"(%717, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %724 = "llvm.shufflevector"(%719, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %725 = "llvm.sub"(%204, %720) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %726 = "llvm.sub"(%221, %721) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %727 = "llvm.sub"(%221, %722) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %728 = "llvm.sub"(%221, %723) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %729 = "llvm.sub"(%221, %724) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %730 = "llvm.shufflevector"(%720, %725) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %731 = "llvm.shufflevector"(%721, %726) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %732 = "llvm.shufflevector"(%722, %727) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %733 = "llvm.shufflevector"(%723, %728) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %734 = "llvm.shufflevector"(%724, %729) <{mask = array<i32: 0, 1, 2, 3, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%730, %245) <{alias_scopes = [#alias_scope42], alignment = 32 : i64, noalias_scopes = [#alias_scope43, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%731, %391) <{alias_scopes = [#alias_scope42], alignment = 32 : i64, noalias_scopes = [#alias_scope43, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%732, %392) <{alias_scopes = [#alias_scope42], alignment = 32 : i64, noalias_scopes = [#alias_scope43, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%733, %393) <{alias_scopes = [#alias_scope42], alignment = 32 : i64, noalias_scopes = [#alias_scope43, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%734, %394) <{alias_scopes = [#alias_scope42], alignment = 32 : i64, noalias_scopes = [#alias_scope43, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%244) : (!llvm.ptr) -> ()
    %735 = "llvm.shufflevector"(%701, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %736 = "llvm.shufflevector"(%700, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %737 = "llvm.shufflevector"(%699, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %738 = "llvm.shufflevector"(%698, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %739 = "llvm.shufflevector"(%702, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %740 = "llvm.sub"(%135, %701) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %741 = "llvm.sub"(%152, %700) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %742 = "llvm.sub"(%152, %699) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %743 = "llvm.sub"(%152, %698) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %744 = "llvm.sub"(%152, %702) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %745 = "llvm.shufflevector"(%740, %701) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %746 = "llvm.shufflevector"(%741, %700) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %747 = "llvm.shufflevector"(%742, %699) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %748 = "llvm.shufflevector"(%743, %698) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %749 = "llvm.shufflevector"(%744, %702) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %750 = "llvm.add"(%745, %735) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %751 = "llvm.add"(%746, %736) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %752 = "llvm.add"(%747, %737) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %753 = "llvm.add"(%748, %738) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %754 = "llvm.add"(%749, %739) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %755 = "llvm.shufflevector"(%750, %701) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %756 = "llvm.shufflevector"(%751, %700) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %757 = "llvm.shufflevector"(%752, %699) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %758 = "llvm.shufflevector"(%753, %698) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %759 = "llvm.shufflevector"(%754, %702) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%755, %244) <{alignment = 32 : i64, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%756, %395) <{alignment = 32 : i64, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%757, %396) <{alignment = 32 : i64, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%758, %397) <{alignment = 32 : i64, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%759, %398) <{alignment = 32 : i64, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%243) : (!llvm.ptr) -> ()
    "llvm.call"(%243, %244, %245) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope44, #alias_scope45, #alias_scope46], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%244, %243, %153) <{arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%243) : (!llvm.ptr) -> ()
    %760 = "llvm.load"(%244) <{alias_scopes = [#alias_scope50], alignment = 32 : i64, noalias_scopes = [#alias_scope51, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %761 = "llvm.load"(%395) <{alias_scopes = [#alias_scope50], alignment = 32 : i64, noalias_scopes = [#alias_scope51, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %762 = "llvm.load"(%396) <{alias_scopes = [#alias_scope50], alignment = 32 : i64, noalias_scopes = [#alias_scope51, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %763 = "llvm.load"(%397) <{alias_scopes = [#alias_scope50], alignment = 32 : i64, noalias_scopes = [#alias_scope51, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %764 = "llvm.shufflevector"(%760, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %765 = "llvm.shufflevector"(%761, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %766 = "llvm.shufflevector"(%762, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %767 = "llvm.shufflevector"(%763, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %768 = "llvm.load"(%398) <{alias_scopes = [#alias_scope50], alignment = 32 : i64, noalias_scopes = [#alias_scope51, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %769 = "llvm.shufflevector"(%768, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %770 = "llvm.shufflevector"(%760, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %771 = "llvm.shufflevector"(%761, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %772 = "llvm.shufflevector"(%762, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %773 = "llvm.shufflevector"(%763, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %774 = "llvm.shufflevector"(%768, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %775 = "llvm.sub"(%170, %764) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %776 = "llvm.sub"(%187, %765) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %777 = "llvm.sub"(%187, %766) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %778 = "llvm.sub"(%187, %767) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %779 = "llvm.sub"(%187, %769) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %780 = "llvm.shufflevector"(%775, %764) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %781 = "llvm.shufflevector"(%776, %765) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %782 = "llvm.shufflevector"(%777, %766) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %783 = "llvm.shufflevector"(%778, %767) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %784 = "llvm.shufflevector"(%779, %769) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %785 = "llvm.add"(%780, %770) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %786 = "llvm.add"(%781, %771) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %787 = "llvm.add"(%782, %772) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %788 = "llvm.add"(%783, %773) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %789 = "llvm.add"(%784, %774) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%242) : (!llvm.ptr) -> ()
    %790 = "llvm.shufflevector"(%785, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %791 = "llvm.shufflevector"(%786, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %792 = "llvm.shufflevector"(%787, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %793 = "llvm.shufflevector"(%788, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %794 = "llvm.shufflevector"(%789, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%790, %242) <{alias_scopes = [#alias_scope52], alignment = 32 : i64, noalias_scopes = [#alias_scope53, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%791, %399) <{alias_scopes = [#alias_scope52], alignment = 32 : i64, noalias_scopes = [#alias_scope53, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%792, %400) <{alias_scopes = [#alias_scope52], alignment = 32 : i64, noalias_scopes = [#alias_scope53, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%793, %401) <{alias_scopes = [#alias_scope52], alignment = 32 : i64, noalias_scopes = [#alias_scope53, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%794, %402) <{alias_scopes = [#alias_scope52], alignment = 32 : i64, noalias_scopes = [#alias_scope53, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%241) : (!llvm.ptr) -> ()
    %795 = "llvm.shufflevector"(%785, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %796 = "llvm.shufflevector"(%786, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %797 = "llvm.shufflevector"(%787, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %798 = "llvm.shufflevector"(%788, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %799 = "llvm.shufflevector"(%789, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%795, %241) <{alias_scopes = [#alias_scope54], alignment = 32 : i64, noalias_scopes = [#alias_scope55, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%796, %403) <{alias_scopes = [#alias_scope54], alignment = 32 : i64, noalias_scopes = [#alias_scope55, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%797, %404) <{alias_scopes = [#alias_scope54], alignment = 32 : i64, noalias_scopes = [#alias_scope55, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%798, %405) <{alias_scopes = [#alias_scope54], alignment = 32 : i64, noalias_scopes = [#alias_scope55, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%799, %406) <{alias_scopes = [#alias_scope54], alignment = 32 : i64, noalias_scopes = [#alias_scope55, #alias_scope47, #alias_scope48, #alias_scope49, #alias_scope44, #alias_scope45, #alias_scope46], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.call"(%259, %242, %241) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope48, #alias_scope49, #alias_scope45, #alias_scope46], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%241) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%242) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%244) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%245) : (!llvm.ptr) -> ()
    %800 = "llvm.load"(%259) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %801 = "llvm.load"(%407) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %802 = "llvm.load"(%408) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %803 = "llvm.load"(%409) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %804 = "llvm.load"(%410) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.end"(%259) : (!llvm.ptr) -> ()
    "llvm.br"(%803, %802, %801, %800, %804)[^bb30] : (vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>) -> ()
  ^bb30(%805: vector<8xi32>, %806: vector<8xi32>, %807: vector<8xi32>, %808: vector<8xi32>, %809: vector<8xi32>):  // 3 preds: ^bb26, ^bb29, ^bb33
    %810 = "llvm.icmp"(%426, %4) <{predicate = 0 : i64}> : (i64, i64) -> i1
    %811 = "llvm.add"(%426, %19) <{overflowFlags = 1 : i32}> : (i64, i64) -> i64
    "llvm.cond_br"(%810, %805, %806, %807, %808, %809, %811)[^bb34, ^bb18] <{operandSegmentSizes = array<i32: 1, 0, 6>}> : (i1, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, i64) -> ()
  ^bb31:  // pred: ^bb26
    "llvm.intr.lifetime.start"(%260) : (!llvm.ptr) -> ()
    %812 = "llvm.sext"(%704) : (i8) -> i64
    %813 = "llvm.lshr"(%812, %10) : (i64, i64) -> i64
    %814 = "llvm.icmp"(%704, %222) <{predicate = 4 : i64}> : (i8, i8) -> i1
    "llvm.cond_br"(%814)[^bb33, ^bb32] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb32:  // pred: ^bb31
    "llvm.call"(%813, %20, %223) <{CConv = #llvm.cconv<ccc>, TailCallKind = #llvm.tailcallkind<tail>, arg_attrs = [{llvm.noundef}, {llvm.noundef}, {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.noalias, llvm.nofree, llvm.noundef, llvm.readonly}], callee = @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check, fastmathFlags = #llvm.fastmath<none>, no_inline, no_unwind, noalias_scopes = [#alias_scope56], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (i64, i64, !llvm.ptr) -> ()
    "llvm.unreachable"() : () -> ()
  ^bb33:  // pred: ^bb31
    %815 = "llvm.getelementptr"(%224, %813) <{elem_type = !llvm.struct<"backend::vector::avx2::edwards::CachedPoint", (struct<"backend::vector::avx2::field::FieldElement2625x4", (array<5 x vector<4xi64>>)>)>, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.lifetime.start"(%240) : (!llvm.ptr) -> ()
    %816 = "llvm.shufflevector"(%701, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %817 = "llvm.shufflevector"(%700, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %818 = "llvm.shufflevector"(%699, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %819 = "llvm.shufflevector"(%698, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %820 = "llvm.shufflevector"(%702, %26) <{mask = array<i32: 1, 0, 3, 2, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %821 = "llvm.sub"(%135, %701) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %822 = "llvm.sub"(%152, %700) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %823 = "llvm.sub"(%152, %699) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %824 = "llvm.sub"(%152, %698) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %825 = "llvm.sub"(%152, %702) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %826 = "llvm.shufflevector"(%821, %701) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %827 = "llvm.shufflevector"(%822, %700) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %828 = "llvm.shufflevector"(%823, %699) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %829 = "llvm.shufflevector"(%824, %698) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %830 = "llvm.shufflevector"(%825, %702) <{mask = array<i32: 0, 9, 2, 11, -1, -1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %831 = "llvm.add"(%826, %816) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %832 = "llvm.add"(%827, %817) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %833 = "llvm.add"(%828, %818) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %834 = "llvm.add"(%829, %819) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %835 = "llvm.add"(%830, %820) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %836 = "llvm.shufflevector"(%831, %701) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %837 = "llvm.shufflevector"(%832, %700) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %838 = "llvm.shufflevector"(%833, %699) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %839 = "llvm.shufflevector"(%834, %698) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %840 = "llvm.shufflevector"(%835, %702) <{mask = array<i32: 0, 1, 2, 3, 12, 13, 14, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%836, %240) <{alignment = 32 : i64, noalias_scopes = [#alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%837, %375) <{alignment = 32 : i64, noalias_scopes = [#alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%838, %376) <{alignment = 32 : i64, noalias_scopes = [#alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%839, %377) <{alignment = 32 : i64, noalias_scopes = [#alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%840, %378) <{alignment = 32 : i64, noalias_scopes = [#alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%239) : (!llvm.ptr) -> ()
    "llvm.call"(%239, %240, %815) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.memcpy"(%240, %239, %153) <{arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.nonnull, llvm.noundef}, {}], isVolatile = false, noalias_scopes = [#alias_scope57, #alias_scope58, #alias_scope59]}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.lifetime.end"(%239) : (!llvm.ptr) -> ()
    %841 = "llvm.load"(%240) <{alias_scopes = [#alias_scope60], alignment = 32 : i64, noalias_scopes = [#alias_scope61, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %842 = "llvm.load"(%375) <{alias_scopes = [#alias_scope60], alignment = 32 : i64, noalias_scopes = [#alias_scope61, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %843 = "llvm.load"(%376) <{alias_scopes = [#alias_scope60], alignment = 32 : i64, noalias_scopes = [#alias_scope61, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %844 = "llvm.load"(%377) <{alias_scopes = [#alias_scope60], alignment = 32 : i64, noalias_scopes = [#alias_scope61, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %845 = "llvm.shufflevector"(%841, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %846 = "llvm.shufflevector"(%842, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %847 = "llvm.shufflevector"(%843, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %848 = "llvm.shufflevector"(%844, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %849 = "llvm.load"(%378) <{alias_scopes = [#alias_scope60], alignment = 32 : i64, noalias_scopes = [#alias_scope61, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %850 = "llvm.shufflevector"(%849, %26) <{mask = array<i32: 0, 1, 2, 3, 5, 4, 7, 6>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %851 = "llvm.shufflevector"(%841, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %852 = "llvm.shufflevector"(%842, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %853 = "llvm.shufflevector"(%843, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %854 = "llvm.shufflevector"(%844, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %855 = "llvm.shufflevector"(%849, %26) <{mask = array<i32: 1, 0, 3, 2, 4, 5, 6, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %856 = "llvm.sub"(%170, %845) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %857 = "llvm.sub"(%187, %846) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %858 = "llvm.sub"(%187, %847) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %859 = "llvm.sub"(%187, %848) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %860 = "llvm.sub"(%187, %850) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %861 = "llvm.shufflevector"(%856, %845) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %862 = "llvm.shufflevector"(%857, %846) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %863 = "llvm.shufflevector"(%858, %847) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %864 = "llvm.shufflevector"(%859, %848) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %865 = "llvm.shufflevector"(%860, %850) <{mask = array<i32: 0, 9, 2, 11, 4, 13, 6, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %866 = "llvm.add"(%861, %851) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %867 = "llvm.add"(%862, %852) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %868 = "llvm.add"(%863, %853) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %869 = "llvm.add"(%864, %854) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %870 = "llvm.add"(%865, %855) <{overflowFlags = 0 : i32}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.intr.lifetime.start"(%238) : (!llvm.ptr) -> ()
    %871 = "llvm.shufflevector"(%866, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %872 = "llvm.shufflevector"(%867, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %873 = "llvm.shufflevector"(%868, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %874 = "llvm.shufflevector"(%869, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %875 = "llvm.shufflevector"(%870, %26) <{mask = array<i32: 0, 5, 2, 7, 5, 0, 7, 2>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%871, %238) <{alias_scopes = [#alias_scope62], alignment = 32 : i64, noalias_scopes = [#alias_scope63, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%872, %379) <{alias_scopes = [#alias_scope62], alignment = 32 : i64, noalias_scopes = [#alias_scope63, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%873, %380) <{alias_scopes = [#alias_scope62], alignment = 32 : i64, noalias_scopes = [#alias_scope63, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%874, %381) <{alias_scopes = [#alias_scope62], alignment = 32 : i64, noalias_scopes = [#alias_scope63, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%875, %382) <{alias_scopes = [#alias_scope62], alignment = 32 : i64, noalias_scopes = [#alias_scope63, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.intr.lifetime.start"(%237) : (!llvm.ptr) -> ()
    %876 = "llvm.shufflevector"(%866, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %877 = "llvm.shufflevector"(%867, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %878 = "llvm.shufflevector"(%868, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %879 = "llvm.shufflevector"(%869, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    %880 = "llvm.shufflevector"(%870, %26) <{mask = array<i32: 4, 1, 6, 3, 4, 1, 6, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<8xi32>
    "llvm.store"(%876, %237) <{alias_scopes = [#alias_scope64], alignment = 32 : i64, noalias_scopes = [#alias_scope65, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%877, %383) <{alias_scopes = [#alias_scope64], alignment = 32 : i64, noalias_scopes = [#alias_scope65, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%878, %384) <{alias_scopes = [#alias_scope64], alignment = 32 : i64, noalias_scopes = [#alias_scope65, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%879, %385) <{alias_scopes = [#alias_scope64], alignment = 32 : i64, noalias_scopes = [#alias_scope65, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.store"(%880, %386) <{alias_scopes = [#alias_scope64], alignment = 32 : i64, noalias_scopes = [#alias_scope65, #alias_scope57, #alias_scope58, #alias_scope59], ordering = 0 : i64}> : (vector<8xi32>, !llvm.ptr) -> ()
    "llvm.call"(%260, %238, %237) <{CConv = #llvm.cconv<fastcc>, TailCallKind = #llvm.tailcallkind<none>, arg_attrs = [{llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}, {llvm.align = 32 : i64, llvm.dereferenceable = 160 : i64, llvm.noalias, llvm.nofree, llvm.nonnull, llvm.noundef, llvm.readonly}], callee = @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul, fastmathFlags = #llvm.fastmath<none>, inline_hint, memory_effects = #llvm.memory_effects<other = none, argMem = readwrite, inaccessibleMem = none, errnoMem = none, targetMem0 = none, targetMem1 = none>, no_unwind, noalias_scopes = [#alias_scope58, #alias_scope59], op_bundle_sizes = array<i32>, operandSegmentSizes = array<i32: 3, 0>}> : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%237) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%238) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%240) : (!llvm.ptr) -> ()
    %881 = "llvm.load"(%260) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %882 = "llvm.load"(%387) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %883 = "llvm.load"(%388) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %884 = "llvm.load"(%389) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    %885 = "llvm.load"(%390) <{alignment = 32 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> vector<8xi32>
    "llvm.intr.lifetime.end"(%260) : (!llvm.ptr) -> ()
    "llvm.br"(%884, %883, %882, %881, %885)[^bb30] : (vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>, vector<8xi32>) -> ()
  ^bb34:  // pred: ^bb30
    %886 = "llvm.extractelement"(%808, %13) : (vector<8xi32>, i64) -> i32
    %887 = "llvm.extractelement"(%808, %225) : (vector<8xi32>, i64) -> i32
    %888 = "llvm.extractelement"(%807, %226) : (vector<8xi32>, i64) -> i32
    %889 = "llvm.extractelement"(%807, %13) : (vector<8xi32>, i64) -> i32
    %890 = "llvm.extractelement"(%806, %226) : (vector<8xi32>, i64) -> i32
    %891 = "llvm.extractelement"(%806, %5) : (vector<8xi32>, i64) -> i32
    %892 = "llvm.extractelement"(%805, %10) : (vector<8xi32>, i64) -> i32
    %893 = "llvm.zext"(%892) : (i32) -> i64
    %894 = "llvm.extractelement"(%805, %227) : (vector<8xi32>, i64) -> i32
    %895 = "llvm.zext"(%894) : (i32) -> i64
    %896 = "llvm.shl"(%895, %228) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %897 = "llvm.add"(%896, %893) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %898 = "llvm.extractelement"(%809, %13) : (vector<8xi32>, i64) -> i32
    %899 = "llvm.zext"(%898) : (i32) -> i64
    %900 = "llvm.extractelement"(%809, %225) : (vector<8xi32>, i64) -> i32
    %901 = "llvm.zext"(%900) : (i32) -> i64
    %902 = "llvm.shl"(%901, %228) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %903 = "llvm.add"(%902, %899) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    %904 = "llvm.shufflevector"(%808, %807) <{mask = array<i32: 0, 8>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %905 = "llvm.zext"(%904) : (vector<2xi32>) -> vector<2xi64>
    %906 = "llvm.shufflevector"(%808, %807) <{mask = array<i32: 2, 10>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %907 = "llvm.zext"(%906) : (vector<2xi32>) -> vector<2xi64>
    %908 = "llvm.shl"(%907, %229) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %909 = "llvm.add"(%908, %905) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%909, %arg0) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %910 = "llvm.getelementptr"(%arg0, %230) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %911 = "llvm.shufflevector"(%806, %805) <{mask = array<i32: 0, 8>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %912 = "llvm.zext"(%911) : (vector<2xi32>) -> vector<2xi64>
    %913 = "llvm.shufflevector"(%806, %805) <{mask = array<i32: 2, 10>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %914 = "llvm.zext"(%913) : (vector<2xi32>) -> vector<2xi64>
    %915 = "llvm.shl"(%914, %229) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %916 = "llvm.add"(%915, %912) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%916, %910) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %917 = "llvm.getelementptr"(%arg0, %3) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %918 = "llvm.shufflevector"(%809, %808) <{mask = array<i32: 0, 9, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %919 = "llvm.shufflevector"(%807, %26) <{mask = array<i32: -1, 1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %920 = "llvm.shufflevector"(%918, %919) <{mask = array<i32: 0, 1, 5, -1>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %921 = "llvm.shufflevector"(%806, %26) <{mask = array<i32: -1, 1, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %922 = "llvm.shufflevector"(%920, %921) <{mask = array<i32: 0, 1, 2, 5>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %923 = "llvm.zext"(%922) : (vector<4xi32>) -> vector<4xi64>
    %924 = "llvm.shufflevector"(%809, %808) <{mask = array<i32: 2, 11, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %925 = "llvm.shufflevector"(%807, %26) <{mask = array<i32: -1, -1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %926 = "llvm.shufflevector"(%924, %925) <{mask = array<i32: 0, 1, 7, -1>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %927 = "llvm.shufflevector"(%806, %26) <{mask = array<i32: -1, -1, -1, 3>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %928 = "llvm.shufflevector"(%926, %927) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %929 = "llvm.zext"(%928) : (vector<4xi32>) -> vector<4xi64>
    %930 = "llvm.shl"(%929, %231) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %931 = "llvm.add"(%930, %923) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    "llvm.store"(%931, %917) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (vector<4xi64>, !llvm.ptr) -> ()
    %932 = "llvm.getelementptr"(%arg0, %20) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%897, %932) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    %933 = "llvm.getelementptr"(%arg0, %232) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %934 = "llvm.shufflevector"(%809, %808) <{mask = array<i32: 1, 12, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %935 = "llvm.insertelement"(%934, %888, %233) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %936 = "llvm.insertelement"(%935, %890, %227) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %937 = "llvm.zext"(%936) : (vector<4xi32>) -> vector<4xi64>
    %938 = "llvm.shufflevector"(%809, %808) <{mask = array<i32: 3, 14, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %939 = "llvm.shufflevector"(%807, %26) <{mask = array<i32: -1, -1, 6, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %940 = "llvm.shufflevector"(%938, %939) <{mask = array<i32: 0, 1, 6, -1>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %941 = "llvm.insertelement"(%940, %891, %227) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %942 = "llvm.zext"(%941) : (vector<4xi32>) -> vector<4xi64>
    %943 = "llvm.shl"(%942, %231) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %944 = "llvm.add"(%943, %937) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    "llvm.store"(%944, %933) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (vector<4xi64>, !llvm.ptr) -> ()
    %945 = "llvm.getelementptr"(%arg0, %234) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %946 = "llvm.shufflevector"(%805, %809) <{mask = array<i32: 4, 12, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %947 = "llvm.insertelement"(%946, %886, %233) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %948 = "llvm.insertelement"(%947, %889, %227) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %949 = "llvm.zext"(%948) : (vector<4xi32>) -> vector<4xi64>
    %950 = "llvm.shufflevector"(%805, %809) <{mask = array<i32: 6, 14, -1, -1>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %951 = "llvm.insertelement"(%950, %887, %233) : (vector<4xi32>, i32, i64) -> vector<4xi32>
    %952 = "llvm.shufflevector"(%807, %26) <{mask = array<i32: -1, -1, -1, 7>}> : (vector<8xi32>, vector<8xi32>) -> vector<4xi32>
    %953 = "llvm.shufflevector"(%951, %952) <{mask = array<i32: 0, 1, 2, 7>}> : (vector<4xi32>, vector<4xi32>) -> vector<4xi32>
    %954 = "llvm.zext"(%953) : (vector<4xi32>) -> vector<4xi64>
    %955 = "llvm.shl"(%954, %231) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    %956 = "llvm.add"(%955, %949) <{overflowFlags = 3 : i32}> : (vector<4xi64>, vector<4xi64>) -> vector<4xi64>
    "llvm.store"(%956, %945) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (vector<4xi64>, !llvm.ptr) -> ()
    %957 = "llvm.getelementptr"(%arg0, %235) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %958 = "llvm.shufflevector"(%806, %805) <{mask = array<i32: 5, 13>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %959 = "llvm.zext"(%958) : (vector<2xi32>) -> vector<2xi64>
    %960 = "llvm.shufflevector"(%806, %805) <{mask = array<i32: 7, 15>}> : (vector<8xi32>, vector<8xi32>) -> vector<2xi32>
    %961 = "llvm.zext"(%960) : (vector<2xi32>) -> vector<2xi64>
    %962 = "llvm.shl"(%961, %229) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    %963 = "llvm.add"(%962, %959) <{overflowFlags = 3 : i32}> : (vector<2xi64>, vector<2xi64>) -> vector<2xi64>
    "llvm.store"(%963, %957) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (vector<2xi64>, !llvm.ptr) -> ()
    %964 = "llvm.getelementptr"(%arg0, %236) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%903, %964) <{alias_scopes = [#alias_scope66, #alias_scope67, #alias_scope68], alignment = 8 : i64, noalias_scopes = [#alias_scope69], ordering = 0 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%264) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%265) : (!llvm.ptr) -> ()
    "llvm.intr.lifetime.end"(%266) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

def program (p : Primitives) (g : Globals) : Except String Func :=
  translate region p.resolve g.resolve

end

end Agave.Ed25519.DoubleBase.Avx2CFG
