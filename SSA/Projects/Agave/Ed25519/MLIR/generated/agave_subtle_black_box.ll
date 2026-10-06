; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_subtle_black_box.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable
define noundef i8 @_RINvCsh8VEmffyqhs_6subtle9black_boxhECsjK63O35OHGN_14solana_ed25519(i8 noundef %0) unnamed_addr #0 {
start:
  %input.sroa.0 = alloca i8, align 1
  store i8 %0, ptr %input.sroa.0, align 1
  %input.sroa.0.0.input.sroa.0.0.input.sroa.0.0.input.sroa.0.0.input.sroa.0.0._0 = load volatile i8, ptr %input.sroa.0, align 1
  ret i8 %input.sroa.0.0.input.sroa.0.0.input.sroa.0.0.input.sroa.0.0.input.sroa.0.0._0
}

attributes #0 = { mustprogress nofree noinline norecurse nounwind nonlazybind willreturn memory(inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
