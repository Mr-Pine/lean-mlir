; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_field_from_bytes_observe_4.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable
define noundef range(i64 0, 2251799813685248) i64 @agave_serial_field_from_bytes_observe_4(i64 noundef %w0, i64 noundef %w1, i64 noundef %w2, i64 noundef %w3) unnamed_addr #0 {
start:
  %_16.i = lshr i64 %w3, 12
  %_15.i = and i64 %_16.i, 2251799813685247
  ret i64 %_15.i
}

attributes #0 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
