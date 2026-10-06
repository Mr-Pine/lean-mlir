; ModuleID = '/home/nine/Documents/anza-code/.lmf-rir-ed25519/SSA/Projects/Agave/Ed25519/MLIR/generated/agave_scalar_from_sha512.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nofree norecurse nounwind nonlazybind uwtable
declare void @_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)), ptr noalias nofree noundef readonly captures(none) dereferenceable(64)) unnamed_addr #0

; Function Attrs: nounwind nonlazybind uwtable
define void @_RNvNtCsjK63O35OHGN_14solana_ed255197ed_sigs18scalar_from_sha512(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([32 x i8]) align 1 captures(none) dereferenceable(32) initializes((0, 32)) %scalar, ptr dead_on_return noalias nofree noundef readonly align 16 captures(none) dereferenceable(208) %hash) unnamed_addr #1 personality ptr @rust_eh_personality {
start:
  %_5.i9.i.i = alloca [128 x i8], align 1
  %_5.i7.i.i = alloca [128 x i8], align 1
  %_5.i.i.i = alloca [128 x i8], align 1
  %res.i.i.i = alloca [128 x i8], align 1
  %bytes = alloca [64 x i8], align 8
  %_3 = alloca [208 x i8], align 16
  %output.sroa.0 = alloca i8, align 1
  %output.sroa.5 = alloca i8, align 1
  %output.sroa.6 = alloca i8, align 1
  %output.sroa.7 = alloca i8, align 1
  %output.sroa.8 = alloca i8, align 1
  %output.sroa.9 = alloca i8, align 1
  %output.sroa.10 = alloca i8, align 1
  %output.sroa.11 = alloca i8, align 1
  %output.sroa.12 = alloca i8, align 1
  %output.sroa.13 = alloca i8, align 1
  %output.sroa.14 = alloca i8, align 1
  %output.sroa.15 = alloca i8, align 1
  %output.sroa.16 = alloca i8, align 1
  %output.sroa.17 = alloca i8, align 1
  %output.sroa.18 = alloca i8, align 1
  %output.sroa.19 = alloca i8, align 1
  %output.sroa.20 = alloca i8, align 1
  %output.sroa.21 = alloca i8, align 1
  %output.sroa.22 = alloca i8, align 1
  %output.sroa.23 = alloca i8, align 1
  %output.sroa.24 = alloca i8, align 1
  %output.sroa.25 = alloca i8, align 1
  %output.sroa.26 = alloca i8, align 1
  %output.sroa.27 = alloca i8, align 1
  %output.sroa.28 = alloca i8, align 1
  %output.sroa.29 = alloca i8, align 1
  %output.sroa.30 = alloca i8, align 1
  %output.sroa.31 = alloca i8, align 1
  %output.sroa.32 = alloca i8, align 1
  %output.sroa.33 = alloca i8, align 1
  %output.sroa.34 = alloca i8, align 1
  %output.sroa.35 = alloca i8, align 1
  %output.sroa.36 = alloca i8, align 1
  %output.sroa.37 = alloca i8, align 1
  %output.sroa.38 = alloca i8, align 1
  %output.sroa.39 = alloca i8, align 1
  %output.sroa.40 = alloca i8, align 1
  %output.sroa.41 = alloca i8, align 1
  %output.sroa.42 = alloca i8, align 1
  %output.sroa.43 = alloca i8, align 1
  %output.sroa.44 = alloca i8, align 1
  %output.sroa.45 = alloca i8, align 1
  %output.sroa.46 = alloca i8, align 1
  %output.sroa.47 = alloca i8, align 1
  %output.sroa.48 = alloca i8, align 1
  %output.sroa.49 = alloca i8, align 1
  %output.sroa.50 = alloca i8, align 1
  %output.sroa.51 = alloca i8, align 1
  %output.sroa.52 = alloca i8, align 1
  %output.sroa.53 = alloca i8, align 1
  %output.sroa.54 = alloca i8, align 1
  %output.sroa.55 = alloca i8, align 1
  %output.sroa.56 = alloca i8, align 1
  %output.sroa.57 = alloca i8, align 1
  %output.sroa.58 = alloca i8, align 1
  %output.sroa.59 = alloca i8, align 1
  %output.sroa.60 = alloca i8, align 1
  %output.sroa.61 = alloca i8, align 1
  %output.sroa.62 = alloca i8, align 1
  %output.sroa.63 = alloca i8, align 1
  %output.sroa.64 = alloca i8, align 1
  %output.sroa.65 = alloca i8, align 1
  %output.sroa.66 = alloca i8, align 1
  %output.sroa.67 = alloca i8, align 1
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.0)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.5)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.6)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.7)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.8)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.9)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.10)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.11)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.12)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.13)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.14)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.15)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.16)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.17)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.18)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.19)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.20)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.21)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.22)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.23)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.24)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.25)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.26)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.27)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.28)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.29)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.30)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.31)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.32)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.33)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.34)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.35)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.36)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.37)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.38)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.39)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.40)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.41)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.42)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.43)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.44)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.45)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.46)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.47)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.48)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.49)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.50)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.51)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.52)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.53)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.54)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.55)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.56)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.57)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.58)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.59)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.60)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.61)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.62)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.63)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.64)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.65)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.66)
  call void @llvm.lifetime.start.p0(ptr nonnull %output.sroa.67)
  call void @llvm.lifetime.start.p0(ptr nonnull %_3)
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 16 dereferenceable(208) %_3, ptr noundef nonnull align 16 dereferenceable(208) %hash, i64 208, i1 false)
  %_21 = getelementptr inbounds nuw i8, ptr %_3, i64 128
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !7)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !9)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !12)
  call void @llvm.lifetime.start.p0(ptr nonnull %res.i.i.i), !noalias !14
  %_32.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 127
  %_30.i.i = load i8, ptr %_32.i.i, align 1, !alias.scope !16, !noalias !17, !noundef !19
  %_29.i.i = icmp sgt i8 %_30.i.i, -1
  tail call void @llvm.assume(i1 %_29.i.i)
  %_6.i.i = zext nneg i8 %_30.i.i to i128
  %0 = getelementptr inbounds nuw i8, ptr %_3, i64 192
  %_9.i.i = load i128, ptr %0, align 16, !alias.scope !20, !noalias !21, !noundef !19
  %1 = shl i128 %_9.i.i, 10
  %2 = shl nuw nsw i128 %_6.i.i, 3
  %bit_len.i.i = or disjoint i128 %1, %2
  %_38.i.i = tail call i128 @llvm.bswap.i128(i128 %bit_len.i.i)
  %pos.i.i.i = zext nneg i8 %_30.i.i to i64
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(128) %res.i.i.i, i8 0, i64 128, i1 false), !noalias !22
  call void @llvm.memcpy.p0.p0.i64(ptr nonnull align 1 %res.i.i.i, ptr nonnull readonly align 16 dereferenceable(128) %_3, i64 range(i64 0, -9223372036854775808) %pos.i.i.i, i1 false), !noalias !17
  %_11.i.i.i = getelementptr inbounds nuw i8, ptr %res.i.i.i, i64 %pos.i.i.i
  store i8 -128, ptr %_11.i.i.i, align 1, !noalias !22
  %_14.i.i.i = xor i64 %pos.i.i.i, 112
  %_13.i.i.i = icmp samesign ult i64 %_14.i.i.i, 16
  br i1 %_13.i.i.i, label %bb4.i.i.i, label %bb18.i.i.i

bb4.i.i.i:                                        ; preds = %start
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i.i.i), !noalias !23
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 1 dereferenceable(128) %_5.i.i.i, ptr noundef nonnull readonly align 1 dereferenceable(128) %res.i.i.i, i64 128, i1 false), !noalias !22
  call void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef nonnull align 16 dereferenceable(80) %_21, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_5.i.i.i, i64 noundef 1) #9, !noalias !26
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i.i.i), !noalias !23
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(128) %res.i.i.i, i8 0, i64 112, i1 false), !noalias !22
  %_65.i.i.i = getelementptr inbounds nuw i8, ptr %res.i.i.i, i64 112
  store i128 %_38.i.i, ptr %_65.i.i.i, align 1, !noalias !22
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i7.i.i), !noalias !27
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 1 dereferenceable(128) %_5.i7.i.i, ptr noundef nonnull readonly align 1 dereferenceable(128) %res.i.i.i, i64 128, i1 false), !noalias !22
  call void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef nonnull align 16 dereferenceable(80) %_21, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_5.i7.i.i, i64 noundef 1) #9, !noalias !30
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i7.i.i), !noalias !27
  br label %_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519.exit

bb18.i.i.i:                                       ; preds = %start
  %_75.i.i.i = getelementptr inbounds nuw i8, ptr %res.i.i.i, i64 112
  store i128 %_38.i.i, ptr %_75.i.i.i, align 1, !noalias !22
  call void @llvm.lifetime.start.p0(ptr nonnull %_5.i9.i.i), !noalias !31
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 1 dereferenceable(128) %_5.i9.i.i, ptr noundef nonnull readonly align 1 dereferenceable(128) %res.i.i.i, i64 128, i1 false), !noalias !22
  call void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef nonnull align 16 dereferenceable(80) %_21, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) %_5.i9.i.i, i64 noundef 1) #9, !noalias !34
  call void @llvm.lifetime.end.p0(ptr nonnull %_5.i9.i.i), !noalias !31
  br label %_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519.exit

_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519.exit: ; preds = %bb18.i.i.i, %bb4.i.i.i
  store i8 0, ptr %_32.i.i, align 1, !alias.scope !35, !noalias !38
  %_28.i.i = load i64, ptr %_21, align 16, !alias.scope !20, !noalias !21, !noundef !19
  %_48.i.i = call i64 @llvm.bswap.i64(i64 %_28.i.i)
  %_3.i.i.1.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 136
  %_28.1.i.i = load i64, ptr %_3.i.i.1.i.i, align 8, !alias.scope !20, !noalias !21, !noundef !19
  %_48.1.i.i = call i64 @llvm.bswap.i64(i64 %_28.1.i.i)
  %_3.i.i.2.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 144
  %_28.2.i.i = load i64, ptr %_3.i.i.2.i.i, align 16, !alias.scope !20, !noalias !21, !noundef !19
  %_48.2.i.i = call i64 @llvm.bswap.i64(i64 %_28.2.i.i)
  %_3.i.i.3.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 152
  %_28.3.i.i = load i64, ptr %_3.i.i.3.i.i, align 8, !alias.scope !20, !noalias !21, !noundef !19
  %_48.3.i.i = call i64 @llvm.bswap.i64(i64 %_28.3.i.i)
  %_3.i.i.4.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 160
  %_28.4.i.i = load i64, ptr %_3.i.i.4.i.i, align 16, !alias.scope !20, !noalias !21, !noundef !19
  %_48.4.i.i = call i64 @llvm.bswap.i64(i64 %_28.4.i.i)
  %_3.i.i.5.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 168
  %_28.5.i.i = load i64, ptr %_3.i.i.5.i.i, align 8, !alias.scope !20, !noalias !21, !noundef !19
  %_48.5.i.i = call i64 @llvm.bswap.i64(i64 %_28.5.i.i)
  %_3.i.i.6.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 176
  %_28.6.i.i = load i64, ptr %_3.i.i.6.i.i, align 16, !alias.scope !20, !noalias !21, !noundef !19
  %_48.6.i.i = call i64 @llvm.bswap.i64(i64 %_28.6.i.i)
  %_3.i.i.7.i.i = getelementptr inbounds nuw i8, ptr %_3, i64 184
  %_28.7.i.i = load i64, ptr %_3.i.i.7.i.i, align 8, !alias.scope !20, !noalias !21, !noundef !19
  %_48.7.i.i = call i64 @llvm.bswap.i64(i64 %_28.7.i.i)
  call void @llvm.lifetime.end.p0(ptr nonnull %res.i.i.i), !noalias !14
  call void @llvm.lifetime.end.p0(ptr nonnull %_3)
  call void @llvm.lifetime.start.p0(ptr nonnull %bytes)
  store i64 %_48.i.i, ptr %bytes, align 8, !alias.scope !41, !noalias !45
  %output.sroa.12.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 8
  store i64 %_48.1.i.i, ptr %output.sroa.12.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  %output.sroa.20.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 16
  store i64 %_48.2.i.i, ptr %output.sroa.20.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  %output.sroa.28.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 24
  store i64 %_48.3.i.i, ptr %output.sroa.28.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  %output.sroa.36.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 32
  store i64 %_48.4.i.i, ptr %output.sroa.36.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  %output.sroa.44.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 40
  store i64 %_48.5.i.i, ptr %output.sroa.44.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  %output.sroa.52.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 48
  store i64 %_48.6.i.i, ptr %output.sroa.52.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  %output.sroa.60.0.bytes.sroa_idx = getelementptr inbounds nuw i8, ptr %bytes, i64 56
  store i64 %_48.7.i.i, ptr %output.sroa.60.0.bytes.sroa_idx, align 8, !alias.scope !41, !noalias !45
  call void @_RNvMNtCsjK63O35OHGN_14solana_ed255196scalarNtB2_6Scalar25from_bytes_mod_order_wide(ptr noalias nofree noundef nonnull sret([32 x i8]) align 1 captures(address) dereferenceable(32) %scalar, ptr noalias nofree noundef nonnull readonly captures(address, read_provenance) dereferenceable(64) %bytes) #9
  store volatile i8 0, ptr %output.sroa.0, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.5, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.6, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.7, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.8, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.9, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.10, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.11, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.12, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.13, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.14, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.15, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.16, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.17, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.18, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.19, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.20, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.21, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.22, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.23, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.24, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.25, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.26, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.27, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.28, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.29, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.30, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.31, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.32, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.33, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.34, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.35, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.36, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.37, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.38, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.39, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.40, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.41, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.42, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.43, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.44, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.45, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.46, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.47, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.48, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.49, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.50, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.51, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.52, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.53, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.54, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.55, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.56, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.57, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.58, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.59, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.60, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.61, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.62, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.63, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.64, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.65, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.66, align 1, !alias.scope !47
  store volatile i8 0, ptr %output.sroa.67, align 1, !alias.scope !47
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %bytes, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.1 = getelementptr inbounds nuw i8, ptr %bytes, i64 1
  store volatile i8 0, ptr %_54.i.ptr.1, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.2 = getelementptr inbounds nuw i8, ptr %bytes, i64 2
  store volatile i8 0, ptr %_54.i.ptr.2, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.3 = getelementptr inbounds nuw i8, ptr %bytes, i64 3
  store volatile i8 0, ptr %_54.i.ptr.3, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.4 = getelementptr inbounds nuw i8, ptr %bytes, i64 4
  store volatile i8 0, ptr %_54.i.ptr.4, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.5 = getelementptr inbounds nuw i8, ptr %bytes, i64 5
  store volatile i8 0, ptr %_54.i.ptr.5, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.6 = getelementptr inbounds nuw i8, ptr %bytes, i64 6
  store volatile i8 0, ptr %_54.i.ptr.6, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.7 = getelementptr inbounds nuw i8, ptr %bytes, i64 7
  store volatile i8 0, ptr %_54.i.ptr.7, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.12.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.9 = getelementptr inbounds nuw i8, ptr %bytes, i64 9
  store volatile i8 0, ptr %_54.i.ptr.9, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.10 = getelementptr inbounds nuw i8, ptr %bytes, i64 10
  store volatile i8 0, ptr %_54.i.ptr.10, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.11 = getelementptr inbounds nuw i8, ptr %bytes, i64 11
  store volatile i8 0, ptr %_54.i.ptr.11, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.12 = getelementptr inbounds nuw i8, ptr %bytes, i64 12
  store volatile i8 0, ptr %_54.i.ptr.12, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.13 = getelementptr inbounds nuw i8, ptr %bytes, i64 13
  store volatile i8 0, ptr %_54.i.ptr.13, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.14 = getelementptr inbounds nuw i8, ptr %bytes, i64 14
  store volatile i8 0, ptr %_54.i.ptr.14, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.15 = getelementptr inbounds nuw i8, ptr %bytes, i64 15
  store volatile i8 0, ptr %_54.i.ptr.15, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.20.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.17 = getelementptr inbounds nuw i8, ptr %bytes, i64 17
  store volatile i8 0, ptr %_54.i.ptr.17, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.18 = getelementptr inbounds nuw i8, ptr %bytes, i64 18
  store volatile i8 0, ptr %_54.i.ptr.18, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.19 = getelementptr inbounds nuw i8, ptr %bytes, i64 19
  store volatile i8 0, ptr %_54.i.ptr.19, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.20 = getelementptr inbounds nuw i8, ptr %bytes, i64 20
  store volatile i8 0, ptr %_54.i.ptr.20, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.21 = getelementptr inbounds nuw i8, ptr %bytes, i64 21
  store volatile i8 0, ptr %_54.i.ptr.21, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.22 = getelementptr inbounds nuw i8, ptr %bytes, i64 22
  store volatile i8 0, ptr %_54.i.ptr.22, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.23 = getelementptr inbounds nuw i8, ptr %bytes, i64 23
  store volatile i8 0, ptr %_54.i.ptr.23, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.28.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.25 = getelementptr inbounds nuw i8, ptr %bytes, i64 25
  store volatile i8 0, ptr %_54.i.ptr.25, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.26 = getelementptr inbounds nuw i8, ptr %bytes, i64 26
  store volatile i8 0, ptr %_54.i.ptr.26, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.27 = getelementptr inbounds nuw i8, ptr %bytes, i64 27
  store volatile i8 0, ptr %_54.i.ptr.27, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.28 = getelementptr inbounds nuw i8, ptr %bytes, i64 28
  store volatile i8 0, ptr %_54.i.ptr.28, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.29 = getelementptr inbounds nuw i8, ptr %bytes, i64 29
  store volatile i8 0, ptr %_54.i.ptr.29, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.30 = getelementptr inbounds nuw i8, ptr %bytes, i64 30
  store volatile i8 0, ptr %_54.i.ptr.30, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.31 = getelementptr inbounds nuw i8, ptr %bytes, i64 31
  store volatile i8 0, ptr %_54.i.ptr.31, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.36.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.33 = getelementptr inbounds nuw i8, ptr %bytes, i64 33
  store volatile i8 0, ptr %_54.i.ptr.33, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.34 = getelementptr inbounds nuw i8, ptr %bytes, i64 34
  store volatile i8 0, ptr %_54.i.ptr.34, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.35 = getelementptr inbounds nuw i8, ptr %bytes, i64 35
  store volatile i8 0, ptr %_54.i.ptr.35, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.36 = getelementptr inbounds nuw i8, ptr %bytes, i64 36
  store volatile i8 0, ptr %_54.i.ptr.36, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.37 = getelementptr inbounds nuw i8, ptr %bytes, i64 37
  store volatile i8 0, ptr %_54.i.ptr.37, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.38 = getelementptr inbounds nuw i8, ptr %bytes, i64 38
  store volatile i8 0, ptr %_54.i.ptr.38, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.39 = getelementptr inbounds nuw i8, ptr %bytes, i64 39
  store volatile i8 0, ptr %_54.i.ptr.39, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.44.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.41 = getelementptr inbounds nuw i8, ptr %bytes, i64 41
  store volatile i8 0, ptr %_54.i.ptr.41, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.42 = getelementptr inbounds nuw i8, ptr %bytes, i64 42
  store volatile i8 0, ptr %_54.i.ptr.42, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.43 = getelementptr inbounds nuw i8, ptr %bytes, i64 43
  store volatile i8 0, ptr %_54.i.ptr.43, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.44 = getelementptr inbounds nuw i8, ptr %bytes, i64 44
  store volatile i8 0, ptr %_54.i.ptr.44, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.45 = getelementptr inbounds nuw i8, ptr %bytes, i64 45
  store volatile i8 0, ptr %_54.i.ptr.45, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.46 = getelementptr inbounds nuw i8, ptr %bytes, i64 46
  store volatile i8 0, ptr %_54.i.ptr.46, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.47 = getelementptr inbounds nuw i8, ptr %bytes, i64 47
  store volatile i8 0, ptr %_54.i.ptr.47, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.52.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.49 = getelementptr inbounds nuw i8, ptr %bytes, i64 49
  store volatile i8 0, ptr %_54.i.ptr.49, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.50 = getelementptr inbounds nuw i8, ptr %bytes, i64 50
  store volatile i8 0, ptr %_54.i.ptr.50, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.51 = getelementptr inbounds nuw i8, ptr %bytes, i64 51
  store volatile i8 0, ptr %_54.i.ptr.51, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.52 = getelementptr inbounds nuw i8, ptr %bytes, i64 52
  store volatile i8 0, ptr %_54.i.ptr.52, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.53 = getelementptr inbounds nuw i8, ptr %bytes, i64 53
  store volatile i8 0, ptr %_54.i.ptr.53, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.54 = getelementptr inbounds nuw i8, ptr %bytes, i64 54
  store volatile i8 0, ptr %_54.i.ptr.54, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.55 = getelementptr inbounds nuw i8, ptr %bytes, i64 55
  store volatile i8 0, ptr %_54.i.ptr.55, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  store volatile i8 0, ptr %output.sroa.60.0.bytes.sroa_idx, align 8, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.57 = getelementptr inbounds nuw i8, ptr %bytes, i64 57
  store volatile i8 0, ptr %_54.i.ptr.57, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.58 = getelementptr inbounds nuw i8, ptr %bytes, i64 58
  store volatile i8 0, ptr %_54.i.ptr.58, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.59 = getelementptr inbounds nuw i8, ptr %bytes, i64 59
  store volatile i8 0, ptr %_54.i.ptr.59, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.60 = getelementptr inbounds nuw i8, ptr %bytes, i64 60
  store volatile i8 0, ptr %_54.i.ptr.60, align 4, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.61 = getelementptr inbounds nuw i8, ptr %bytes, i64 61
  store volatile i8 0, ptr %_54.i.ptr.61, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.62 = getelementptr inbounds nuw i8, ptr %bytes, i64 62
  store volatile i8 0, ptr %_54.i.ptr.62, align 2, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  %_54.i.ptr.63 = getelementptr inbounds nuw i8, ptr %bytes, i64 63
  store volatile i8 0, ptr %_54.i.ptr.63, align 1, !alias.scope !50, !noalias !53
  fence syncscope("singlethread") seq_cst
  call void @llvm.lifetime.end.p0(ptr nonnull %bytes)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.0)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.5)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.6)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.7)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.8)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.9)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.10)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.11)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.12)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.13)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.14)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.15)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.16)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.17)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.18)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.19)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.20)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.21)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.22)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.23)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.24)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.25)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.26)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.27)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.28)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.29)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.30)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.31)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.32)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.33)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.34)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.35)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.36)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.37)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.38)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.39)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.40)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.41)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.42)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.43)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.44)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.45)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.46)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.47)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.48)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.49)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.50)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.51)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.52)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.53)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.54)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.55)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.56)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.57)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.58)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.59)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.60)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.61)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.62)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.63)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.64)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.65)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.66)
  call void @llvm.lifetime.end.p0(ptr nonnull %output.sroa.67)
  ret void
}

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #2

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write)
declare void @llvm.assume(i1 noundef) #4

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #6

; Function Attrs: nounwind nonlazybind uwtable
declare void @_RNvNtCs7dqAOVfn11v_4sha26sha51211compress512(ptr noalias nofree noundef align 8 dereferenceable(64), ptr noalias nofree noundef nonnull readonly captures(address, read_provenance), i64 noundef range(i64 0, 72057594037927936)) unnamed_addr #1

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i128 @llvm.bswap.i128(i128) #7

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.bswap.i64(i64) #7

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #8

attributes #0 = { nofree norecurse nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #3 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #4 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: write) }
attributes #5 = { nonlazybind "target-cpu"="x86-64" }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #7 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #8 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #9 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519: %self"}
!6 = distinct !{!6, !"_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519: %buffer"}
!9 = !{!10}
!10 = distinct !{!10, !11, !"_RNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB5_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core: %self"}
!11 = distinct !{!11, !"_RNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB5_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core"}
!12 = !{!13}
!13 = distinct !{!13, !11, !"_RNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB5_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core: %buffer"}
!14 = !{!5, !8, !15}
!15 = distinct !{!15, !6, !"_RNvXs5_NtNtCsbCMGC99J5wG_6digest9block_api11ct_variableINtB5_12CtOutWrapperNtNtCs7dqAOVfn11v_4sha29block_api13Sha512VarCoreINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIB1Y_IB1Y_IB1Y_IB1Y_IB1Y_IB1Y_NtB20_5UTermNtNtB22_3bit2B1ENtB3g_2B0EB3u_EB3u_EB3u_EB3u_EB3u_EENtB7_15FixedOutputCore19finalize_fixed_coreCsjK63O35OHGN_14solana_ed25519: %out"}
!16 = !{!13, !8}
!17 = !{!10, !18, !5, !15}
!18 = distinct !{!18, !11, !"_RNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB5_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core: %out"}
!19 = !{}
!20 = !{!10, !5}
!21 = !{!13, !18, !8, !15}
!22 = !{!10, !13, !18, !5, !8, !15}
!23 = !{!24, !10, !13, !18, !5, !8, !15}
!24 = distinct !{!24, !25, !"_RNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB7_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0CsjK63O35OHGN_14solana_ed25519: %b"}
!25 = distinct !{!25, !"_RNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB7_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0CsjK63O35OHGN_14solana_ed25519"}
!26 = !{!24, !13, !18, !8, !15}
!27 = !{!28, !10, !13, !18, !5, !8, !15}
!28 = distinct !{!28, !29, !"_RNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB7_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0CsjK63O35OHGN_14solana_ed25519: %b"}
!29 = distinct !{!29, !"_RNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB7_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0CsjK63O35OHGN_14solana_ed25519"}
!30 = !{!28, !13, !18, !8, !15}
!31 = !{!32, !10, !13, !18, !5, !8, !15}
!32 = distinct !{!32, !33, !"_RNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB7_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0CsjK63O35OHGN_14solana_ed25519: %b"}
!33 = distinct !{!33, !"_RNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB7_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0CsjK63O35OHGN_14solana_ed25519"}
!34 = !{!32, !13, !18, !8, !15}
!35 = !{!36, !13, !8}
!36 = distinct !{!36, !37, !"_RINvMs7_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE10digest_padNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB3u_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0ECsjK63O35OHGN_14solana_ed25519: %self"}
!37 = distinct !{!37, !"_RINvMs7_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE10digest_padNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB3u_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0ECsjK63O35OHGN_14solana_ed25519"}
!38 = !{!39, !40, !10, !18, !5, !15}
!39 = distinct !{!39, !37, !"_RINvMs7_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE10digest_padNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB3u_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0ECsjK63O35OHGN_14solana_ed25519: %suffix.0"}
!40 = distinct !{!40, !37, !"_RINvMs7_Cs9ruV6Mq2l7p_12block_bufferINtB6_11BlockBufferINtNtCsiVSo6Qqr6PT_7typenum4uint4UIntIBS_IBS_IBS_IBS_IBS_IBS_IBS_NtBU_5UTermNtNtBW_3bit2B1ENtB27_2B0EB2k_EB2k_EB2k_EB2k_EB2k_EB2k_ENtB6_5EagerE10digest_padNCNvXsd_NtCs7dqAOVfn11v_4sha29block_apiNtB3u_13Sha512VarCoreNtNtCsbCMGC99J5wG_6digest9block_api18VariableOutputCore22finalize_variable_core0ECsjK63O35OHGN_14solana_ed25519: argument 2"}
!41 = !{!42, !44}
!42 = distinct !{!42, !43, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %dest.0"}
!43 = distinct !{!43, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519"}
!44 = distinct !{!44, !43, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: %src.0"}
!45 = !{!46}
!46 = distinct !{!46, !43, !"_RINvNtCsgxBkk5gSRhY_4core5slice20copy_from_slice_implhECsjK63O35OHGN_14solana_ed25519: argument 2"}
!47 = !{!48}
!48 = distinct !{!48, !49, !"_RNvXs9_Cs2F8OvSoAkiP_7zeroizeShNtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self.0"}
!49 = distinct !{!49, !"_RNvXs9_Cs2F8OvSoAkiP_7zeroizeShNtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!50 = !{!51}
!51 = distinct !{!51, !52, !"_RNvXCs2F8OvSoAkiP_7zeroizehNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!52 = distinct !{!52, !"_RNvXCs2F8OvSoAkiP_7zeroizehNtB2_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
!53 = !{!54}
!54 = distinct !{!54, !55, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMuthENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519: %self"}
!55 = distinct !{!55, !"_RNvXs4_Cs2F8OvSoAkiP_7zeroizeINtNtNtCsgxBkk5gSRhY_4core5slice4iter7IterMuthENtB5_7Zeroize7zeroizeCsjK63O35OHGN_14solana_ed25519"}
