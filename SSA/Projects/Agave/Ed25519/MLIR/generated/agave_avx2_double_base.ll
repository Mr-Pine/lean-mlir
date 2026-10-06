; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_avx2_double_base.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"backend::vector::avx2::edwards::CachedPoint" = type { %"backend::vector::avx2::field::FieldElement2625x4" }
%"backend::vector::avx2::field::FieldElement2625x4" = type { [5 x <4 x i64>] }

@alloc_8241d8c786577e4be83f121c84457b0a = internal unnamed_addr constant [14 x i8] c"src/window.rs\00", align 1
@alloc_a8fabae8f73f66aef6660ad7c9447c5d = internal unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_8241d8c786577e4be83f121c84457b0a, [16 x i8] c"\0D\00\00\00\00\00\00\00\DD\00\00\00\09\00\00\00" }>, align 8
@alloc_f7b128ba219626851d37833adc9e2368 = internal unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_8241d8c786577e4be83f121c84457b0a, [16 x i8] c"\0D\00\00\00\00\00\00\00\0B\01\00\00\09\00\00\00" }>, align 8
@_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE = internal constant [10240 x i8] c"\E1~6\00JF\99\00\93y\22\01\A0\B9\10\00\84\B6\03\00<\82\ED\03\00\00\00\00a\F3\B9\01\FFr\D7\01\9A&\C2\03C\A4\18\00\22\C2M\00\00\00\00\00\C8\CB4\03\00\00\00\00\C8\F6\DC\01+\AB\CB\00\08\88g\02m\1F\22\00_\AD\AA\00\00\00\00\00\17\A1W\01\00\00\00\008\22\84\00\A5\C2\A9\00\C1\A3\BC\01\86\D9\E8\01\13\C0\B0\01\00\00\00\00\81\0D\D9\03\00\00\00\00\AF\07\93\00\B0\A1\FB\01\1B+\D1\02\16-B\00\1C\06\F1\00\00\00\00\00\19\1DP\01\00\00\00\00\C0\F3I\00!\AF\CE\02\8A\DB\DF\01\C7\14\C0\01\A1\82y\01\C6\FD\8F\02\14\82\17\01\BC\ED\F4\00B\9AF\01\E5\D3\E3\01\D7\1F\B9\01\8B\1A$\00o\1A\D1\00\FE(\07\00\06i:\03\BA\B1'\00b[\F7\01\09\E7\C7\03\12\9B\CD\01|`\E7\00\CC'\1A\01\D7q\AD\01\CFK\1F\02w\C6\D0\00x\E7\19\01\A7|\BA\00\AE\CCK\00\9C\AC\8D\01\C6\D9\8C\01c\A04\01\F1k\94\00\02D\00\00\0Bp\13\01-8\9C\03-z\B9\03J\C0\B5\00\9A|N\01\C9p>\00\D7\AFF\02\FBFV\01\B9\9D\DE\01\85\E7\14\01^\04\BB\03\F9\FA&\00t0\08\000\F4\B5\00\D3\03\97\01y?\0D\01\ABks\01m\98\B0\00]\D4\A4\01\1E\87\E0\01\B5\84\BA\01P\CF\A4\00G\F9\17\03ki\AC\01\9DA8\01\A1\F9V\03\DD\A8\A5\00Y\EB\B3\00\16x\98\01L'\82\01\98]Z\00\1D-e\00\8A4\8F\004\E5\DD\01\97\C9l\01\A5\91\F8\00Vs\EA\01\B2h\A4\03\7F,\06\01\94$6\00&s\B7\00\AA\17Z\00mF\FE\02\08u\B4\00\19\CES\00?_\9E\00\7F\FB4\00\C6\A2\02\008~\E7\01<#\A2\00\DD\D6\E7\00\FA\B4]\01\FAEi\01\B8S3\03\11\0CG\03;\9E\99\00`A\B3\00M\06\E0\03\D4\FB\13\00\C0\E8\C3\01^T\B9\01\BB\08\99\03\8Bg+\01&\A8\97\00\1D\F7\CF\01\92\BEF\03\8E\0A\EE\03\D2aU\00\E3r\88\01(r\DE\03\0Fh\D2\018N\F3\00\D5\A0\81\005\CF\11\00\FAFK\03U\95\AF\00\DE\CD\E2\01\B0\B9\97\02j\1F$\00!j\C5\00\8A\E0\A3\01@\05\0A\00b\D5&\00yw\C6\00\D3V\07\00\AA\07K\02\B8M\BA\03}\DD\82\01\F0\F5\AF\00\96cR\01\B9\CB<\00u\8B\A3\01\10\B9>\00\90e,\00:\D4\D2\01\DF9\EF\00\BF\E5&\00\E1z\06\02\D1)\B6\03\D7\9B\1F\00\A44i\00>\9D+\03Y\B7\D0\02\FF\C7a\00\D9n]\00\91\BB\F0\01\FE\C4\CF\031s\C0\00\0Ep7\00e\0Ao\01\FA\22>\02\AF\F7\DC\00$\03\82\00&\EC^\03\FE\05\A4\00\FD\A2\B7\00\AA\A2\B7\01\08\0F\16\00\91\D80\02\7F\B3\B8\00\A9\85\9C\00 \D6[\01\DF\09\E8\02\B8U\11\00\A0#\8F\00\C3\89\15\00s\82Q\009\D8\A0\01\EF\CE\93\00P\D5B\01\E6|U\02Xe8\01\01LK\00'\15\AA\03\01\80\B0\02`\DAR\00\0F\E6\C6\00a`y\00~\0D\81\03\D3\BC\DF\01\8D\A3k\00\A5\86J\02+a2\02\90\D0\14\00\9A\FC\DD\00\93\8F\8E\01P8*\02\BD\12K\00H\83\E3\01E\1A\03\02\F7\F0(\02.\97\E8\00\15\C8\EA\01#\DF\8A\01\B87\C6\02\CF\DF(\01W\D9$\00\B6\07\01\01Xs^\03j\AA\F2\014\CF\96\01\1C\EB\E1\02JW\96\02\A2\F5\B9\00xV|\01\EAFq\004\DC\88\01>\89\C3\00\FBp\09\01\F4\A5\C3\03sE\EB\01d`>\00I\A8\80\00@\C0\CF\01]C\D0\02\19 \89\00o#\8A\00\E9\\\CB\03\1F@\DC\02\A0\BC,\00\C0w0\01#?\B3\00\F5\81\13\03u\B4?\01\97\EE\CB\00\BD\D57\00\F9\12\81\03s|Z\00\00\C1'\00\C8\89\B2\01x\DC\08\00\97\05:\01\BE\D5'\00g\89}\02\8E\DC\05\01\E3\1F\A3\00\8F\D3s\01W\93\CD\02\C3\A40\02&\9FR\00\0D\C0\C8\00]\FE\C9\00W\FB\0C\03\B2\A3\88\00\CE\9A\BA\01\15\85Y\01\1D,d\03\01^\\\01,\02\9D\00\B1a\15\00i\EE\81\03\84\AC\D7\01L\EE\EB\01@\DB\EA\005\F2\E7\00\ED\BA`\00\84L\FA\00E-U\03\\\C5\C2\01\CDe\19\00bBK\01X\03K\02\04\A5\CE\02\C1\B2\0D\01\D2q\F2\01B\94\\\01\8D\C2\A4\00\CAY\A4\01\CF\C4\E2\01hq\0E\02/\0F\96\01k\03-\01\A9\D1\C8\00\14m\E0\01\A41\DD\00\18V\D5\00\18\D0\9C\00H\B8W\004n\16\02\FB\D2)\00\ED\1Er\00\97D}\03\D7\D6\E2\00\E9\87\ED\01\8AT\08\00p#\BC\03B\EAi\00mU\AA\01\B0\BD\B6\00P\0F`\02uP\AB\02\B1\85\EF\00\05!t\01\EE\C1\BE\00|\E8\FE\02\F9\FEa\01\C02\E7\01\1E\C5z\011\93\AA\01\B8\82\9C\01\B1j\9D\00\ADK\D7\02>,\AA\00\0F\DB\EF\00\F1\88\CC\01u\F1<\01x\B40\01\D1\A4\DF\01=\BE$\01`\9F\A4\01=t\9E\00/&,\00\C29\8D\00~\86\8E\02)\F8\B5\00)U\EA\01\FA\8D\F3\0107U\03(\98\EF\01\1E\84*\01\D9\18T\00\89z\10\01\91\82\D9\02\12;\DE\0076\AB\01\80\EA\F7\01g\0DN\028\9E\E7\01]\C4\A0\01N\A3x\03q\E1\F2\00\90\F7\1F\01\B6\EE'\01Y\1C\09\01\AB\19]\00=\D9I\00$\A9d\00A\89\FD\03\D7<\F0\00\E1I\18\01\90\D8\0E\01\BD\B5q\02\F9v\8C\00# (\00q\E3\EA\01\E5l\F6\03\B6I\1D\00Jj\B0\01\A7\80p\00\11\0A\04\02'k?\00%\EA\9D\01\E8d\C2\00\A6,\A1\02\90T}\03\1B\A6W\01\B03\B4\00\88|\BA\01\02\18\06\03\13\0E\CD\01\99\E3\88\01D\84g\01\F4z?\00\8D\DE\89\00\D0\DE{\01\E7\B6^\02\A8\22\88\03\D7\84\84\008#W\01\9EX\C1\00\ED\E2\\\03\F1\8C\F5\00\BFX\CA\01W\13=\00\0E\B7\D9\02\CF\1Em\00\B0\D1\B1\01\14l\A3\03~\BC!\02\A0\E3\D2\01k\16,\01\9F\AD\A1\02\05}d\02\A5n\04\002\00\B2\014\98\1F\01\E1\ED\14\00\11`\FC\01@j\C9\00r\FE\99\02Qs\04\01\94?\B8\00\87u\17\00\81b\99\00&\A8H\02\E5'\A3\01\81\D5P\00\C2\02\06\03\95\D17\011\C3\9D\00Yj*\00]V\18\01\91\FF\EB\00\12\D7y\01\EC\04S\01\0F\A4f\01p\0C\DA\02\BA\EB\9E\00)\C7'\00\17\7FH\03\17;\B3\02\8E\A3\F4\00l\02[\00\90\BE\0E\01\89\E5w\01\CAp)\01c\1CO\00\D9\92\FD\02.{\17\02\FF4\99\00\00[h\01\9CUE\00\1F\CA\AF\03\9D\CB=\00\B5Fq\00\E6\AE5\01\A0~b\02\96\05\A0\00\9D\1C\EF\00\F8\0A\19\03\D0\EB~\03\A8\D57\011`4\00\AC\F2\18\02w\C59\03\0C\B5\C3\00\1E\DF_\00\03=\A4\01\B6\A9\D3\01`\BFY\01As\90\00\CDs\15\03\19mm\02\16\A7\09\01\BE\89\80\01\8F\D1B\01\A8|\09\028(\99\01H\E3Z\00\F2K}\00hIz\00W\88_\00\C0WQ\01\\\11\EB\01\EF\16\17\03\DE\A1%\00W!\B4\01\FB\08\9F\01\8D\B8:\00\A1H\E4\01\0D3\A6\00\8E\BEK\00\9A\CC\E5\03=\B4\F0\01\E5\13\B9\01~f\FD\00\DCp\EB\01\B7\E6\92\01\B1.t\00\C6\01\B5\02N\BE\E8\03Y\E7\D2\00,`(\00\0A\B3&\02g\B9t\03v\0F\EC\01\FEx\\\01\D5\14\D9\015\12N\03C\83\\\007\D26\01\9B\CE\A1\01\BB\C2\03\03\87\F9\07\00\A2t\C2\01\D9\1E\DB\01A\B8e\02\11\92\A5\01\C3\D5\1B\00\CBh\8A\03oD\04\01a\83\BE\01I\90]\000\DF!\03/\BC\95\02_\F6\C0\01\08a \01\A6\BAW\00\F4\FA\97\02\0Bn\AD\00\80IH\01R\DA\E8\03\E4\F5\A1\03\C4\C2.\01\97\E2U\00\E1\04'\01,\17!\03\D9\CC\BB\00\A7_P\00G\031\00.\E0\89\00\91\AC\BC\01z\B6\D1\01\12\BDi\03>\0Fh\00\C9\0DQ\01\B5\8A\95\00\FD\9AI\03h\DF\B5\03O\10\D2\00\813\81\01\B2\9F=\03-W\B0\03\D9\C7u\01%\C4&\00\82\8C\E9\03\B3\B6\97\03!\03\15\01[U\B2\00\AF\11\BF\00]\F1\8C\01i\8E\D5\00/\09\FD\01\E20h\012\8Ep\00S|\9F\01\1C`\06\01\0B\A3\8B\037\B9\99\00\95\C3\08\00Y\DD:\00\FB\8C\A8\03}\9E\FF\02\E9\F8O\00\9C\C04\01]?i\01\B4\C4j\00\01\F4<\01\8F=\01\018\FAj\02\90Z\C9\01T\92k\00\B2\8C\DE\00\15\C8\15\00t\E0\CA\00\92\A6\E4\01\DC\A5\E0\01U\EF\99\03\B4#B\03P\D6O\01\09p{\00/\\w\03\BC\A8z\02\F8\1A\EA\00w\9A\0E\00\AC\22R\02\BA%5\028\84{\01a\22\F7\01\19\C1\D3\01\09\90\0E\03\C6\97C\01\1A\22%\00I\02\C3\00^3\E4\01\DC\E1\F8\01e\C7\F8\01\91\D8\F8\03\09\DB\8B\02D\CD\FC\00\89x\E9\00\FFY\17\00\A3\8E\F7\01\C7^?\01\E5\15A\01\DC\EE\E4\00'\C8P\00\85\BB^\01\84\D4 \01\ED\DE\F1\01\9C+\16\012l\E1\00z\F1\9E\01\A3k\00\00\EF\1A\E5\03V\A9\03\01\18\98w\00\8B\0FH\01\BD\EC\8D\02\E8\F0V\01M\AA\D0\00\11\B8p\01\C4\EC\FC\02\9D$[\00\09\88p\01v\11\18\00\DE\92\83\01\A4\8D\1C\01\F6\C5\EB\019\98\F3\02\B0\16\86\03\96A\E3\01\11:7\01J\E6\AD\03\8A\F0\09\00\A0\AF\02\00\9Ah\91\00\9Cw\AE\03x\95\8A\00\C8g\F4\01,\EC\EC\00|\B5\E4\02D\A7\F1\01v\EF!\01e\D9\87\01K\98\E9\01\D9G\9E\00#E\89\00\E7\93\E5\01\BC\18\22\02\C6\87\FA\02\D8\08\D2\01\97\7F\10\01\95h\DE\02\A1\DEv\03K{\A7\01\C4\97\C8\01\CB\CF>\03\B6\B7\94\02\F5v\8E\00\A6\A1\F0\00j\D2p\03\BA\AE9\01\D9\EA\8E\00\0E\80\F4\00g\06\F7\00sK+\00\A5\05s\01q\0A\9C\01\90\9E\AF\01\BCL\A4\00\C3\06\16\01t\99R\00\CBI\E0\02V\E9x\03 \0B\B5\007J\B3\01`:\AF\02\DD\01\7F\03v^\87\01<\1B\A7\00\1E{\89\02\FB\14\0F\02\CA1a\01\DEDS\01\D6\B9\E2\00i%}\01/\80\E5\00T\D2B\00e\A5\D6\02P~f\02t\CE\EE\00\90\7F\1E\00\97\D5o\01%\E2\92\00\B9A\05\00\B6W\81\01X\A5\0F\02\B1\C0\8E\03\11n\88\01\05D\8B\01\0B;\1E\00\06\0A@\02P\BE\8E\01r\ED\1A\00'\C3\CA\00\AE\95\B7\01e6\BF\00\D5 \17\01\1B\A3\D3\00H\DF\DF\01SS\E4\00m\AEs\00\A5\\9\01\1Ba\16\02f]D\01A\FB\FC\01\C4\193\0295\19\01\01W\A9\000\B2Z\00\A5l\9C\03\C7\97b\02\D3\89\D1\01\07\FD\E6\01I&\EE\02\BB\C1l\024\09\01\00\15g\84\01\1D\97[\01'\A7\89\01\9D\9A\F3\00;wY\00\8D\E5\9F\03W\9CD\00q\9BO\00\0C\13\D7\00\CBQ\09\03W\D0\05\03tB&\00[\9D\99\01(\A5\0F\02\19\A40\03\15\B5\A5\00\18\1C\1F\01 N\89\02\F9dZ\02\98\83g\00m\A0\07\01E\82\94\023\BB\A9\01\EBQ\FA\01\A27*\00E\0A\04\01\94\89\0F\00\96\88\FD\01P\B3I\00\82}\96\03'\CD\D5\018Uy\01+t\DD\00\F2\DC>\01\E1\1C\B8\01l\E22\01\A8\A6\0A\01\A2\8C\BE\02\D2\D6%\01\CD\9EF\00\BF\EF\E2\01\9C\E9\A1\01E\B7\F8\03~\1D\B0\00\\\C7a\00\A8 f\038\DE\F3\02\B6\0C\E9\01=\EF\DD\01\FB\13\0A\01\A4\F0\F5\02\93\04,\00\A7\B68\01\EF\B4\8C\03\B3\D8\C9\02\D5\85\BA\01H\AE\1B\00\C4\A2N\01\9A\13\0F\03p\\\E4\00\8E-\D5\01\D9\E1\FA\00\E9\05'\02\C8Ji\00z0\09\00W\DF\C5\02\8C\E0\FA\00\9E!|\00M\85K\01ym?\02\07\FE\F2\01\885\B2\00\9DG\C8\00\17\A2\EA\01\AE\8D\8F\00\B1/\95\010y\09\00\7Fz%\01\D0\16\CB\01\10\FE\DF\00>\AF*\00\86\A8J\00\F5\F6y\00j\C7\03\00$\F3U\00>\18;\02'\09\97\01\9B\E7\9D\01C\EF\CD\00\09\E7\05\03\99\1Dd\02\07\F5\B2\01\D1\C3\A8\01\D3\00\03\00\BD\EB\18\01<\E1k\00\FC\FBJ\01+'\C6\01\CB\B7y\01Hl\94\00\03\C8\A6\009\1E\B0\01\BA\8Fm\02\90\95\F7\00p}y\01\F0\B7\D4\03\E1\80\1B\02\18\09x\00\0D\11\D0\00/R\09\02\FFn\E1\02\86\9F\9C\01\07\C6h\01\BE\EA\EA\02\D8'(\03}\09\D0\01\F6=\\\00\07\90\1B\01\AA\86{\02Q\BE\95\00X;\8E\01.\E3\87\01\D6\EB\97\01\CA\22&\01\08\94\A2\00\14\09\14\02\C0a$\03k\E4V\00r-\CC\00\12\F1\E6\00W\F1\1B\00\01Y\83\00\E1v\07\01\8Fe\92\03<\B1\A3\02a;\A8\01]N\1C\00}4\D9\00_\03/\02\96u\AC\00=\E8\A6\00\19\C4\7F\00.\AA\EC\02\E7AK\00{\80\F7\01\B0\0CK\02d\A1\BF\01\DCQ\DD\00}\B6V\01\DA*\E5\01\83\EE\06\03\D69\8A\01y\86\89\01\D1\0A\EA\03\C2X\AD\00\05\1E\98\00$t\89\00\E2\F1\FE\02\CD\E8\BB\02\12\0A\F6\00G\02\EA\00Jx\0D\00\FF\D7\88\02\8E\13\AC\009@\91\01<\F2\85\02\94=\86\03P\88\DC\00\B1\AA\08\00\BD,\03\00\A9\D3\11\02\CFg\E8\01\CDD\E2\00\82\B5\11\01\D092\02\09\D9\E9\01b\C9C\00\9BJ-\01+\B0\E2\01\AB\0Bm\00\BBE\F1\00\15\13\D5\01\A8\BBM\02\D5\B0\BF\00O-\CB\01H\99~\01#e\B6\01A\E6\A9\01>\C7\C9\01\12\A3+\00\14\9A\8C\01\CE=\0F\01\DAc\9D\01\02\87#\00\DAu\94\03@\89\1B\01\E0@\13\01}(x\03\AAe\11\01R\18\1E\00\C6\DF\B4\00\90\84(\00\9E\D1\9B\03F\04\19\01\10\C0\CA\00\DAn\BD\03\0DA\A9\03q2D\013\96\22\00C\0A\95\03\E3\E6\E1\00\0Ah\E1\00\0A\8B;\01\B2\CC\9B\011W\EC\00`\EB\0A\00\ED\B2#\00\D0)\19\03i~\08\01/)O\01\0Cg\A5\00\A4\EB\1C\01\1F\D6o\03\9E\CB\F4\007\D7)\01\BBA\BF\03\A1C\0C\01\FBP\96\01'\C6j\01\C6\9D\05\00\17\DD4\000\06\8B\01\FFj\CF\01\15\80\1F\03\8C(\B5\02#\9E\B6\01m\18\8D\003\E1\BB\01U?t\03\91\8C`\01\F3\D3J\00\02\A9\A7\00d\FDX\03\A3oh\01X\AA\9D\00{\E0-\03\D9_\AC\02\BD\B1I\01\B6\15\DA\01\AE\C0@\00\88\E2\0D\02\B67\AC\00&\88X\00\E5\BF\C8\02\8B=\C7\03\F1\A7\B1\00::\1E\00\A9\DD\C5\00\0D\B8\AD\01p\CF:\00\0C\\\D0\01z\D9\B9\00\8A\B1q\02\93u\C3\00\EC\8D\FF\01\15\90F\00A\85\CC\02'\EC\02\01hz\B4\00\8A&\12\03W:\BE\00\A7\18\E5\01\E3\83\E9\00A\DD\F7\02\88\F2\BC\03 Tc\00 \1F\C5\00w\F97\01!\CD\1A\00=2\B8\01+\DAx\00 \12\96\00'\07Z\00\A1\CD\B6\01p\DA\BC\00(\9E\16\014\E9\D9\00r#L\01\AC!\9C\00\E2-1\01\9C7\BD\00\C6\A2>\00o\A8g\01\10D8\00\D8\11\95\01\B5a\CB\00\F9\8F\99\01\0E<\F8\02f\CAT\01\10\BB\03\00O_{\01\D5A\8C\03\E4\06\B5\03\AB\CB:\00\F1\EE\D4\00|\05\BD\00_\BD\D6\02f]\9F\014 \11\01\F3A\C4\03\0B\8E*\02<\B4\DE\00\1B\FEh\008\D3\14\002x>\02\89\BA1\00\EEZ9\01\D2L\CF\01\B4N\9F\00\E0\18\92\00P\F9\B2\00ms\CE\03\A5\DAK\01\DEdT\002\87)\00\B0\D7\17\01(\A9\17\00_\FF\05\01k\A7\88\01\FF@\B2\01]y\C3\03i<J\01(\88\E1\01R\EA\A1\00\8FjO\00\E9h\13\01\9FD\03\00\13\85(\01\AE\06\F8\02&\E3\8C\01\B2\D8\A2\01m\AD-\01]\08\94\01\DDj\90\00\99\EA\BC\01\93w\B4\01<\A5\B1\02\DC\C2s\00\C3Xe\00\D4\CE\E9\03b\F9\1C\03\D4J\D7\01w\A3#\01\81O\D1\02\937R\02Cr\F4\00\E9c\A4\00\83\12\A3\01H\DB>\03\F5\0A;\013\95\0E\01\CD\15_\01<G2\03\C5\A31\00\CAA\EE\008H\1F\03\10\EDl\02\F0\C5k\00\DDj\B2\01\B6\A1\0C\03\EB\AC\A7\02\91I0\01\ABT[\00\04\D0\CE\00\F1\10\1E\02\81\A8\E1\00\C5\BE\1C\00\EF\FD\BC\003\CB\DB\02j\92\BC\01R\1C\1B\00\BEL0\02=\CF=\01\CD\A0a\01\C6}\F7\01$\82\81\02\F6\A2\EA\03\07lS\00(\AA>\01\D9\09\94\02V\1Cn\02\9F\1F\07\01\0B\AB\E7\010'\D6\03)p\98\02\DAY~\01\F0\B2\C0\00\B6\8D\08\01y6|\03v\D3\A9\01:\8A\E9\00\C29\CE\01]nW\02U\96\02\018\85z\01\86\F4b\00\AB\1B\EF\01n!\F8\00T\F0\CE\00\93c\F2\02\C0\DA\A3\001\8C\FA\00\CF\C2\87\00\AB\C7\AB\02\967d\02\FA\09\85\01r\1C*\00\C8\F9\81\01\C0-\1C\03S\90p\01\88\9B\BF\01\B6\8E\85\02N\10i\03\A8\9D\10\00\FB{:\00\F9Z\05\02\DE\F0`\01\E8+j\00\03\9C\C0\00\E58;\00+\E6\E2\00>\CB,\01.\A5\\\00h\17F\02\CA_\9F\03bN4\00G\0C\D2\00\DF\FCt\00\07\AFq\01\90\93\04\01$u^\01\0F\E6h\00\C3\BB\D7\01/\BD\AE\00\80\ABr\01\89m\D0\00O\0B\E8\01@\EA\B6\014\E68\01\1B\B2\DB\03\A4\96\F0\02\DC\96\AF\01s\AD\84\014\97X\02\B7)\85\02h$\90\00`B\0D\00\CC'\EF\02\CB\CAE\01;V\D2\01\C0M\AC\00\8B\E5k\00:\AE\C4\02\8C6R\00\AD|\EB\00:r\9F\01.Xy\02F\98$\00\00\B4<\00NX\0A\03\0DI;\03*\D7s\01h\03\DF\01V\CBJ\02\AC\D4\B6\03\C2\ADf\00\8C\85\01\00\1C\A3\0A\01\B9\22\BF\03\1A\FA'\00\EC\D2\D3\01\15\C0\16\01\17\A1\F4\014M\\\01\E7\C8v\01\0C\B0F\02\D4b\FE\03\88m\D7\00a\C7\FB\00\F0\FE\1E\01\A4\92\DF\03!Y\88\01u0\F0\01\85\B2\88\01\E6a\B6\03\A8,\A5\00\04\B39\01\B1\B4\DE\02+\81\DB\01\92\F9X\01\81\14\91\01p\B3\0E\00/\A1\CC\033\1A\9C\00\00T\85\01.\02\F0\01a*]\00\9Dm\8C\01\09\0Ex\01MIm\00\81\9D{\00\E1\FC\DF\00:N\FE\01\DC\8D\1E\00\DDT\82\00d\AA(\01\E9-I\00\D6\D9{\00\9DC\11\03(`C\00\A4\9C\86\01\19\87S\03\F5\FB[\02\CC\87f\00\AFG\CA\01j\C4\DC\00\ED\A4\83\02\DAY\80\01K\17\93\00M\7F\D5\02j\E5\BC\03O\EA\F3\01\10\D1\17\01\FA\F7\04\02\9D\A7\F4\01\CB\DE\88\00F\D1\C7\00\1DVI\02\15wd\02\B6\15\8D\00:2K\00\A4N\CB\03\16\E2\10\01\C6\96\8F\00I6\8F\01{ML\00\E9#p\00$\EFj\01\F1\BD\F3\01\A1\EC\B3\01C\C6\A3\00\BD\8D\8E\00q$I\01\B0r9\03\87j\EF\01_\B98\01Y=H\01\15w\D7\02\87e\DB\02\82U\BE\01\90#\EF\00U\DF\8F\03y\C1\97\00\97\F4\E3\00\1DU\19\01\F3\9BC\02\17`\83\00\0A\C4\E1\01\1Cz3\00\93\CF\D9\02\A8\E7=\01h(\CA\00\B4\90p\01w\96T\00Z\F2\C2\01U\AC3\00\1Ei\D1\01)[~\01\DB}\E8\00;\7F\86\00kX\EF\01\8E\83U\02\B4\CD\E9\00\FF\BA8\01`\8C2\00\F3\1F\DE\00[#\C6\00\C5\C0z\00\C3y0\00\0A|x\01~\15\C5\01\AA\B9F\01\DB\9C\17\01\16\E0 \00=_g\02\7F\09\0B\01eV<\00\9D\E40\02\0D\1CO\02\89\86\02\00\1A.\E0\00\0B\DA.\00\AB\0F\9F\00X\DF\04\01\82\D3\01\01{T\90\03:\92\91\02)\11\85\00%\0D\9F\00\EE\1E\11\00\0FY\E1\01\AA\1CD\00\DDf\E5\010\91\F7\02\94\F8\A0\03\16\F58\01.\FFX\009\F1\D2\03\DEe\E0\01\FF\D5D\00g\DF5\01\0D\B1+\00\D2\B8o\02\F9\F0\99\01\19=o\01G\F7\EF\00\1E`p\02.\A9\C5\00\0F\8B\97\00\DD\CA\A1\03L\AF\88\02\F5VJ\01f\DBN\01\F2\B0\1C\03\81\8B\A2\03?\84k\00%\D7Q\00\93-@\00p\9B\D1\03\19\AB\15\01\C8\CDo\00r@\12\03H\FBB\01\EDe;\01\12|\B4\00\9F6\90\03I\19\F5\02\D4\AD\EA\00\C3\FC\06\00<8\8E\00\22\0CH\01,z1\00\AE\9D\E1\01\C1\E4\A6\01^6\84\00\12]3\00&\E5\91\01^Sb\03\A6\9D\89\01\BFU\C8\00L^F\01\04}\88\03z\84\FA\02zE\00\01+\7F\FE\01\11\FC\E2\02\B5\CB5\03\FF9\1C\01g\85\EF\01\BBP\83\02\E4\B5\05\03\ACu\CE\00\9Ap\AB\01\85\A1.\01\16\C4T\03(\1A4\01\19)\93\00\C0\DB6\01\F9\92\B1\01\0A\7Fo\01\C0J\E5\01Q\FB\03\02\B9P'\02\A9;\07\01\90\19\17\01\AB\12Z\03\F9\AA\E3\00s\06\1F\00\A3;\C3\01\8BN\1A\00S\93\B6\02G\BB\10\01\E4\A8\07\00+l\FB\02\9A\EC\E0\01\AF\86\EF\00\0D\84\0F\00\95\B9\91\02\AE\B7C\03\993z\00\DB\E8\9F\01\C3\F9'\03TZ\F7\03\C5\A5\E2\00W\8C\D0\01\95\CE\B7\00\15\1Fs\01\8Aw\FC\00\06\1C\15\01\87,\95\03s.\11\00\1D\C1Z\00\A4U)\01\F0ps\02\98\E4\D6\01\A3\15y\00\C6\C5\CB\00\B0<\10\01\E5\CF\A8\00\1Af\19\00P8\97\01(\A8_\00\B3\F8S\01\\\9A\07\01\9B\04E\00\D9f\F2\00\FA\B0b\03\18\B2\EB\00\8AOK\01\EAV\0F\00\8F\05\10\015\F8K\00\E2\98h\00\AD\AB\0B\02:Q\D8\02\0C\166\01?\8E\B3\01\06\89\C3\01\DF\0B\C7\03q\B9y\012\C1\8C\01o\07\FB\03\AA\DEO\00\16\B4\00\00\CC\B6\82\00K_0\01\C2\ED3\01\DE\8B\83\01V\DD8\00\04\E3\CE\03\A5\B7\C3\02\15v;\01\10\E3Q\00\AF\\\8E\03T\A0\E2\02.*\E1\01\F1\E5k\00$\F6\C7\00\A7v\15\00P2s\01\1F\F4.\01\A8c\A3\03\80&\A8\00\C1\C8\E7\01KC%\01\CD%S\02\D5\F5\CB\01\1A@\EA\00\CB\D3\83\00\8Eyj\03zs\A9\03\CB\8D\F1\00N\F7\99\00\E4\BA\BC\02\8F<f\00U\84\01\00\B1rD\01\D7\96j\01I\886\03*\87\\\00\10\96\99\00\B6j\8D\02M\1Bp\03\8F\D7=\00{`\84\01\83\BA8\03\E45$\00\F8\D5T\016\82u\00\938\A5\02q\D1\94\02\C1\C2\FF\00\C5v\CF\01\08\BD\F7\02\1Cyb\01\0Ax\87\01_\83\A0\00\B3\07\0E\00\ED\EE\89\03jn\13\00\8A\FE\85\01'c\94\00\A5\90\82\00\C5\00\89\01\DF!\A6\00c\93\84\01\96R\A9\02\18r\0D\01J\C6\AB\00\19\B9\C5\01\1E3]\01\BCAl\00\15_\99\01M\0B\E0\02\1FB\D7\029\D1\9C\01F\D1o\00AC\A0\013;\E9\03\F5\E5_\01\D5\A3?\00q\E5\94\01\ED)\97\03l\02\CF\01\17\89\89\01\CD\BDC\02\E4\95w\01\80R\91\00~\B8\9E\00\F3z*\00\1E\A9\C1\01\B3\ABG\00;1.\01\D6V8\02\98\13\CA\02\06\93\9C\00,\09!\01\1C\14w\03\C9N\97\03\B2\13\82\01\91ph\00\CE\A9?\01\92\FB_\02ZuE\00\11\06\0E\00\B7$f\005P\A1\02\92\A2\EC\01\C4\AB\DE\012lw\013\B9-\03\CD.\D5\00DCQ\00\7F\FB\DD\03\CE\E1\08\00\81b\12\01\99\D2$\01\F6\B9|\01B\D3\9A\01\B6\AE\BB\01\AE\E7\FB\01E(E\03\EF\96\FE\03k\AD\12\00\E8\9Dd\01\AAc\C0\03\DB\FF\1A\03\B5Z\CE\00\C6Z\CF\01\E5D*\02\FD\AF\83\01\BF\9A\16\01\EA\B1G\00\80\86\FF\02\D4\90(\00\07R\91\01V\D7'\00g\CB\9E\01&\81L\01\E8B\14\01\FF\AE\96\00\00\D3v\03k\01;\037\A9a\00pW\E1\00n\8D\05\02j.\8F\02\F6\F8\E1\00\10\C7Q\01,M\A2\00\E1\C2\BB\01<*\C7\01\90\A2\B3\01I\05\A4\03\C4\08\0D\00\F71\BA\00\97>1\01/>\8D\00\ADXi\00E\D49\01\1FM\05\00\CE\96w\02p\F0\0B\02\C49U\01<h\D9\00\94\DE\B8\00\F0\82z\02\F8\90t\00a%\B9\01\B9\0F\B3\03\0B\D9\8F\03\DB\E3\96\01\\:\B1\00\C0\13\EB\03_e\B9\02J\B8\CE\01\18[\C4\00;\E7\0A\01\B6 \99\02GE\90\00ju\8D\01\22\0F#\034\BCW\02(\09;\00>o&\01N\03\10\01\16\13\D0\01\D1n\F0\01]\98\F3\01'\12\E5\00\114\DB\00\81#\F8\01\E7\B2\E1\00\8CS\D2\03\8BF\87\03\BD\8E\F3\01\E0(c\01\D0\D7\F6\01~`S\01\DA4=\01^lK\00\E0\9C\E7\01\D4\F7\8C\03`|*\00\A4\A9@\00(\8E\D0\02\FF+J\003\B6\1C\01\D2$\E9\00\87\F9\C4\03\DE\B1\AD\01M\F6f\01\0DT\CC\00\1E\C1\F5\03h\B5p\03 \CF\FC\01*\EC\B8\01\11~S\02\DD\90\C1\02\F3&G\01\98\8B~\01_\C0\D0\03h\C5\A2\03\C4\07\FC\00\D3#\C3\01%v\14\01\D8\FD\95\03|E@\000\D9m\01\F9\8D)\02\08\96\B7\03$\C2X\00\0A\DB\02\01\AA\A6\15\01E\88\B9\03|K\04\00\F9\12y\00\B0\E8V\03\EDH\B2\03u\CFI\00\9C\81\F6\01\82\05\C8\01c\A0\0A\03\DF$\D0\011<\FE\01\CBQ\BA\03`\D8Y\02\043\E1\01\C3/\02\00\17\95\05\01\97Ra\03\8C\84\DC\00\D8\D0\F0\00)\EB\F3\01ZW\D6\00\FD:\91\01\A7\E4R\00\8F%\01\00f$\08\00\85\09s\00m\E5\D7\01\A2\1AJ\02 \BAj\01\FBXJ\00\CE\8C\BD\01\DC\C1\AA\034\AF\EA\02\96\8B\F7\00\14*\03\00\99x\AA\00\EB\0A\DC\02^\22\D8\00\C6b\05\00\AE\BB\EB\00E\97^\03\F0\E1\98\01\0A\CE\B7\00I\93\CC\03[\88l\02n\90\F7\01=\E2\8A\00\E1.\95\02m=\19\01\EB\B1\89\01\F2{\07\01m~'\01bAj\03\E9\08S\01\EE\C6D\01\99\13%\00\AF>$\01\BC7\A4\00LOX\01F\DEM\01\FAL\FC\03/\A36\01\F2|Y\011\AF-\01U\FB\E2\01\C5\F07\00\FEU\AD\01[zh\01>\C8H\03\C0W`\00\AE\82g\00\A155\00\DB8l\00\14\E0\A7\00,\BA\8F\01\CE\08\D2\02t\A8\A7\02\D9v\0C\010N\E5\00\D7G\F4\02\892\EB\013)L\00\C0\94\83\01\90!\C6\02\DFf?\00+\E6\ED\01\F3\11\03\00O\8D9\01k\BA\DA\00\92)>\00L-a\003\E7+\03\A3\E2]\03\17\AF\F3\00!\0B\86\01\D9\A4\F9\02K\DB\9F\02(\EF\AA\00\F8\D7\BE\01\E7v\97\030\86\F2\03\F49{\00\18\F5\BC\00\90q\B2\02$HK\00Y]\92\00\A7\CCX\00\C7~\D9\01w}F\02f\EE\EE\01Z\90q\00\81\8B\BC\03\0D\C1\DF\02I\0FQ\01Q\CC\C4\00\016A\01\E9\0D\0B\02\0B\7Fs\00i71\00\C7\AE\22\01\AF\8E\0B\03M\8F\F6\01CvY\01N\F2\F0\03\A0^\CF\02}\01\1E\01\F7+\80\01\01vt\02fN\C8\02[\88\E5\01\0D\7F\F7\01\E7]L\02\07;\9E\01;?\CE\01l\C8\FF\00A\92p\01\B9\D6\15\03gpl\01w'\CE\00\0AeL\03\E14\A6\03-\F7\B1\00\F8\07\D6\01\AE?\14\01\C0k\D7\00\F5\E4\B2\00\85\F5E\019\93\EA\03\02&\1E\02\CA\F6\CD\00\A1\84\FF\01\18\B5\CD\03\93$n\01\DBJ\B9\01IJn\01\BF\04\93\01J3.\02\1A\DF@\00\B5,\8F\01%\AF\00\01\D2\0E\F0\03!\225\00I\F8\E7\01$\F2\BC\02s:?\035Z\09\00\1E\B6y\00\02\AD\C5\02\989L\03\98{\88\00\E21\04\00\A2U\93\01\B4^5\03|_C\01\E6x6\00\D45?\01+\01\D6\03\A8\90\D3\01\C2\AE\06\01\14J6\01\A1\F4\AA\00\94\C7\1C\01.I\22\01\1F\CD\88\03\1F\925\03\CC'8\00v\A3\95\00\C9\098\03\F2\98\11\03~\D5\C6\01793\01\98\8C\E1\00\AAFY\01\EA\1F\9A\01'\E7\8A\01\F3e\D0\01\8F\E8\02\00d\93\CC\01@1\89\00W\AE\D6\03\87\97\D9\03\22\0A\0D\00/\8B\AE\01\9EU1\01\C9D\01\03`\98\95\00 -Z\01\F0E\E6\00\CF\AF\F0\01\D3\8F\86\00\10\C5@\009\03\92\02\161\D9\03\06=\06\00\D6\85\C9\00ER\FA\00\F7Q\99\03\F9{\E0\01!\A9?\01o\AA\A4\01\8A\0CO\02\E8\A0\7F\00\CC\FC\BD\00a8\F4\00\0C\22u\03:w\15\00\EF\12\95\01H\D1[\02\B5\11\\\0385\DD\01\06\17\88\00\D2\16c\01\1D\D6(\019\F2\A6\01\0E\9D\F3\01\\\93\03\00\BEL1\02\CB\DFX\01\A6\AC\DA\00y\0El\02\D1rV\01KtQ\01CUj\01\91 t\02T\EE\00\00\9E\BA\BE\00\B9E\08\00\D2\E2\BD\03U\07\F5\01>\18\09\01\EDA\06\01I\22?\0320L\01)\FA\F2\00\DFs\BA\01z%\8A\03:\8F\C2\03\81\C7\BF\00L\D6\81\00N\B4\90\00\16\BF\F5\00\96\D4W\00\06R\9A\01\9C\CA7\03\94\E9F\02\FD@T\00\BF\D5\22\01\17\C7\1C\01\05\C2\8A\00S\FE\A7\01\CC\E8\DB\01&#\ED\03\BA\D1\99\02O\C4\A9\01\8C\C7}\01\C1\9C\EB\03\E5\84E\02>\8DO\00^ON\01\C3\BBC\00\C6\B7\93\00^\D4\9B\00\18\B2H\00\E4\F5\C9\00k\C3x\03z65\011\CD@\01yH\A0\03\CF\9C\DF\02\\\C5\D9\01\8C\89G\00\D9\9D\BD\005\EB\90\03\18OT\01\89\A2\BA\01\83\11\01\03tp\C5\01\D8\0Eg\01a\AEs\00\17\C7\EC\02\A9\16j\00\9B\E2\E3\00\90f}\00\A6o\18\00u\F3.\02[\D8\E4\01\F2\0B\C4\01\C2|b\03\13!\7F\00\A5\ED`\01\B0\DE-\01\D7\1D\8C\03Vd\D8\03\0C\0B\1B\00\DA\FEV\00'\8CW\00cd\F6\00\0B_\90\00g\06W\00N\A7\F8\01\0A\8F<\03\121\B6\00\F7\F7\13\00#u\EE\00+@K\00B\04\B2\01\B6G?\01\E5\B7\14\01\1A\A56\01\BD\1CK\00{\D2\98\00\85\F4\EA\03\E0\CC\12\02e\85\90\01wx\BD\01\E2+\0C\00(\05\16\02\B8\0Bs\01\1E\1B\7F\01\E0\8Ew\019\A7H\009\92\E9\00\1Cs\EE\01\A0\C9\FB\00G)\9C\03\01\C3\90\00\B6&\8E\00\C6A}\01\18\06\E7\01\A8t<\00\FB,&\00|\BF\C6\03V\89\01\03\FEW\13\01\E1i\D2\01\9C[\81\02\A2[\DF\01x^\CE\00c\F8\F5\00\F6\EC;\00\A6\17f\03\1Da\8D\00$\E8I\01TE)\01\DA\16:\00`\F8z\01o[\DE\00\FB\93\A4\00\BE\85\C6\02=\9F\05\00\C8N\FA\01\A3,Q\00 \F1#\03f\0F\CF\01-H\C7\01\FC']\033F\DA\02\1C]p\01\D8\84S\01\C4\F8\84\03c\BCK\00u\9C\FE\01\DB\F9\05\01\EC\B1\EC\00\14&a\00\E0IH\00\84\D2\A5\01\89v\CE\01i\0C~\01o\AF\DE\00\8A\DE\C3\00\F1\B6\CE\03_\FF\06\02\90mY\00@\89n\00\F5K8\00\A7\EFe\03h\98\18\01\E7\D6\B0\00~qG\00\EE\EF)\02n\F8\09\00\13\87T\01'\DF\D6\00\C0QV\00\F81\A9\00\14\E6o\01\C3\EF`\02&\FE\BC\02\AF\C0{\01\D1\E2\17\01mg\0D\00\DFOi\02\8Ae\B7\00\13D\05\00f<\C3\00\F8\E2\B8\01Q(\90\00@\C1\AD\00\AB\D1\02\01D[\D4\00\A09\A6\00\16,\8B\01\12\A4\AD\02\09\D3/\03\84\AE6\00\FE\D1\10\00s\B86\030\9B\C8\03\D2\04%\00-\88\9E\00d\1C\B0\02\D0\A8=\02&\87'\01\97\195\01\A2\DF\9C\00\C9\94{\02\EA$\A6\01v\BC\05\00]\95\BB\02J0o\01\E4\D4\EF\01\0Cg\EB\01\C0\95\A3\00\94g\0B\03\1C\CC\13\00\81\88\C7\01\F3\B7\F3\03\CB<&\02\F2\AF\FB\00c\E4|\01K\AB\B6\00\1A\E6\F3\02\D0d~\015\F9\1D\00\81\8D\8C\01\9E\C6\A5\01\CD\16|\01\DF\9A\9F\01[\F1\F8\03\9AR%\03\91\A5\F9\00D\9B\9F\00\A1S\9E\02 \82\0C\02px\DC\01vb\86\00\86\9C\9E\00V\DD#\02\15p\82\01\9F\09'\01)\EA~\01\97\9C\0C\02\F1\F41\01\B9\A9\EC\01\C4 \B3\00\D1A6\03G\A8\D1\01\A4\E9\95\01\C2R\87\00.\C1\1F\02/\1C\F0\01\17\08\AF\01\ED\A5\18\03\98\05\D9\00w\F3$\01\91\F2b\01X\86\0D\03.]M\00\19\8F\A8\00j0Q\00\AF\05\A6\03\7Fd\08\021\9Cl\017\95b\00\C8\F6_\02\0F(\C2\02\08\17\9F\00\D8\00\87\01\CE!\F9\03s\B66\02\F3{\B9\01}\E6\C5\00Q\F8\8D\03\1F\B6e\02}\C2W\00p\A6\02\00\A1\EBy\03\F1K\0B\00\EF\8E\15\00?:u\00Z\E4\0E\00\BB7]\03\F4\91=\01\CBRY\01\90$\ED\02zd/\01\22\EC$\00@\B0\D9\01\BFC\F2\03PN]\02\DB\B7W\01!49\00\18\00\EF\03\B0\F0\0E\02N\FF{\00\1F\A2\17\01\ADA\D3\03\D0\B2;\00yH'\01\F7\CE\CA\01'\EC\DB\01\F3\97q\01\98\B6\F9\01\AE\E7\B5\01\18\C6\12\02m\B6>\009\02;\00\C2k*\01\00< \00r4\F3\01\E5\9Av\01\08<\FD\00\E9V\1E\02+\CD\DC\02w\B5\A6\00\B1\0E\E1\01G\E5\F7\03=\D9a\01\DD\18\CC\00\B7y\1A\006\F0\8E\03\0D)\9D\02\C7t\C6\017\12z\01\F4\13+\01\ED2a\02P3,\00\B9v\16\00\18p\\\036\06%\02v+\FA\01\E0\E8\14\00X\BFi\01\A5\BEo\03\DD\CBw\00\A8\19\C1\004\85I\02\92Ng\03d\7Fk\00&I\C2\00\D9\ECm\03A6\\\00\A2\DE\D6\01 \08\A7\00\EC\CA@\01\B0\00j\00\FC\E1\92\01\7F\B6l\01\C7\AB \02/\ADe\01\F3\B0H\00\9Aec\00\01Z\B5\01\C3\02\D8\012\B4\8E\00\8D$\92\01\83\B6:\02\D8\FD/\00\F1\D2\85\00q\06\08\00n6F\03\18\EF/\02\C3\132\00N\8EH\00\DE\9C_\01\0Bg\F4\01FS\EE\00\EC$h\01-\8B\97\00\B41\C8\01a\DA%\00\A5*q\01\0F\88w\00\8B\DD\22\00\E6\A3\0D\00:\CD\CC\00\A3\B2]\01\A7\0AQ\01\B3+\BA\01\AF\0B.\01n\CD\9B\03\DE\E8\C7\01\A3\D7\D9\01\90\8F\8A\00`Pi\01\DB\CD!\03\D4\BA\B1\01\A4\0D;\019+=\00\15R\AF\01\09\C6\C5\00g?\18\00\C2\A2P\03\91\16\97\01\F9\DA\E4\00\9D#c\01\BA\84A\03\A8\A1\C1\02\FA\D2\B4\01\09\02\F8\01\A2\E4\AF\00\07ib\00\17\D7\94\01*\FE4\00\D8\DFy\02BQ\BB\03\A2\14/\01\F3\CA9\01\1D(\F5\01[\B3\EC\02`\BE\B1\01\D7\DF)\01\09\82\E8\02\BE \E0\02\BB\F9\A1\01\B2\0C\C9\00\C1\F6\F6\00\F5\FC\AA\03\99/-\00\DA\C5\16\00KY\7F\01\FA9/\00~\B5\E6\01O\E8\F8\01}\FA\DB\03S\CB\17\01\F7\1B\FC\00\88\F9\83\01\A5\CA\EA\03\FFw\1D\02\E37\D2\01\DE\BA\9B\00\B6\A8\\\02\85:W\02j\8E\FA\00\C0\EF\95\00\8D\E0]\03\15\F1\9D\01\EB\BA9\00\86\DB\CB\002\E0\D5\01\F8\DB\FA\03L\15\07\01\DD*d\00\F5Y\A4\03\CC_\C9\01\E8)\EE\01*\82\89\00FI\AC\01\CC\00\B5\00o\8F\DA\00\C9\E9\BC\00a\D6\1A\03\80\95\F4\00\CD\C4u\01\D1\ADF\01\05\8E\8A\03\C4kl\03{u\B2\00\A9Z\0C\01\BB\CD\F5\00\15\FB\96\02\92\84\DA\01\1CX_\00\7F\CE\84\02\1B\E1\AB\03u6\BF\01\BD-\B3\00)\C6\90\02R\B0\A1\01\01I\CC\01\05\A0N\01\15\86\F9\02q\CB\92\00Q\FCM\01Z%@\01]\E6Z\03[]\AB\03\8E\F3\FA\01\EE\A96\00)\EAm\03\98\A9q\02\A0\EBP\014\B3\DC\00\E5\BB\E7\03\11\9C\14\01\AF\DEs\01\B8\9D\FC\01\94\14\F9\03\DF\1Db\00\E62\07\00\99N\B6\000\DD\D2\01\E3^ \01a\15\F3\00\8BD@\00\22\1Cg\00\CE\C5\E6\03\90I\CF\00}_\AD\00G\C0\A4\00\8F\19u\01z-*\01\FB9\BF\01\DC\D8g\02!\DA\0D\01\A5\A2\17\01\F7\B2:\00\B5\F1\D0\00\07\0F\C2\03\C7\C2\E6\01\E7\D3d\01~f \03\1F\96m\03o/R\01\02p\9D\01\A6\BD\E5\02\90\02\F6\03]h\B8\00\0C-\92\01\92,Q\01\E0\98\D6\00rRf\00\F6\DA\DA\00\B16\F1\03\99\E3;\01\F2G\DD\01A`r\00\C6}\A1\01\15|\F0\02?{\1E\01\C4\0Bm\00\E8\955\02\E1\F1\80\02\BC\F2U\01\1E\97\A0\00\A3\D9\16\00\F1^\F8\01\A2\A9\B4\00,,-\00_\91j\02\BA' \01\C4\C1}\01\F2)>\00\A1]?\03\9F\E7\99\02\C1\D9*\004\05<\01\DA\EB_\02\98a\9F\01\F8cL\01J\CB\B4\00uR\BA\02k{\DF\02K\E4\8D\00\FFS\8F\00\8CH\13\02\B3\00X\03A$\CF\00\FB\A0@\01\D4\15A\00\02B\F5\02\1A\DD|\01\F2\D2\8F\00\83\A5\DA\02\D4\AF*\00\86\DD\B4\00\91\14]\01-\98}\01O\9B\D3\03\8F\CC\05\00O\BE\B8\00\E8!\BC\00\9F\CC\B5\00y\A9\0B\00\DA\FC\C4\01F\A2#\02:\AC_\019b=\00\E5\13k\00f\FEn\00S\8A-\03\90\FF~\01T\9F\E9\00\D3\1D\87\02\9A\E2\CD\01\AD\1Fh\00\98o\E1\01\991l\02\CF\8D\F6\03\B9\FD\12\01\A7~\F2\01\BE\B6_\02R\84\9A\02\0C\CB\AF\01U\1D5\01\F6\9F\8D\01\A6E#\03{TS\01\A5\F8J\01B\DB\9F\03[\07\0B\01\86h\CA\01x>\BF\012\C7\DF\02\CEr\C0\01Bt\84\00\E5I\10\01\A0vb\00\C9\B7\FC\02\8Fr\91\00^B\99\01?c\A7\02\0Dz\01\039>N\010b\C0\00", align 32

; Function Attrs: nounwind nonlazybind uwtable
define hidden fastcc void @_RNvNvNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector10scalar_mul19vartime_double_base9spec_avx23mul9__impl_mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(160) %_0, ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32) %a, ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(160) %A, ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32) %b) unnamed_addr #0 personality ptr @rust_eh_personality {
start:
  %t1.i187 = alloca [160 x i8], align 32
  %t0.i188 = alloca [160 x i8], align 32
  %_8.i189 = alloca [160 x i8], align 32
  %tmp.i190 = alloca [160 x i8], align 32
  %t1.i.i74 = alloca [160 x i8], align 32
  %t0.i.i75 = alloca [160 x i8], align 32
  %_8.i.i76 = alloca [160 x i8], align 32
  %tmp.i.i77 = alloca [160 x i8], align 32
  %_4.i78 = alloca [160 x i8], align 32
  %t1.i = alloca [160 x i8], align 32
  %t0.i = alloca [160 x i8], align 32
  %_8.i = alloca [160 x i8], align 32
  %tmp.i = alloca [160 x i8], align 32
  %t1.i.i = alloca [160 x i8], align 32
  %t0.i.i = alloca [160 x i8], align 32
  %_8.i.i = alloca [160 x i8], align 32
  %tmp.i.i = alloca [160 x i8], align 32
  %_4.i = alloca [160 x i8], align 32
  %tmp1.i = alloca [160 x i8], align 32
  %tmp0.i = alloca [160 x i8], align 32
  %x_u64.i18 = alloca [40 x i8], align 8
  %x_u64.i = alloca [40 x i8], align 8
  %_60 = alloca [160 x i8], align 32
  %_52 = alloca [160 x i8], align 32
  %_37 = alloca [160 x i8], align 32
  %_28 = alloca [160 x i8], align 32
  %_21 = alloca [160 x i8], align 32
  %table_A = alloca [1280 x i8], align 32
  %b_naf = alloca [256 x i8], align 1
  %a_naf = alloca [256 x i8], align 1
  call void @llvm.lifetime.start.p0(ptr nonnull %a_naf)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !4)
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(256) %a_naf, i8 0, i64 256, i1 false), !alias.scope !4, !noalias !7
  call void @llvm.lifetime.start.p0(ptr nonnull %x_u64.i), !noalias !9
  %0 = getelementptr inbounds nuw i8, ptr %x_u64.i, i64 32
  store i64 0, ptr %0, align 8, !noalias !9
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(32) %x_u64.i, ptr noundef nonnull readonly align 1 dereferenceable(32) %a, i64 32, i1 false), !alias.scope !10, !noalias !4
  br label %bb3.lr.ph.i

bb3.lr.ph.i:                                      ; preds = %bb11.i, %start
  %pos.sroa.0.0.ph17.i = phi i64 [ 0, %start ], [ %10, %bb11.i ]
  %carry.sroa.0.0.ph16.i = phi i64 [ 0, %start ], [ %carry.sroa.0.1.i, %bb11.i ]
  br label %bb3.i

bb3.i:                                            ; preds = %bb10.i, %bb3.lr.ph.i
  %pos.sroa.0.015.i = phi i64 [ %pos.sroa.0.0.ph17.i, %bb3.lr.ph.i ], [ %7, %bb10.i ]
  %u64_idx11.i = lshr i64 %pos.sroa.0.015.i, 6
  %bit_idx.i = and i64 %pos.sroa.0.015.i, 63
  %_20.i = icmp samesign ult i64 %bit_idx.i, 59
  %1 = getelementptr inbounds nuw i64, ptr %x_u64.i, i64 %u64_idx11.i
  %_22.i = load i64, ptr %1, align 8, !noalias !9, !noundef !14
  %2 = lshr i64 %_22.i, %bit_idx.i
  br i1 %_20.i, label %bb9.i, label %bb8.i

bb8.i:                                            ; preds = %bb3.i
  %3 = getelementptr inbounds nuw i8, ptr %1, i64 8
  %_28.i = load i64, ptr %3, align 8, !noalias !9, !noundef !14
  %_31.i = sub nsw i64 0, %pos.sroa.0.015.i
  %4 = and i64 %_31.i, 63
  %_27.i = shl i64 %_28.i, %4
  %5 = or i64 %_27.i, %2
  br label %bb9.i

bb9.i:                                            ; preds = %bb8.i, %bb3.i
  %bit_buf.sroa.0.0.i = phi i64 [ %5, %bb8.i ], [ %2, %bb3.i ]
  %_34.i = and i64 %bit_buf.sroa.0.0.i, 31
  %window.i = add nuw nsw i64 %_34.i, %carry.sroa.0.0.ph16.i
  %_35.i = and i64 %window.i, 1
  %6 = icmp eq i64 %_35.i, 0
  br i1 %6, label %bb10.i, label %bb11.i

bb10.i:                                           ; preds = %bb9.i
  %7 = add nuw nsw i64 %pos.sroa.0.015.i, 1
  %exitcond.not.i = icmp eq i64 %7, 256
  br i1 %exitcond.not.i, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit, label %bb3.i

bb11.i:                                           ; preds = %bb9.i
  %_36.i = icmp samesign ugt i64 %window.i, 15
  %8 = trunc nuw nsw i64 %window.i to i8
  %_40.i.neg = select i1 %_36.i, i8 -32, i8 0
  %_40.sink.i = add nsw i8 %_40.i.neg, %8
  %carry.sroa.0.1.i = zext i1 %_36.i to i64
  %9 = getelementptr inbounds nuw i8, ptr %a_naf, i64 %pos.sroa.0.015.i
  store i8 %_40.sink.i, ptr %9, align 1, !alias.scope !4, !noalias !7
  %10 = add nuw nsw i64 %pos.sroa.0.015.i, 5
  %_1314.i = icmp ult i64 %pos.sroa.0.015.i, 251
  br i1 %_1314.i, label %bb3.lr.ph.i, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit

_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit: ; preds = %bb11.i, %bb10.i
  call void @llvm.lifetime.end.p0(ptr nonnull %x_u64.i), !noalias !9
  call void @llvm.lifetime.start.p0(ptr nonnull %b_naf)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !15)
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 1 dereferenceable(256) %b_naf, i8 0, i64 256, i1 false), !alias.scope !15, !noalias !18
  call void @llvm.lifetime.start.p0(ptr nonnull %x_u64.i18), !noalias !20
  %11 = getelementptr inbounds nuw i8, ptr %x_u64.i18, i64 32
  store i64 0, ptr %11, align 8, !noalias !20
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(32) %x_u64.i18, ptr noundef nonnull readonly align 1 dereferenceable(32) %b, i64 32, i1 false), !alias.scope !21, !noalias !15
  br label %bb3.lr.ph.i19

bb3.lr.ph.i19:                                    ; preds = %bb11.i37, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit
  %pos.sroa.0.0.ph17.i20 = phi i64 [ 0, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit ], [ %21, %bb11.i37 ]
  %carry.sroa.0.0.ph16.i21 = phi i64 [ 0, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit ], [ %carry.sroa.0.1.i41, %bb11.i37 ]
  br label %bb3.i22

bb3.i22:                                          ; preds = %bb10.i43, %bb3.lr.ph.i19
  %pos.sroa.0.015.i23 = phi i64 [ %pos.sroa.0.0.ph17.i20, %bb3.lr.ph.i19 ], [ %18, %bb10.i43 ]
  %u64_idx11.i24 = lshr i64 %pos.sroa.0.015.i23, 6
  %bit_idx.i25 = and i64 %pos.sroa.0.015.i23, 63
  %_20.i26 = icmp samesign ult i64 %bit_idx.i25, 56
  %12 = getelementptr inbounds nuw i64, ptr %x_u64.i18, i64 %u64_idx11.i24
  %_22.i27 = load i64, ptr %12, align 8, !noalias !20, !noundef !14
  %13 = lshr i64 %_22.i27, %bit_idx.i25
  br i1 %_20.i26, label %bb9.i32, label %bb8.i28

bb8.i28:                                          ; preds = %bb3.i22
  %14 = getelementptr inbounds nuw i8, ptr %12, i64 8
  %_28.i29 = load i64, ptr %14, align 8, !noalias !20, !noundef !14
  %_31.i30 = sub nsw i64 0, %pos.sroa.0.015.i23
  %15 = and i64 %_31.i30, 63
  %_27.i31 = shl i64 %_28.i29, %15
  %16 = or i64 %_27.i31, %13
  br label %bb9.i32

bb9.i32:                                          ; preds = %bb8.i28, %bb3.i22
  %bit_buf.sroa.0.0.i33 = phi i64 [ %16, %bb8.i28 ], [ %13, %bb3.i22 ]
  %_34.i34 = and i64 %bit_buf.sroa.0.0.i33, 255
  %window.i35 = add nuw nsw i64 %_34.i34, %carry.sroa.0.0.ph16.i21
  %_35.i36 = and i64 %window.i35, 1
  %17 = icmp eq i64 %_35.i36, 0
  br i1 %17, label %bb10.i43, label %bb11.i37

bb10.i43:                                         ; preds = %bb9.i32
  %18 = add nuw nsw i64 %pos.sroa.0.015.i23, 1
  %exitcond.not.i44 = icmp eq i64 %18, 256
  br i1 %exitcond.not.i44, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit45, label %bb3.i22

bb11.i37:                                         ; preds = %bb9.i32
  %_36.i38 = icmp samesign ugt i64 %window.i35, 127
  %19 = trunc i64 %window.i35 to i8
  %carry.sroa.0.1.i41 = zext i1 %_36.i38 to i64
  %20 = getelementptr inbounds nuw i8, ptr %b_naf, i64 %pos.sroa.0.015.i23
  store i8 %19, ptr %20, align 1, !alias.scope !15, !noalias !18
  %21 = add nuw nsw i64 %pos.sroa.0.015.i23, 8
  %_1314.i42 = icmp ult i64 %pos.sroa.0.015.i23, 248
  br i1 %_1314.i42, label %bb3.lr.ph.i19, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit45

_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit45: ; preds = %bb11.i37, %bb10.i43
  call void @llvm.lifetime.end.p0(ptr nonnull %x_u64.i18), !noalias !20
  br label %bb9

bb16:                                             ; preds = %bb12, %bb9
  call void @llvm.lifetime.start.p0(ptr nonnull %table_A)
  call void @_RNvXNvXsk_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsINtNtBg_6window15NafLookupTable5NtB8_11CachedPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtBg_7edwards12EdwardsPointE4fromB1c_NtB2_13___Impl_from__10__impl_from(ptr noalias nofree noundef nonnull sret([1280 x i8]) align 32 captures(none) dereferenceable(1280) %table_A, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %A) #11
  %_3.sroa.4.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %tmp0.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i8.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i9.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i10.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i11.i = getelementptr inbounds nuw i8, ptr %tmp1.i, i64 128
  %Q.sroa.14.0._21.sroa_idx = getelementptr inbounds nuw i8, ptr %_21, i64 32
  %Q.sroa.15.0._21.sroa_idx = getelementptr inbounds nuw i8, ptr %_21, i64 64
  %Q.sroa.16.0._21.sroa_idx = getelementptr inbounds nuw i8, ptr %_21, i64 96
  %Q.sroa.17.0._21.sroa_idx = getelementptr inbounds nuw i8, ptr %_21, i64 128
  %Q.sroa.14.0.tmp.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i, i64 32
  %Q.sroa.15.0.tmp.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i, i64 64
  %Q.sroa.16.0.tmp.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i, i64 96
  %Q.sroa.17.0.tmp.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i38.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i39.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i40.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i41.i = getelementptr inbounds nuw i8, ptr %t0.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i49.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i50.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i51.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i52.i = getelementptr inbounds nuw i8, ptr %t1.i, i64 128
  %Q.sroa.14.0._28.sroa_idx = getelementptr inbounds nuw i8, ptr %_28, i64 32
  %Q.sroa.15.0._28.sroa_idx = getelementptr inbounds nuw i8, ptr %_28, i64 64
  %Q.sroa.16.0._28.sroa_idx = getelementptr inbounds nuw i8, ptr %_28, i64 96
  %Q.sroa.17.0._28.sroa_idx = getelementptr inbounds nuw i8, ptr %_28, i64 128
  %_4.sroa.4.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %_4.i, i64 32
  %_4.sroa.5.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %_4.i, i64 64
  %_4.sroa.6.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %_4.i, i64 96
  %_4.sroa.7.0._0.sroa_idx.i.i = getelementptr inbounds nuw i8, ptr %_4.i, i64 128
  %Q.sroa.14.0.tmp.i.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i, i64 32
  %Q.sroa.15.0.tmp.i.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i, i64 64
  %Q.sroa.16.0.tmp.i.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i, i64 96
  %Q.sroa.17.0.tmp.i.i.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i38.i.i = getelementptr inbounds nuw i8, ptr %t0.i.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i39.i.i = getelementptr inbounds nuw i8, ptr %t0.i.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i40.i.i = getelementptr inbounds nuw i8, ptr %t0.i.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i41.i.i = getelementptr inbounds nuw i8, ptr %t0.i.i, i64 128
  %_3.sroa.4.0._0.sroa_idx.i49.i.i = getelementptr inbounds nuw i8, ptr %t1.i.i, i64 32
  %_3.sroa.5.0._0.sroa_idx.i50.i.i = getelementptr inbounds nuw i8, ptr %t1.i.i, i64 64
  %_3.sroa.6.0._0.sroa_idx.i51.i.i = getelementptr inbounds nuw i8, ptr %t1.i.i, i64 96
  %_3.sroa.7.0._0.sroa_idx.i52.i.i = getelementptr inbounds nuw i8, ptr %t1.i.i, i64 128
  %Q.sroa.14.0._37.sroa_idx = getelementptr inbounds nuw i8, ptr %_37, i64 32
  %Q.sroa.15.0._37.sroa_idx = getelementptr inbounds nuw i8, ptr %_37, i64 64
  %Q.sroa.16.0._37.sroa_idx = getelementptr inbounds nuw i8, ptr %_37, i64 96
  %Q.sroa.17.0._37.sroa_idx = getelementptr inbounds nuw i8, ptr %_37, i64 128
  %Q.sroa.14.0.tmp.i190.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i190, i64 32
  %Q.sroa.15.0.tmp.i190.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i190, i64 64
  %Q.sroa.16.0.tmp.i190.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i190, i64 96
  %Q.sroa.17.0.tmp.i190.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i190, i64 128
  %_3.sroa.4.0._0.sroa_idx.i38.i257 = getelementptr inbounds nuw i8, ptr %t0.i188, i64 32
  %_3.sroa.5.0._0.sroa_idx.i39.i258 = getelementptr inbounds nuw i8, ptr %t0.i188, i64 64
  %_3.sroa.6.0._0.sroa_idx.i40.i259 = getelementptr inbounds nuw i8, ptr %t0.i188, i64 96
  %_3.sroa.7.0._0.sroa_idx.i41.i260 = getelementptr inbounds nuw i8, ptr %t0.i188, i64 128
  %_3.sroa.4.0._0.sroa_idx.i49.i266 = getelementptr inbounds nuw i8, ptr %t1.i187, i64 32
  %_3.sroa.5.0._0.sroa_idx.i50.i267 = getelementptr inbounds nuw i8, ptr %t1.i187, i64 64
  %_3.sroa.6.0._0.sroa_idx.i51.i268 = getelementptr inbounds nuw i8, ptr %t1.i187, i64 96
  %_3.sroa.7.0._0.sroa_idx.i52.i269 = getelementptr inbounds nuw i8, ptr %t1.i187, i64 128
  %Q.sroa.14.0._52.sroa_idx = getelementptr inbounds nuw i8, ptr %_52, i64 32
  %Q.sroa.15.0._52.sroa_idx = getelementptr inbounds nuw i8, ptr %_52, i64 64
  %Q.sroa.16.0._52.sroa_idx = getelementptr inbounds nuw i8, ptr %_52, i64 96
  %Q.sroa.17.0._52.sroa_idx = getelementptr inbounds nuw i8, ptr %_52, i64 128
  %_4.sroa.4.0._0.sroa_idx.i.i100 = getelementptr inbounds nuw i8, ptr %_4.i78, i64 32
  %_4.sroa.5.0._0.sroa_idx.i.i101 = getelementptr inbounds nuw i8, ptr %_4.i78, i64 64
  %_4.sroa.6.0._0.sroa_idx.i.i102 = getelementptr inbounds nuw i8, ptr %_4.i78, i64 96
  %_4.sroa.7.0._0.sroa_idx.i.i103 = getelementptr inbounds nuw i8, ptr %_4.i78, i64 128
  %Q.sroa.14.0.tmp.i.i77.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i77, i64 32
  %Q.sroa.15.0.tmp.i.i77.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i77, i64 64
  %Q.sroa.16.0.tmp.i.i77.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i77, i64 96
  %Q.sroa.17.0.tmp.i.i77.sroa_idx = getelementptr inbounds nuw i8, ptr %tmp.i.i77, i64 128
  %_3.sroa.4.0._0.sroa_idx.i38.i.i170 = getelementptr inbounds nuw i8, ptr %t0.i.i75, i64 32
  %_3.sroa.5.0._0.sroa_idx.i39.i.i171 = getelementptr inbounds nuw i8, ptr %t0.i.i75, i64 64
  %_3.sroa.6.0._0.sroa_idx.i40.i.i172 = getelementptr inbounds nuw i8, ptr %t0.i.i75, i64 96
  %_3.sroa.7.0._0.sroa_idx.i41.i.i173 = getelementptr inbounds nuw i8, ptr %t0.i.i75, i64 128
  %_3.sroa.4.0._0.sroa_idx.i49.i.i179 = getelementptr inbounds nuw i8, ptr %t1.i.i74, i64 32
  %_3.sroa.5.0._0.sroa_idx.i50.i.i180 = getelementptr inbounds nuw i8, ptr %t1.i.i74, i64 64
  %_3.sroa.6.0._0.sroa_idx.i51.i.i181 = getelementptr inbounds nuw i8, ptr %t1.i.i74, i64 96
  %_3.sroa.7.0._0.sroa_idx.i52.i.i182 = getelementptr inbounds nuw i8, ptr %t1.i.i74, i64 128
  %Q.sroa.14.0._60.sroa_idx = getelementptr inbounds nuw i8, ptr %_60, i64 32
  %Q.sroa.15.0._60.sroa_idx = getelementptr inbounds nuw i8, ptr %_60, i64 64
  %Q.sroa.16.0._60.sroa_idx = getelementptr inbounds nuw i8, ptr %_60, i64 96
  %Q.sroa.17.0._60.sroa_idx = getelementptr inbounds nuw i8, ptr %_60, i64 128
  br label %bb18

bb9:                                              ; preds = %bb12, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit45
  %iter.sroa.4.0331 = phi i64 [ 256, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit45 ], [ %_0.i1.i.i.i, %bb12 ]
  %_0.i1.i.i.i = add nsw i64 %iter.sroa.4.0331, -1
  %22 = getelementptr inbounds nuw i8, ptr %a_naf, i64 %_0.i1.i.i.i
  %_13 = load i8, ptr %22, align 1, !noundef !14
  %23 = icmp eq i8 %_13, 0
  br i1 %23, label %bb12, label %bb16

bb12:                                             ; preds = %bb9
  %24 = getelementptr inbounds nuw i8, ptr %b_naf, i64 %_0.i1.i.i.i
  %_16 = load i8, ptr %24, align 1, !noundef !14
  %25 = icmp ne i8 %_16, 0
  %_0.i.i.i.i.not = icmp eq i64 %_0.i1.i.i.i, 0
  %or.cond = or i1 %25, %_0.i.i.i.i.not
  br i1 %or.cond, label %bb16, label %bb9

bb18:                                             ; preds = %bb41, %bb16
  %Q.sroa.16.0 = phi <8 x i32> [ zeroinitializer, %bb16 ], [ %Q.sroa.16.2, %bb41 ]
  %Q.sroa.15.0 = phi <8 x i32> [ zeroinitializer, %bb16 ], [ %Q.sroa.15.2, %bb41 ]
  %Q.sroa.14.0 = phi <8 x i32> [ zeroinitializer, %bb16 ], [ %Q.sroa.14.2, %bb41 ]
  %Q.sroa.0.0 = phi <8 x i32> [ <i32 0, i32 1, i32 0, i32 0, i32 1, i32 0, i32 0, i32 0>, %bb16 ], [ %Q.sroa.0.2, %bb41 ]
  %Q.sroa.17.0 = phi <8 x i32> [ zeroinitializer, %bb16 ], [ %Q.sroa.17.2, %bb41 ]
  %i.sroa.0.2 = phi i64 [ %_0.i1.i.i.i, %bb16 ], [ %30, %bb41 ]
  call void @llvm.lifetime.start.p0(ptr nonnull %_21)
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp0.i), !noalias !25
  %_3.i214.i.i = shufflevector <8 x i32> %Q.sroa.0.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i74266.i.i = shufflevector <8 x i32> %Q.sroa.14.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i75320.i.i = shufflevector <8 x i32> %Q.sroa.15.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i76374.i.i = shufflevector <8 x i32> %Q.sroa.16.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  %_3.i77.i.i = shufflevector <8 x i32> %Q.sroa.17.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 1, i32 poison, i32 3>
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp1.i), !noalias !25
  %_3.i219.i.i = shufflevector <8 x i32> %Q.sroa.0.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i74272.i.i = shufflevector <8 x i32> %Q.sroa.14.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i75326.i.i = shufflevector <8 x i32> %Q.sroa.15.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i76380.i.i = shufflevector <8 x i32> %Q.sroa.16.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_3.i77.i7.i = shufflevector <8 x i32> %Q.sroa.17.0, <8 x i32> poison, <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 0, i32 poison, i32 2>
  %_6.i.i.i = add <8 x i32> %_3.i219.i.i, %_3.i214.i.i
  %_6.i10.i.i = add <8 x i32> %_3.i74272.i.i, %_3.i74266.i.i
  %_6.i11.i.i = add <8 x i32> %_3.i75326.i.i, %_3.i75320.i.i
  %_6.i12.i.i = add <8 x i32> %_3.i76380.i.i, %_3.i76374.i.i
  %_6.i13.i.i = add <8 x i32> %_3.i77.i7.i, %_3.i77.i.i
  %r.i190.i.i = shufflevector <8 x i32> %Q.sroa.0.0, <8 x i32> %_6.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i.i = shufflevector <8 x i32> %Q.sroa.14.0, <8 x i32> %_6.i10.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i.i = shufflevector <8 x i32> %Q.sroa.15.0, <8 x i32> %_6.i11.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i.i = shufflevector <8 x i32> %Q.sroa.16.0, <8 x i32> %_6.i12.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i.i = shufflevector <8 x i32> %Q.sroa.17.0, <8 x i32> %_6.i13.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  store <8 x i32> %r.i190.i.i, ptr %tmp0.i, align 32, !noalias !25
  store <8 x i32> %r.i197.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i.i, align 32, !noalias !25
  store <8 x i32> %r.i204.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i.i, align 32, !noalias !25
  store <8 x i32> %r.i211.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i.i, align 32, !noalias !25
  store <8 x i32> %r.i218.i.i, ptr %_3.sroa.7.0._0.sroa_idx.i.i, align 32, !noalias !25
  call void @_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D(ptr noalias nofree noundef nonnull sret([160 x i8]) align 32 captures(address) dereferenceable(160) %tmp1.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp0.i) #11, !noalias !25
  %_5423.i16.i = load <8 x i32>, ptr %tmp1.i, align 32, !alias.scope !29, !noalias !32
  %_7184416.i17.i = load <8 x i32>, ptr %_3.sroa.4.0._0.sroa_idx.i8.i, align 32, !alias.scope !29, !noalias !32
  %_9230417.i18.i = load <8 x i32>, ptr %_3.sroa.5.0._0.sroa_idx.i9.i, align 32, !alias.scope !29, !noalias !32
  %_11284418.i19.i = load <8 x i32>, ptr %_3.sroa.6.0._0.sroa_idx.i10.i, align 32, !alias.scope !29, !noalias !32
  %_3.i183.i.i = shufflevector <8 x i32> %_5423.i16.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i74229.i.i = shufflevector <8 x i32> %_7184416.i17.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i75283.i.i = shufflevector <8 x i32> %_9230417.i18.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i76337.i.i = shufflevector <8 x i32> %_11284418.i19.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_13339419.i21.i = load <8 x i32>, ptr %_3.sroa.7.0._0.sroa_idx.i11.i, align 32, !alias.scope !29, !noalias !32
  %_3.i77.i22.i = shufflevector <8 x i32> %_13339419.i21.i, <8 x i32> poison, <8 x i32> <i32 0, i32 0, i32 2, i32 2, i32 0, i32 0, i32 2, i32 2>
  %_3.i189.i.i = shufflevector <8 x i32> %_5423.i16.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i74236.i.i = shufflevector <8 x i32> %_7184416.i17.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i75290.i.i = shufflevector <8 x i32> %_9230417.i18.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i76344.i.i = shufflevector <8 x i32> %_11284418.i19.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_3.i77.i33.i = shufflevector <8 x i32> %_13339419.i21.i, <8 x i32> poison, <8 x i32> <i32 1, i32 1, i32 3, i32 3, i32 1, i32 1, i32 3, i32 3>
  %_6.i.i40.i = shl <8 x i32> %_5423.i16.i, splat (i32 1)
  %_6.i10.i43.i = shl <8 x i32> %_7184416.i17.i, splat (i32 1)
  %_6.i11.i46.i = shl <8 x i32> %_9230417.i18.i, splat (i32 1)
  %_6.i12.i49.i = shl <8 x i32> %_11284418.i19.i, splat (i32 1)
  %_6.i13.i52.i = shl <8 x i32> %_13339419.i21.i, splat (i32 1)
  %r.i.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i.i40.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i196.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i10.i43.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i203.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i11.i46.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i210.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i12.i49.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i217.i.i = shufflevector <8 x i32> <i32 0, i32 0, i32 0, i32 0, i32 poison, i32 poison, i32 poison, i32 poison>, <8 x i32> %_6.i13.i52.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 poison, i32 14, i32 poison>
  %r.i190.i81.i = shufflevector <8 x i32> %r.i.i.i, <8 x i32> %_5423.i16.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i82.i = shufflevector <8 x i32> %r.i196.i.i, <8 x i32> %_7184416.i17.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i83.i = shufflevector <8 x i32> %r.i203.i.i, <8 x i32> %_9230417.i18.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i84.i = shufflevector <8 x i32> %r.i210.i.i, <8 x i32> %_11284418.i19.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i85.i = shufflevector <8 x i32> %r.i217.i.i, <8 x i32> %_13339419.i21.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i194.i.i = shufflevector <8 x i32> %_3.i189.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i201.i.i = shufflevector <8 x i32> %_3.i74236.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i208.i.i = shufflevector <8 x i32> %_3.i75290.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i215.i.i = shufflevector <8 x i32> %_3.i76344.i.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i222.i.i = shufflevector <8 x i32> %_3.i77.i33.i, <8 x i32> <i32 poison, i32 0, i32 poison, i32 0, i32 0, i32 poison, i32 0, i32 poison>, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %_6.i.i142.i = sub <8 x i32> <i32 poison, i32 134217690, i32 poison, i32 67108862, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i189.i.i
  %_6.i10.i143.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74236.i.i
  %_6.i11.i144.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75290.i.i
  %_6.i12.i145.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76344.i.i
  %_6.i13.i146.i = sub <8 x i32> <i32 poison, i32 134217726, i32 poison, i32 67108862, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i33.i
  %r.i195.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i.i142.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i202.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i10.i143.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i209.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i11.i144.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i216.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i12.i145.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %r.i223.i.i = shufflevector <8 x i32> <i32 0, i32 poison, i32 0, i32 poison, i32 poison, i32 0, i32 poison, i32 0>, <8 x i32> %_6.i13.i146.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 12, i32 5, i32 14, i32 7>
  %_6.i.i92.i = add <8 x i32> %r.i194.i.i, %_3.i183.i.i
  %_6.i.i125.i = add <8 x i32> %_6.i.i92.i, %r.i190.i81.i
  %_6.i.i163.i = add <8 x i32> %_6.i.i125.i, %r.i195.i.i
  %_6.i10.i95.i = add <8 x i32> %r.i201.i.i, %_3.i74229.i.i
  %_6.i10.i128.i = add <8 x i32> %_6.i10.i95.i, %r.i197.i82.i
  %_6.i10.i166.i = add <8 x i32> %_6.i10.i128.i, %r.i202.i.i
  %_6.i11.i98.i = add <8 x i32> %r.i208.i.i, %_3.i75283.i.i
  %_6.i11.i131.i = add <8 x i32> %_6.i11.i98.i, %r.i204.i83.i
  %_6.i11.i169.i = add <8 x i32> %_6.i11.i131.i, %r.i209.i.i
  %_6.i12.i101.i = add <8 x i32> %r.i215.i.i, %_3.i76337.i.i
  %_6.i12.i134.i = add <8 x i32> %_6.i12.i101.i, %r.i211.i84.i
  %_6.i12.i172.i = add <8 x i32> %_6.i12.i134.i, %r.i216.i.i
  %_6.i13.i104.i = add <8 x i32> %r.i222.i.i, %_3.i77.i22.i
  %_6.i13.i137.i = add <8 x i32> %_6.i13.i104.i, %r.i218.i85.i
  %_6.i13.i175.i = add <8 x i32> %_6.i13.i137.i, %r.i223.i.i
  %_3.i199.i.i = shufflevector <8 x i32> %_6.i.i163.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i74248.i.i = shufflevector <8 x i32> %_6.i10.i166.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i75302.i.i = shufflevector <8 x i32> %_6.i11.i169.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i76356.i.i = shufflevector <8 x i32> %_6.i12.i172.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  %_3.i77.i186.i = shufflevector <8 x i32> %_6.i13.i175.i, <8 x i32> poison, <8 x i32> <i32 5, i32 1, i32 7, i32 3, i32 1, i32 5, i32 3, i32 7>
  store <8 x i32> %_3.i199.i.i, ptr %tmp1.i, align 32, !noalias !25
  store <8 x i32> %_3.i74248.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i8.i, align 32, !noalias !25
  store <8 x i32> %_3.i75302.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i9.i, align 32, !noalias !25
  store <8 x i32> %_3.i76356.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i10.i, align 32, !noalias !25
  store <8 x i32> %_3.i77.i186.i, ptr %_3.sroa.7.0._0.sroa_idx.i11.i, align 32, !noalias !25
  %_3.i194.i.i = shufflevector <8 x i32> %_6.i.i163.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i74242.i.i = shufflevector <8 x i32> %_6.i10.i166.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i75296.i.i = shufflevector <8 x i32> %_6.i11.i169.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i76350.i.i = shufflevector <8 x i32> %_6.i12.i172.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  %_3.i77.i197.i = shufflevector <8 x i32> %_6.i13.i175.i, <8 x i32> poison, <8 x i32> <i32 4, i32 0, i32 6, i32 2, i32 4, i32 0, i32 6, i32 2>
  store <8 x i32> %_3.i194.i.i, ptr %tmp0.i, align 32, !noalias !25
  store <8 x i32> %_3.i74242.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i.i, align 32, !noalias !25
  store <8 x i32> %_3.i75296.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i.i, align 32, !noalias !25
  store <8 x i32> %_3.i76350.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i.i, align 32, !noalias !25
  store <8 x i32> %_3.i77.i197.i, ptr %_3.sroa.7.0._0.sroa_idx.i.i, align 32, !noalias !25
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_21, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp0.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp1.i) #12, !noalias !34
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp1.i), !noalias !25
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp0.i), !noalias !25
  %Q.sroa.0.0.copyload = load <8 x i32>, ptr %_21, align 32
  %Q.sroa.14.0.copyload = load <8 x i32>, ptr %Q.sroa.14.0._21.sroa_idx, align 32
  %Q.sroa.15.0.copyload = load <8 x i32>, ptr %Q.sroa.15.0._21.sroa_idx, align 32
  %Q.sroa.16.0.copyload = load <8 x i32>, ptr %Q.sroa.16.0._21.sroa_idx, align 32
  %Q.sroa.17.0.copyload = load <8 x i32>, ptr %Q.sroa.17.0._21.sroa_idx, align 32
  call void @llvm.lifetime.end.p0(ptr nonnull %_21)
  %_24 = getelementptr inbounds nuw i8, ptr %a_naf, i64 %i.sroa.0.2
  %_3.i = load i8, ptr %_24, align 1, !alias.scope !35, !noundef !14
  %_0.i = tail call noundef range(i8 -1, 2) i8 @llvm.scmp.i8.i8(i8 %_3.i, i8 0)
  switch i8 %_0.i, label %bb7 [
    i8 -1, label %bb22
    i8 0, label %bb31
    i8 1, label %bb23
  ]

bb7:                                              ; preds = %bb31, %bb18
  unreachable

bb22:                                             ; preds = %bb18
  call void @llvm.lifetime.start.p0(ptr nonnull %_37)
  %_43 = sub i8 0, %_3.i
  %_42 = sext i8 %_43 to i64
  tail call void @llvm.experimental.noalias.scope.decl(metadata !38)
  tail call void @llvm.experimental.noalias.scope.decl(metadata !41)
  %_61.i = lshr i64 %_42, 1
  %_7.i = icmp ult i8 %_43, 16
  br i1 %_7.i, label %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit, label %panic.i

panic.i:                                          ; preds = %bb22
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_61.i, i64 noundef 8, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_a8fabae8f73f66aef6660ad7c9447c5d) #13, !noalias !43
  unreachable

_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit: ; preds = %bb22
  %26 = getelementptr inbounds nuw %"backend::vector::avx2::edwards::CachedPoint", ptr %table_A, i64 %_61.i
  %_40.sroa.0.0.copyload = load <8 x i32>, ptr %26, align 32, !alias.scope !43
  %_40.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %26, i64 32
  %_40.sroa.4.0.copyload = load <8 x i32>, ptr %_40.sroa.4.0..sroa_idx, align 32, !alias.scope !43
  %_40.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %26, i64 64
  %_40.sroa.5.0.copyload = load <8 x i32>, ptr %_40.sroa.5.0..sroa_idx, align 32, !alias.scope !43
  %_40.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %26, i64 96
  %_40.sroa.6.0.copyload = load <8 x i32>, ptr %_40.sroa.6.0..sroa_idx, align 32, !alias.scope !43
  %_40.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %26, i64 128
  %_40.sroa.7.0.copyload = load <8 x i32>, ptr %_40.sroa.7.0..sroa_idx, align 32, !alias.scope !43
  call void @llvm.lifetime.start.p0(ptr nonnull %_4.i), !noalias !44
  %_3.i224.i.i.i = shufflevector <8 x i32> %_40.sroa.0.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74278.i.i.i = shufflevector <8 x i32> %_40.sroa.4.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75332.i.i.i = shufflevector <8 x i32> %_40.sroa.5.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76386.i.i.i = shufflevector <8 x i32> %_40.sroa.6.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i.i = shufflevector <8 x i32> %_40.sroa.7.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i.i = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217690, i32 poison, i32 67108862>, %_3.i224.i.i.i
  %_6.i10.i.i.i = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i74278.i.i.i
  %_6.i11.i.i.i = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i75332.i.i.i
  %_6.i12.i.i.i = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i76386.i.i.i
  %_6.i13.i.i.i = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i77.i.i.i
  %r.i190.i.i.i = shufflevector <8 x i32> %_3.i224.i.i.i, <8 x i32> %_6.i.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i.i.i = shufflevector <8 x i32> %_3.i74278.i.i.i, <8 x i32> %_6.i10.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i.i.i = shufflevector <8 x i32> %_3.i75332.i.i.i, <8 x i32> %_6.i11.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i.i.i = shufflevector <8 x i32> %_3.i76386.i.i.i, <8 x i32> %_6.i12.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i.i.i = shufflevector <8 x i32> %_3.i77.i.i.i, <8 x i32> %_6.i13.i.i.i, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  store <8 x i32> %r.i190.i.i.i, ptr %_4.i, align 32, !alias.scope !49, !noalias !52
  store <8 x i32> %r.i197.i.i.i, ptr %_4.sroa.4.0._0.sroa_idx.i.i, align 32, !alias.scope !49, !noalias !52
  store <8 x i32> %r.i204.i.i.i, ptr %_4.sroa.5.0._0.sroa_idx.i.i, align 32, !alias.scope !49, !noalias !52
  store <8 x i32> %r.i211.i.i.i, ptr %_4.sroa.6.0._0.sroa_idx.i.i, align 32, !alias.scope !49, !noalias !52
  store <8 x i32> %r.i218.i.i.i, ptr %_4.sroa.7.0._0.sroa_idx.i.i, align 32, !alias.scope !49, !noalias !52
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp.i.i), !noalias !54
  %_3.i219.i.i.i.i = shufflevector <8 x i32> %Q.sroa.0.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i.i = shufflevector <8 x i32> %Q.sroa.14.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i.i = shufflevector <8 x i32> %Q.sroa.15.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i.i = shufflevector <8 x i32> %Q.sroa.16.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i77.i.i.i.i = shufflevector <8 x i32> %Q.sroa.17.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i.i = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.0.0.copyload
  %_6.i10.i.i.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.14.0.copyload
  %_6.i11.i.i.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.15.0.copyload
  %_6.i12.i.i.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.16.0.copyload
  %_6.i13.i.i.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.17.0.copyload
  %r.i192.i.i.i.i = shufflevector <8 x i32> %_6.i.i.i.i.i, <8 x i32> %Q.sroa.0.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i.i = shufflevector <8 x i32> %_6.i10.i.i.i.i, <8 x i32> %Q.sroa.14.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i.i = shufflevector <8 x i32> %_6.i11.i.i.i.i, <8 x i32> %Q.sroa.15.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i.i = shufflevector <8 x i32> %_6.i12.i.i.i.i, <8 x i32> %Q.sroa.16.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i.i = shufflevector <8 x i32> %_6.i13.i.i.i.i, <8 x i32> %Q.sroa.17.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i.i = add <8 x i32> %r.i192.i.i.i.i, %_3.i219.i.i.i.i
  %_6.i10.i2.i.i.i = add <8 x i32> %r.i199.i.i.i.i, %_3.i74272.i.i.i.i
  %_6.i11.i3.i.i.i = add <8 x i32> %r.i206.i.i.i.i, %_3.i75326.i.i.i.i
  %_6.i12.i4.i.i.i = add <8 x i32> %r.i213.i.i.i.i, %_3.i76380.i.i.i.i
  %_6.i13.i5.i.i.i = add <8 x i32> %r.i220.i.i.i.i, %_3.i77.i.i.i.i
  %r.i191.i.i.i = shufflevector <8 x i32> %_6.i.i1.i.i.i, <8 x i32> %Q.sroa.0.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i.i = shufflevector <8 x i32> %_6.i10.i2.i.i.i, <8 x i32> %Q.sroa.14.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i.i = shufflevector <8 x i32> %_6.i11.i3.i.i.i, <8 x i32> %Q.sroa.15.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i.i = shufflevector <8 x i32> %_6.i12.i4.i.i.i, <8 x i32> %Q.sroa.16.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i.i = shufflevector <8 x i32> %_6.i13.i5.i.i.i, <8 x i32> %Q.sroa.17.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %r.i191.i.i.i, ptr %tmp.i.i, align 32, !noalias !54
  store <8 x i32> %r.i198.i.i.i, ptr %Q.sroa.14.0.tmp.i.i.sroa_idx, align 32, !noalias !54
  store <8 x i32> %r.i205.i.i.i, ptr %Q.sroa.15.0.tmp.i.i.sroa_idx, align 32, !noalias !54
  store <8 x i32> %r.i212.i.i.i, ptr %Q.sroa.16.0.tmp.i.i.sroa_idx, align 32, !noalias !54
  store <8 x i32> %r.i219.i.i.i, ptr %Q.sroa.17.0.tmp.i.i.sroa_idx, align 32, !noalias !54
  call void @llvm.lifetime.start.p0(ptr nonnull %_8.i.i), !noalias !54
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_8.i.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp.i.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %_4.i) #12, !noalias !59
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(160) %tmp.i.i, ptr noundef nonnull align 32 dereferenceable(160) %_8.i.i, i64 160, i1 false), !noalias !54
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.i.i), !noalias !54
  %_5423.i.i1.i = load <8 x i32>, ptr %tmp.i.i, align 32, !alias.scope !60, !noalias !63
  %_7184416.i.i2.i = load <8 x i32>, ptr %Q.sroa.14.0.tmp.i.i.sroa_idx, align 32, !alias.scope !60, !noalias !63
  %_9230417.i.i3.i = load <8 x i32>, ptr %Q.sroa.15.0.tmp.i.i.sroa_idx, align 32, !alias.scope !60, !noalias !63
  %_11284418.i.i4.i = load <8 x i32>, ptr %Q.sroa.16.0.tmp.i.i.sroa_idx, align 32, !alias.scope !60, !noalias !63
  %_3.i.i.i.i46 = shufflevector <8 x i32> %_5423.i.i1.i, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i74.i.i.i = shufflevector <8 x i32> %_7184416.i.i2.i, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i75.i.i.i = shufflevector <8 x i32> %_9230417.i.i3.i, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i76.i.i.i = shufflevector <8 x i32> %_11284418.i.i4.i, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_13339419.i.i5.i = load <8 x i32>, ptr %Q.sroa.17.0.tmp.i.i.sroa_idx, align 32, !alias.scope !60, !noalias !63
  %_3.i77.i.i6.i = shufflevector <8 x i32> %_13339419.i.i5.i, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i219.i.i5.i.i = shufflevector <8 x i32> %_5423.i.i1.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74272.i.i6.i.i = shufflevector <8 x i32> %_7184416.i.i2.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75326.i.i7.i.i = shufflevector <8 x i32> %_9230417.i.i3.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76380.i.i8.i.i = shufflevector <8 x i32> %_11284418.i.i4.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i11.i.i = shufflevector <8 x i32> %_13339419.i.i5.i, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i12.i.i = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i.i.i.i46
  %_6.i10.i.i13.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74.i.i.i
  %_6.i11.i.i14.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75.i.i.i
  %_6.i12.i.i15.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76.i.i.i
  %_6.i13.i.i16.i.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i.i6.i
  %r.i192.i.i17.i.i = shufflevector <8 x i32> %_6.i.i.i12.i.i, <8 x i32> %_3.i.i.i.i46, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i199.i.i18.i.i = shufflevector <8 x i32> %_6.i10.i.i13.i.i, <8 x i32> %_3.i74.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i206.i.i19.i.i = shufflevector <8 x i32> %_6.i11.i.i14.i.i, <8 x i32> %_3.i75.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i213.i.i20.i.i = shufflevector <8 x i32> %_6.i12.i.i15.i.i, <8 x i32> %_3.i76.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i220.i.i21.i.i = shufflevector <8 x i32> %_6.i13.i.i16.i.i, <8 x i32> %_3.i77.i.i6.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %_6.i.i1.i22.i.i = add <8 x i32> %r.i192.i.i17.i.i, %_3.i219.i.i5.i.i
  %_6.i10.i2.i23.i.i = add <8 x i32> %r.i199.i.i18.i.i, %_3.i74272.i.i6.i.i
  %_6.i11.i3.i24.i.i = add <8 x i32> %r.i206.i.i19.i.i, %_3.i75326.i.i7.i.i
  %_6.i12.i4.i25.i.i = add <8 x i32> %r.i213.i.i20.i.i, %_3.i76380.i.i8.i.i
  %_6.i13.i5.i26.i.i = add <8 x i32> %r.i220.i.i21.i.i, %_3.i77.i.i11.i.i
  call void @llvm.lifetime.start.p0(ptr nonnull %t0.i.i), !noalias !54
  %_3.i204.i.i.i = shufflevector <8 x i32> %_6.i.i1.i22.i.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i74254.i.i.i = shufflevector <8 x i32> %_6.i10.i2.i23.i.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i75308.i.i.i = shufflevector <8 x i32> %_6.i11.i3.i24.i.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i76362.i.i.i = shufflevector <8 x i32> %_6.i12.i4.i25.i.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i77.i37.i.i = shufflevector <8 x i32> %_6.i13.i5.i26.i.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  store <8 x i32> %_3.i204.i.i.i, ptr %t0.i.i, align 32, !alias.scope !65, !noalias !68
  store <8 x i32> %_3.i74254.i.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i38.i.i, align 32, !alias.scope !65, !noalias !68
  store <8 x i32> %_3.i75308.i.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i39.i.i, align 32, !alias.scope !65, !noalias !68
  store <8 x i32> %_3.i76362.i.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i40.i.i, align 32, !alias.scope !65, !noalias !68
  store <8 x i32> %_3.i77.i37.i.i, ptr %_3.sroa.7.0._0.sroa_idx.i41.i.i, align 32, !alias.scope !65, !noalias !68
  call void @llvm.lifetime.start.p0(ptr nonnull %t1.i.i), !noalias !54
  %_3.i209.i.i.i = shufflevector <8 x i32> %_6.i.i1.i22.i.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i74260.i.i.i = shufflevector <8 x i32> %_6.i10.i2.i23.i.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i75314.i.i.i = shufflevector <8 x i32> %_6.i11.i3.i24.i.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i76368.i.i.i = shufflevector <8 x i32> %_6.i12.i4.i25.i.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i77.i48.i.i = shufflevector <8 x i32> %_6.i13.i5.i26.i.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  store <8 x i32> %_3.i209.i.i.i, ptr %t1.i.i, align 32, !alias.scope !70, !noalias !73
  store <8 x i32> %_3.i74260.i.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i49.i.i, align 32, !alias.scope !70, !noalias !73
  store <8 x i32> %_3.i75314.i.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i50.i.i, align 32, !alias.scope !70, !noalias !73
  store <8 x i32> %_3.i76368.i.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i51.i.i, align 32, !alias.scope !70, !noalias !73
  store <8 x i32> %_3.i77.i48.i.i, ptr %_3.sroa.7.0._0.sroa_idx.i52.i.i, align 32, !alias.scope !70, !noalias !73
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_37, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t0.i.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t1.i.i) #12, !noalias !75
  call void @llvm.lifetime.end.p0(ptr nonnull %t1.i.i), !noalias !54
  call void @llvm.lifetime.end.p0(ptr nonnull %t0.i.i), !noalias !54
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp.i.i), !noalias !54
  call void @llvm.lifetime.end.p0(ptr nonnull %_4.i), !noalias !44
  %Q.sroa.0.0.copyload270 = load <8 x i32>, ptr %_37, align 32
  %Q.sroa.14.0.copyload280 = load <8 x i32>, ptr %Q.sroa.14.0._37.sroa_idx, align 32
  %Q.sroa.15.0.copyload290 = load <8 x i32>, ptr %Q.sroa.15.0._37.sroa_idx, align 32
  %Q.sroa.16.0.copyload300 = load <8 x i32>, ptr %Q.sroa.16.0._37.sroa_idx, align 32
  %Q.sroa.17.0.copyload310 = load <8 x i32>, ptr %Q.sroa.17.0._37.sroa_idx, align 32
  call void @llvm.lifetime.end.p0(ptr nonnull %_37)
  br label %bb31

bb23:                                             ; preds = %bb18
  call void @llvm.lifetime.start.p0(ptr nonnull %_28)
  %_33 = sext i8 %_3.i to i64
  %_61.i47 = lshr i64 %_33, 1
  %_7.i48 = icmp ult i8 %_3.i, 16
  br i1 %_7.i48, label %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50, label %panic.i49

panic.i49:                                        ; preds = %bb23
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_61.i47, i64 noundef 8, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_a8fabae8f73f66aef6660ad7c9447c5d) #13, !noalias !76
  unreachable

_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50: ; preds = %bb23
  %27 = getelementptr inbounds nuw %"backend::vector::avx2::edwards::CachedPoint", ptr %table_A, i64 %_61.i47
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp.i), !noalias !80
  %_3.i219.i.i.i = shufflevector <8 x i32> %Q.sroa.0.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i = shufflevector <8 x i32> %Q.sroa.14.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i = shufflevector <8 x i32> %Q.sroa.15.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i = shufflevector <8 x i32> %Q.sroa.16.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i77.i.i.i57 = shufflevector <8 x i32> %Q.sroa.17.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i58 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.0.0.copyload
  %_6.i10.i.i.i59 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.14.0.copyload
  %_6.i11.i.i.i60 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.15.0.copyload
  %_6.i12.i.i.i61 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.16.0.copyload
  %_6.i13.i.i.i62 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.17.0.copyload
  %r.i192.i.i.i = shufflevector <8 x i32> %_6.i.i.i.i58, <8 x i32> %Q.sroa.0.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i = shufflevector <8 x i32> %_6.i10.i.i.i59, <8 x i32> %Q.sroa.14.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i = shufflevector <8 x i32> %_6.i11.i.i.i60, <8 x i32> %Q.sroa.15.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i = shufflevector <8 x i32> %_6.i12.i.i.i61, <8 x i32> %Q.sroa.16.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i = shufflevector <8 x i32> %_6.i13.i.i.i62, <8 x i32> %Q.sroa.17.0.copyload, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i = add <8 x i32> %r.i192.i.i.i, %_3.i219.i.i.i
  %_6.i10.i2.i.i = add <8 x i32> %r.i199.i.i.i, %_3.i74272.i.i.i
  %_6.i11.i3.i.i = add <8 x i32> %r.i206.i.i.i, %_3.i75326.i.i.i
  %_6.i12.i4.i.i = add <8 x i32> %r.i213.i.i.i, %_3.i76380.i.i.i
  %_6.i13.i5.i.i = add <8 x i32> %r.i220.i.i.i, %_3.i77.i.i.i57
  %r.i191.i.i = shufflevector <8 x i32> %_6.i.i1.i.i, <8 x i32> %Q.sroa.0.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i = shufflevector <8 x i32> %_6.i10.i2.i.i, <8 x i32> %Q.sroa.14.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i = shufflevector <8 x i32> %_6.i11.i3.i.i, <8 x i32> %Q.sroa.15.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i = shufflevector <8 x i32> %_6.i12.i4.i.i, <8 x i32> %Q.sroa.16.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i = shufflevector <8 x i32> %_6.i13.i5.i.i, <8 x i32> %Q.sroa.17.0.copyload, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %r.i191.i.i, ptr %tmp.i, align 32, !noalias !80
  store <8 x i32> %r.i198.i.i, ptr %Q.sroa.14.0.tmp.i.sroa_idx, align 32, !noalias !80
  store <8 x i32> %r.i205.i.i, ptr %Q.sroa.15.0.tmp.i.sroa_idx, align 32, !noalias !80
  store <8 x i32> %r.i212.i.i, ptr %Q.sroa.16.0.tmp.i.sroa_idx, align 32, !noalias !80
  store <8 x i32> %r.i219.i.i, ptr %Q.sroa.17.0.tmp.i.sroa_idx, align 32, !noalias !80
  call void @llvm.lifetime.start.p0(ptr nonnull %_8.i), !noalias !80
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_8.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %27) #12
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(160) %tmp.i, ptr noundef nonnull align 32 dereferenceable(160) %_8.i, i64 160, i1 false), !noalias !80
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.i), !noalias !80
  %_5423.i.i63 = load <8 x i32>, ptr %tmp.i, align 32, !alias.scope !85, !noalias !88
  %_7184416.i.i64 = load <8 x i32>, ptr %Q.sroa.14.0.tmp.i.sroa_idx, align 32, !alias.scope !85, !noalias !88
  %_9230417.i.i65 = load <8 x i32>, ptr %Q.sroa.15.0.tmp.i.sroa_idx, align 32, !alias.scope !85, !noalias !88
  %_11284418.i.i66 = load <8 x i32>, ptr %Q.sroa.16.0.tmp.i.sroa_idx, align 32, !alias.scope !85, !noalias !88
  %_3.i.i.i = shufflevector <8 x i32> %_5423.i.i63, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i74.i.i = shufflevector <8 x i32> %_7184416.i.i64, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i75.i.i = shufflevector <8 x i32> %_9230417.i.i65, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i76.i.i = shufflevector <8 x i32> %_11284418.i.i66, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_13339419.i.i67 = load <8 x i32>, ptr %Q.sroa.17.0.tmp.i.sroa_idx, align 32, !alias.scope !85, !noalias !88
  %_3.i77.i.i68 = shufflevector <8 x i32> %_13339419.i.i67, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i219.i.i5.i = shufflevector <8 x i32> %_5423.i.i63, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74272.i.i6.i = shufflevector <8 x i32> %_7184416.i.i64, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75326.i.i7.i = shufflevector <8 x i32> %_9230417.i.i65, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76380.i.i8.i = shufflevector <8 x i32> %_11284418.i.i66, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i11.i = shufflevector <8 x i32> %_13339419.i.i67, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i12.i = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i.i.i
  %_6.i10.i.i13.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74.i.i
  %_6.i11.i.i14.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75.i.i
  %_6.i12.i.i15.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76.i.i
  %_6.i13.i.i16.i = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i.i68
  %r.i192.i.i17.i = shufflevector <8 x i32> %_6.i.i.i12.i, <8 x i32> %_3.i.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i199.i.i18.i = shufflevector <8 x i32> %_6.i10.i.i13.i, <8 x i32> %_3.i74.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i206.i.i19.i = shufflevector <8 x i32> %_6.i11.i.i14.i, <8 x i32> %_3.i75.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i213.i.i20.i = shufflevector <8 x i32> %_6.i12.i.i15.i, <8 x i32> %_3.i76.i.i, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i220.i.i21.i = shufflevector <8 x i32> %_6.i13.i.i16.i, <8 x i32> %_3.i77.i.i68, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %_6.i.i1.i22.i = add <8 x i32> %r.i192.i.i17.i, %_3.i219.i.i5.i
  %_6.i10.i2.i23.i = add <8 x i32> %r.i199.i.i18.i, %_3.i74272.i.i6.i
  %_6.i11.i3.i24.i = add <8 x i32> %r.i206.i.i19.i, %_3.i75326.i.i7.i
  %_6.i12.i4.i25.i = add <8 x i32> %r.i213.i.i20.i, %_3.i76380.i.i8.i
  %_6.i13.i5.i26.i = add <8 x i32> %r.i220.i.i21.i, %_3.i77.i.i11.i
  call void @llvm.lifetime.start.p0(ptr nonnull %t0.i), !noalias !80
  %_3.i204.i.i = shufflevector <8 x i32> %_6.i.i1.i22.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i74254.i.i = shufflevector <8 x i32> %_6.i10.i2.i23.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i75308.i.i = shufflevector <8 x i32> %_6.i11.i3.i24.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i76362.i.i = shufflevector <8 x i32> %_6.i12.i4.i25.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i77.i37.i = shufflevector <8 x i32> %_6.i13.i5.i26.i, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  store <8 x i32> %_3.i204.i.i, ptr %t0.i, align 32, !alias.scope !90, !noalias !93
  store <8 x i32> %_3.i74254.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i38.i, align 32, !alias.scope !90, !noalias !93
  store <8 x i32> %_3.i75308.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i39.i, align 32, !alias.scope !90, !noalias !93
  store <8 x i32> %_3.i76362.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i40.i, align 32, !alias.scope !90, !noalias !93
  store <8 x i32> %_3.i77.i37.i, ptr %_3.sroa.7.0._0.sroa_idx.i41.i, align 32, !alias.scope !90, !noalias !93
  call void @llvm.lifetime.start.p0(ptr nonnull %t1.i), !noalias !80
  %_3.i209.i.i = shufflevector <8 x i32> %_6.i.i1.i22.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i74260.i.i = shufflevector <8 x i32> %_6.i10.i2.i23.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i75314.i.i = shufflevector <8 x i32> %_6.i11.i3.i24.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i76368.i.i = shufflevector <8 x i32> %_6.i12.i4.i25.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i77.i48.i = shufflevector <8 x i32> %_6.i13.i5.i26.i, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  store <8 x i32> %_3.i209.i.i, ptr %t1.i, align 32, !alias.scope !95, !noalias !98
  store <8 x i32> %_3.i74260.i.i, ptr %_3.sroa.4.0._0.sroa_idx.i49.i, align 32, !alias.scope !95, !noalias !98
  store <8 x i32> %_3.i75314.i.i, ptr %_3.sroa.5.0._0.sroa_idx.i50.i, align 32, !alias.scope !95, !noalias !98
  store <8 x i32> %_3.i76368.i.i, ptr %_3.sroa.6.0._0.sroa_idx.i51.i, align 32, !alias.scope !95, !noalias !98
  store <8 x i32> %_3.i77.i48.i, ptr %_3.sroa.7.0._0.sroa_idx.i52.i, align 32, !alias.scope !95, !noalias !98
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_28, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t0.i, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t1.i) #12, !noalias !100
  call void @llvm.lifetime.end.p0(ptr nonnull %t1.i), !noalias !80
  call void @llvm.lifetime.end.p0(ptr nonnull %t0.i), !noalias !80
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp.i), !noalias !80
  %Q.sroa.0.0.copyload271 = load <8 x i32>, ptr %_28, align 32
  %Q.sroa.14.0.copyload281 = load <8 x i32>, ptr %Q.sroa.14.0._28.sroa_idx, align 32
  %Q.sroa.15.0.copyload291 = load <8 x i32>, ptr %Q.sroa.15.0._28.sroa_idx, align 32
  %Q.sroa.16.0.copyload301 = load <8 x i32>, ptr %Q.sroa.16.0._28.sroa_idx, align 32
  %Q.sroa.17.0.copyload311 = load <8 x i32>, ptr %Q.sroa.17.0._28.sroa_idx, align 32
  call void @llvm.lifetime.end.p0(ptr nonnull %_28)
  br label %bb31

bb31:                                             ; preds = %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit, %bb18
  %Q.sroa.16.1 = phi <8 x i32> [ %Q.sroa.16.0.copyload300, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit ], [ %Q.sroa.16.0.copyload, %bb18 ], [ %Q.sroa.16.0.copyload301, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50 ]
  %Q.sroa.15.1 = phi <8 x i32> [ %Q.sroa.15.0.copyload290, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit ], [ %Q.sroa.15.0.copyload, %bb18 ], [ %Q.sroa.15.0.copyload291, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50 ]
  %Q.sroa.14.1 = phi <8 x i32> [ %Q.sroa.14.0.copyload280, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit ], [ %Q.sroa.14.0.copyload, %bb18 ], [ %Q.sroa.14.0.copyload281, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50 ]
  %Q.sroa.0.1 = phi <8 x i32> [ %Q.sroa.0.0.copyload270, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit ], [ %Q.sroa.0.0.copyload, %bb18 ], [ %Q.sroa.0.0.copyload271, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50 ]
  %Q.sroa.17.1 = phi <8 x i32> [ %Q.sroa.17.0.copyload310, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit ], [ %Q.sroa.17.0.copyload, %bb18 ], [ %Q.sroa.17.0.copyload311, %_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_.exit50 ]
  %_48 = getelementptr inbounds nuw i8, ptr %b_naf, i64 %i.sroa.0.2
  %_3.i69 = load i8, ptr %_48, align 1, !alias.scope !101, !noundef !14
  %_0.i70 = tail call noundef range(i8 -1, 2) i8 @llvm.scmp.i8.i8(i8 %_3.i69, i8 0)
  switch i8 %_0.i70, label %bb7 [
    i8 -1, label %bb33
    i8 0, label %bb41
    i8 1, label %bb34
  ]

bb33:                                             ; preds = %bb31
  call void @llvm.lifetime.start.p0(ptr nonnull %_60)
  %_65 = sub i8 0, %_3.i69
  %_64 = sext i8 %_65 to i64
  %_61.i71 = lshr i64 %_64, 1
  %_7.i72 = icmp sgt i8 %_65, -1
  br i1 %_7.i72, label %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit, label %panic.i73

panic.i73:                                        ; preds = %bb33
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_61.i71, i64 noundef 64, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_f7b128ba219626851d37833adc9e2368) #13, !noalias !104
  unreachable

_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit: ; preds = %bb33
  %28 = getelementptr inbounds nuw %"backend::vector::avx2::edwards::CachedPoint", ptr @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE, i64 %_61.i71
  %_63.sroa.0.0.copyload = load <8 x i32>, ptr %28, align 32
  %_63.sroa.4.0..sroa_idx = getelementptr inbounds nuw i8, ptr %28, i64 32
  %_63.sroa.4.0.copyload = load <8 x i32>, ptr %_63.sroa.4.0..sroa_idx, align 32
  %_63.sroa.5.0..sroa_idx = getelementptr inbounds nuw i8, ptr %28, i64 64
  %_63.sroa.5.0.copyload = load <8 x i32>, ptr %_63.sroa.5.0..sroa_idx, align 32
  %_63.sroa.6.0..sroa_idx = getelementptr inbounds nuw i8, ptr %28, i64 96
  %_63.sroa.6.0.copyload = load <8 x i32>, ptr %_63.sroa.6.0..sroa_idx, align 32
  %_63.sroa.7.0..sroa_idx = getelementptr inbounds nuw i8, ptr %28, i64 128
  %_63.sroa.7.0.copyload = load <8 x i32>, ptr %_63.sroa.7.0..sroa_idx, align 32
  call void @llvm.lifetime.start.p0(ptr nonnull %_4.i78), !noalias !107
  %_3.i224.i.i.i83 = shufflevector <8 x i32> %_63.sroa.0.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74278.i.i.i84 = shufflevector <8 x i32> %_63.sroa.4.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75332.i.i.i85 = shufflevector <8 x i32> %_63.sroa.5.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76386.i.i.i86 = shufflevector <8 x i32> %_63.sroa.6.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i.i89 = shufflevector <8 x i32> %_63.sroa.7.0.copyload, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i.i90 = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217690, i32 poison, i32 67108862>, %_3.i224.i.i.i83
  %_6.i10.i.i.i91 = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i74278.i.i.i84
  %_6.i11.i.i.i92 = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i75332.i.i.i85
  %_6.i12.i.i.i93 = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i76386.i.i.i86
  %_6.i13.i.i.i94 = sub <8 x i32> <i32 poison, i32 poison, i32 poison, i32 poison, i32 poison, i32 134217726, i32 poison, i32 67108862>, %_3.i77.i.i.i89
  %r.i190.i.i.i95 = shufflevector <8 x i32> %_3.i224.i.i.i83, <8 x i32> %_6.i.i.i.i90, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i197.i.i.i96 = shufflevector <8 x i32> %_3.i74278.i.i.i84, <8 x i32> %_6.i10.i.i.i91, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i204.i.i.i97 = shufflevector <8 x i32> %_3.i75332.i.i.i85, <8 x i32> %_6.i11.i.i.i92, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i211.i.i.i98 = shufflevector <8 x i32> %_3.i76386.i.i.i86, <8 x i32> %_6.i12.i.i.i93, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  %r.i218.i.i.i99 = shufflevector <8 x i32> %_3.i77.i.i.i89, <8 x i32> %_6.i13.i.i.i94, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 4, i32 13, i32 6, i32 15>
  store <8 x i32> %r.i190.i.i.i95, ptr %_4.i78, align 32, !alias.scope !112, !noalias !115
  store <8 x i32> %r.i197.i.i.i96, ptr %_4.sroa.4.0._0.sroa_idx.i.i100, align 32, !alias.scope !112, !noalias !115
  store <8 x i32> %r.i204.i.i.i97, ptr %_4.sroa.5.0._0.sroa_idx.i.i101, align 32, !alias.scope !112, !noalias !115
  store <8 x i32> %r.i211.i.i.i98, ptr %_4.sroa.6.0._0.sroa_idx.i.i102, align 32, !alias.scope !112, !noalias !115
  store <8 x i32> %r.i218.i.i.i99, ptr %_4.sroa.7.0._0.sroa_idx.i.i103, align 32, !alias.scope !112, !noalias !115
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp.i.i77), !noalias !117
  %_3.i219.i.i.i.i108 = shufflevector <8 x i32> %Q.sroa.0.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i.i109 = shufflevector <8 x i32> %Q.sroa.14.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i.i110 = shufflevector <8 x i32> %Q.sroa.15.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i.i111 = shufflevector <8 x i32> %Q.sroa.16.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i77.i.i.i.i114 = shufflevector <8 x i32> %Q.sroa.17.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i.i115 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.0.1
  %_6.i10.i.i.i.i116 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.14.1
  %_6.i11.i.i.i.i117 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.15.1
  %_6.i12.i.i.i.i118 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.16.1
  %_6.i13.i.i.i.i119 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.17.1
  %r.i192.i.i.i.i120 = shufflevector <8 x i32> %_6.i.i.i.i.i115, <8 x i32> %Q.sroa.0.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i.i121 = shufflevector <8 x i32> %_6.i10.i.i.i.i116, <8 x i32> %Q.sroa.14.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i.i122 = shufflevector <8 x i32> %_6.i11.i.i.i.i117, <8 x i32> %Q.sroa.15.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i.i123 = shufflevector <8 x i32> %_6.i12.i.i.i.i118, <8 x i32> %Q.sroa.16.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i.i124 = shufflevector <8 x i32> %_6.i13.i.i.i.i119, <8 x i32> %Q.sroa.17.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i.i125 = add <8 x i32> %r.i192.i.i.i.i120, %_3.i219.i.i.i.i108
  %_6.i10.i2.i.i.i126 = add <8 x i32> %r.i199.i.i.i.i121, %_3.i74272.i.i.i.i109
  %_6.i11.i3.i.i.i127 = add <8 x i32> %r.i206.i.i.i.i122, %_3.i75326.i.i.i.i110
  %_6.i12.i4.i.i.i128 = add <8 x i32> %r.i213.i.i.i.i123, %_3.i76380.i.i.i.i111
  %_6.i13.i5.i.i.i129 = add <8 x i32> %r.i220.i.i.i.i124, %_3.i77.i.i.i.i114
  %r.i191.i.i.i130 = shufflevector <8 x i32> %_6.i.i1.i.i.i125, <8 x i32> %Q.sroa.0.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i.i131 = shufflevector <8 x i32> %_6.i10.i2.i.i.i126, <8 x i32> %Q.sroa.14.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i.i132 = shufflevector <8 x i32> %_6.i11.i3.i.i.i127, <8 x i32> %Q.sroa.15.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i.i133 = shufflevector <8 x i32> %_6.i12.i4.i.i.i128, <8 x i32> %Q.sroa.16.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i.i134 = shufflevector <8 x i32> %_6.i13.i5.i.i.i129, <8 x i32> %Q.sroa.17.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %r.i191.i.i.i130, ptr %tmp.i.i77, align 32, !noalias !117
  store <8 x i32> %r.i198.i.i.i131, ptr %Q.sroa.14.0.tmp.i.i77.sroa_idx, align 32, !noalias !117
  store <8 x i32> %r.i205.i.i.i132, ptr %Q.sroa.15.0.tmp.i.i77.sroa_idx, align 32, !noalias !117
  store <8 x i32> %r.i212.i.i.i133, ptr %Q.sroa.16.0.tmp.i.i77.sroa_idx, align 32, !noalias !117
  store <8 x i32> %r.i219.i.i.i134, ptr %Q.sroa.17.0.tmp.i.i77.sroa_idx, align 32, !noalias !117
  call void @llvm.lifetime.start.p0(ptr nonnull %_8.i.i76), !noalias !117
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_8.i.i76, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp.i.i77, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %_4.i78) #12, !noalias !122
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(160) %tmp.i.i77, ptr noundef nonnull align 32 dereferenceable(160) %_8.i.i76, i64 160, i1 false), !noalias !117
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.i.i76), !noalias !117
  %_5423.i.i1.i135 = load <8 x i32>, ptr %tmp.i.i77, align 32, !alias.scope !123, !noalias !126
  %_7184416.i.i2.i136 = load <8 x i32>, ptr %Q.sroa.14.0.tmp.i.i77.sroa_idx, align 32, !alias.scope !123, !noalias !126
  %_9230417.i.i3.i137 = load <8 x i32>, ptr %Q.sroa.15.0.tmp.i.i77.sroa_idx, align 32, !alias.scope !123, !noalias !126
  %_11284418.i.i4.i138 = load <8 x i32>, ptr %Q.sroa.16.0.tmp.i.i77.sroa_idx, align 32, !alias.scope !123, !noalias !126
  %_3.i.i.i.i139 = shufflevector <8 x i32> %_5423.i.i1.i135, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i74.i.i.i140 = shufflevector <8 x i32> %_7184416.i.i2.i136, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i75.i.i.i141 = shufflevector <8 x i32> %_9230417.i.i3.i137, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i76.i.i.i142 = shufflevector <8 x i32> %_11284418.i.i4.i138, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_13339419.i.i5.i143 = load <8 x i32>, ptr %Q.sroa.17.0.tmp.i.i77.sroa_idx, align 32, !alias.scope !123, !noalias !126
  %_3.i77.i.i6.i144 = shufflevector <8 x i32> %_13339419.i.i5.i143, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i219.i.i5.i.i145 = shufflevector <8 x i32> %_5423.i.i1.i135, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74272.i.i6.i.i146 = shufflevector <8 x i32> %_7184416.i.i2.i136, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75326.i.i7.i.i147 = shufflevector <8 x i32> %_9230417.i.i3.i137, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76380.i.i8.i.i148 = shufflevector <8 x i32> %_11284418.i.i4.i138, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i11.i.i149 = shufflevector <8 x i32> %_13339419.i.i5.i143, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i12.i.i150 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i.i.i.i139
  %_6.i10.i.i13.i.i151 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74.i.i.i140
  %_6.i11.i.i14.i.i152 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75.i.i.i141
  %_6.i12.i.i15.i.i153 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76.i.i.i142
  %_6.i13.i.i16.i.i154 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i.i6.i144
  %r.i192.i.i17.i.i155 = shufflevector <8 x i32> %_6.i.i.i12.i.i150, <8 x i32> %_3.i.i.i.i139, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i199.i.i18.i.i156 = shufflevector <8 x i32> %_6.i10.i.i13.i.i151, <8 x i32> %_3.i74.i.i.i140, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i206.i.i19.i.i157 = shufflevector <8 x i32> %_6.i11.i.i14.i.i152, <8 x i32> %_3.i75.i.i.i141, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i213.i.i20.i.i158 = shufflevector <8 x i32> %_6.i12.i.i15.i.i153, <8 x i32> %_3.i76.i.i.i142, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i220.i.i21.i.i159 = shufflevector <8 x i32> %_6.i13.i.i16.i.i154, <8 x i32> %_3.i77.i.i6.i144, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %_6.i.i1.i22.i.i160 = add <8 x i32> %r.i192.i.i17.i.i155, %_3.i219.i.i5.i.i145
  %_6.i10.i2.i23.i.i161 = add <8 x i32> %r.i199.i.i18.i.i156, %_3.i74272.i.i6.i.i146
  %_6.i11.i3.i24.i.i162 = add <8 x i32> %r.i206.i.i19.i.i157, %_3.i75326.i.i7.i.i147
  %_6.i12.i4.i25.i.i163 = add <8 x i32> %r.i213.i.i20.i.i158, %_3.i76380.i.i8.i.i148
  %_6.i13.i5.i26.i.i164 = add <8 x i32> %r.i220.i.i21.i.i159, %_3.i77.i.i11.i.i149
  call void @llvm.lifetime.start.p0(ptr nonnull %t0.i.i75), !noalias !117
  %_3.i204.i.i.i165 = shufflevector <8 x i32> %_6.i.i1.i22.i.i160, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i74254.i.i.i166 = shufflevector <8 x i32> %_6.i10.i2.i23.i.i161, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i75308.i.i.i167 = shufflevector <8 x i32> %_6.i11.i3.i24.i.i162, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i76362.i.i.i168 = shufflevector <8 x i32> %_6.i12.i4.i25.i.i163, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i77.i37.i.i169 = shufflevector <8 x i32> %_6.i13.i5.i26.i.i164, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  store <8 x i32> %_3.i204.i.i.i165, ptr %t0.i.i75, align 32, !alias.scope !128, !noalias !131
  store <8 x i32> %_3.i74254.i.i.i166, ptr %_3.sroa.4.0._0.sroa_idx.i38.i.i170, align 32, !alias.scope !128, !noalias !131
  store <8 x i32> %_3.i75308.i.i.i167, ptr %_3.sroa.5.0._0.sroa_idx.i39.i.i171, align 32, !alias.scope !128, !noalias !131
  store <8 x i32> %_3.i76362.i.i.i168, ptr %_3.sroa.6.0._0.sroa_idx.i40.i.i172, align 32, !alias.scope !128, !noalias !131
  store <8 x i32> %_3.i77.i37.i.i169, ptr %_3.sroa.7.0._0.sroa_idx.i41.i.i173, align 32, !alias.scope !128, !noalias !131
  call void @llvm.lifetime.start.p0(ptr nonnull %t1.i.i74), !noalias !117
  %_3.i209.i.i.i174 = shufflevector <8 x i32> %_6.i.i1.i22.i.i160, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i74260.i.i.i175 = shufflevector <8 x i32> %_6.i10.i2.i23.i.i161, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i75314.i.i.i176 = shufflevector <8 x i32> %_6.i11.i3.i24.i.i162, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i76368.i.i.i177 = shufflevector <8 x i32> %_6.i12.i4.i25.i.i163, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i77.i48.i.i178 = shufflevector <8 x i32> %_6.i13.i5.i26.i.i164, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  store <8 x i32> %_3.i209.i.i.i174, ptr %t1.i.i74, align 32, !alias.scope !133, !noalias !136
  store <8 x i32> %_3.i74260.i.i.i175, ptr %_3.sroa.4.0._0.sroa_idx.i49.i.i179, align 32, !alias.scope !133, !noalias !136
  store <8 x i32> %_3.i75314.i.i.i176, ptr %_3.sroa.5.0._0.sroa_idx.i50.i.i180, align 32, !alias.scope !133, !noalias !136
  store <8 x i32> %_3.i76368.i.i.i177, ptr %_3.sroa.6.0._0.sroa_idx.i51.i.i181, align 32, !alias.scope !133, !noalias !136
  store <8 x i32> %_3.i77.i48.i.i178, ptr %_3.sroa.7.0._0.sroa_idx.i52.i.i182, align 32, !alias.scope !133, !noalias !136
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_60, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t0.i.i75, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t1.i.i74) #12, !noalias !138
  call void @llvm.lifetime.end.p0(ptr nonnull %t1.i.i74), !noalias !117
  call void @llvm.lifetime.end.p0(ptr nonnull %t0.i.i75), !noalias !117
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp.i.i77), !noalias !117
  call void @llvm.lifetime.end.p0(ptr nonnull %_4.i78), !noalias !107
  %Q.sroa.0.0.copyload272 = load <8 x i32>, ptr %_60, align 32
  %Q.sroa.14.0.copyload282 = load <8 x i32>, ptr %Q.sroa.14.0._60.sroa_idx, align 32
  %Q.sroa.15.0.copyload292 = load <8 x i32>, ptr %Q.sroa.15.0._60.sroa_idx, align 32
  %Q.sroa.16.0.copyload302 = load <8 x i32>, ptr %Q.sroa.16.0._60.sroa_idx, align 32
  %Q.sroa.17.0.copyload312 = load <8 x i32>, ptr %Q.sroa.17.0._60.sroa_idx, align 32
  call void @llvm.lifetime.end.p0(ptr nonnull %_60)
  br label %bb41

bb41:                                             ; preds = %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit, %bb31
  %Q.sroa.16.2 = phi <8 x i32> [ %Q.sroa.16.0.copyload302, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit ], [ %Q.sroa.16.1, %bb31 ], [ %Q.sroa.16.0.copyload303, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186 ]
  %Q.sroa.15.2 = phi <8 x i32> [ %Q.sroa.15.0.copyload292, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit ], [ %Q.sroa.15.1, %bb31 ], [ %Q.sroa.15.0.copyload293, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186 ]
  %Q.sroa.14.2 = phi <8 x i32> [ %Q.sroa.14.0.copyload282, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit ], [ %Q.sroa.14.1, %bb31 ], [ %Q.sroa.14.0.copyload283, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186 ]
  %Q.sroa.0.2 = phi <8 x i32> [ %Q.sroa.0.0.copyload272, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit ], [ %Q.sroa.0.1, %bb31 ], [ %Q.sroa.0.0.copyload273, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186 ]
  %Q.sroa.17.2 = phi <8 x i32> [ %Q.sroa.17.0.copyload312, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit ], [ %Q.sroa.17.1, %bb31 ], [ %Q.sroa.17.0.copyload313, %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186 ]
  %29 = icmp eq i64 %i.sroa.0.2, 0
  %30 = add nsw i64 %i.sroa.0.2, -1
  br i1 %29, label %bb42, label %bb18

bb34:                                             ; preds = %bb31
  call void @llvm.lifetime.start.p0(ptr nonnull %_52)
  %_56 = sext i8 %_3.i69 to i64
  %_61.i183 = lshr i64 %_56, 1
  %_7.i184 = icmp sgt i8 %_3.i69, -1
  br i1 %_7.i184, label %_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186, label %panic.i185

panic.i185:                                       ; preds = %bb34
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_61.i183, i64 noundef 64, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_f7b128ba219626851d37833adc9e2368) #13, !noalias !139
  unreachable

_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_.exit186: ; preds = %bb34
  %31 = getelementptr inbounds nuw %"backend::vector::avx2::edwards::CachedPoint", ptr @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx29constants26BASEPOINT_ODD_LOOKUP_TABLE, i64 %_61.i183
  call void @llvm.lifetime.start.p0(ptr nonnull %tmp.i190), !noalias !142
  %_3.i219.i.i.i195 = shufflevector <8 x i32> %Q.sroa.0.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i74272.i.i.i196 = shufflevector <8 x i32> %Q.sroa.14.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i75326.i.i.i197 = shufflevector <8 x i32> %Q.sroa.15.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i76380.i.i.i198 = shufflevector <8 x i32> %Q.sroa.16.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_3.i77.i.i.i201 = shufflevector <8 x i32> %Q.sroa.17.1, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i.i.i202 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.0.1
  %_6.i10.i.i.i203 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.14.1
  %_6.i11.i.i.i204 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.15.1
  %_6.i12.i.i.i205 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.16.1
  %_6.i13.i.i.i206 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 poison, i32 poison, i32 poison, i32 poison>, %Q.sroa.17.1
  %r.i192.i.i.i207 = shufflevector <8 x i32> %_6.i.i.i.i202, <8 x i32> %Q.sroa.0.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i199.i.i.i208 = shufflevector <8 x i32> %_6.i10.i.i.i203, <8 x i32> %Q.sroa.14.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i206.i.i.i209 = shufflevector <8 x i32> %_6.i11.i.i.i204, <8 x i32> %Q.sroa.15.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i213.i.i.i210 = shufflevector <8 x i32> %_6.i12.i.i.i205, <8 x i32> %Q.sroa.16.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %r.i220.i.i.i211 = shufflevector <8 x i32> %_6.i13.i.i.i206, <8 x i32> %Q.sroa.17.1, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 poison, i32 poison, i32 poison, i32 poison>
  %_6.i.i1.i.i212 = add <8 x i32> %r.i192.i.i.i207, %_3.i219.i.i.i195
  %_6.i10.i2.i.i213 = add <8 x i32> %r.i199.i.i.i208, %_3.i74272.i.i.i196
  %_6.i11.i3.i.i214 = add <8 x i32> %r.i206.i.i.i209, %_3.i75326.i.i.i197
  %_6.i12.i4.i.i215 = add <8 x i32> %r.i213.i.i.i210, %_3.i76380.i.i.i198
  %_6.i13.i5.i.i216 = add <8 x i32> %r.i220.i.i.i211, %_3.i77.i.i.i201
  %r.i191.i.i217 = shufflevector <8 x i32> %_6.i.i1.i.i212, <8 x i32> %Q.sroa.0.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i198.i.i218 = shufflevector <8 x i32> %_6.i10.i2.i.i213, <8 x i32> %Q.sroa.14.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i205.i.i219 = shufflevector <8 x i32> %_6.i11.i3.i.i214, <8 x i32> %Q.sroa.15.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i212.i.i220 = shufflevector <8 x i32> %_6.i12.i4.i.i215, <8 x i32> %Q.sroa.16.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  %r.i219.i.i221 = shufflevector <8 x i32> %_6.i13.i5.i.i216, <8 x i32> %Q.sroa.17.1, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 12, i32 13, i32 14, i32 15>
  store <8 x i32> %r.i191.i.i217, ptr %tmp.i190, align 32, !noalias !142
  store <8 x i32> %r.i198.i.i218, ptr %Q.sroa.14.0.tmp.i190.sroa_idx, align 32, !noalias !142
  store <8 x i32> %r.i205.i.i219, ptr %Q.sroa.15.0.tmp.i190.sroa_idx, align 32, !noalias !142
  store <8 x i32> %r.i212.i.i220, ptr %Q.sroa.16.0.tmp.i190.sroa_idx, align 32, !noalias !142
  store <8 x i32> %r.i219.i.i221, ptr %Q.sroa.17.0.tmp.i190.sroa_idx, align 32, !noalias !142
  call void @llvm.lifetime.start.p0(ptr nonnull %_8.i189), !noalias !142
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_8.i189, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %tmp.i190, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %31) #12
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 32 dereferenceable(160) %tmp.i190, ptr noundef nonnull align 32 dereferenceable(160) %_8.i189, i64 160, i1 false), !noalias !142
  call void @llvm.lifetime.end.p0(ptr nonnull %_8.i189), !noalias !142
  %_5423.i.i222 = load <8 x i32>, ptr %tmp.i190, align 32, !alias.scope !147, !noalias !150
  %_7184416.i.i223 = load <8 x i32>, ptr %Q.sroa.14.0.tmp.i190.sroa_idx, align 32, !alias.scope !147, !noalias !150
  %_9230417.i.i224 = load <8 x i32>, ptr %Q.sroa.15.0.tmp.i190.sroa_idx, align 32, !alias.scope !147, !noalias !150
  %_11284418.i.i225 = load <8 x i32>, ptr %Q.sroa.16.0.tmp.i190.sroa_idx, align 32, !alias.scope !147, !noalias !150
  %_3.i.i.i226 = shufflevector <8 x i32> %_5423.i.i222, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i74.i.i227 = shufflevector <8 x i32> %_7184416.i.i223, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i75.i.i228 = shufflevector <8 x i32> %_9230417.i.i224, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i76.i.i229 = shufflevector <8 x i32> %_11284418.i.i225, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_13339419.i.i230 = load <8 x i32>, ptr %Q.sroa.17.0.tmp.i190.sroa_idx, align 32, !alias.scope !147, !noalias !150
  %_3.i77.i.i231 = shufflevector <8 x i32> %_13339419.i.i230, <8 x i32> poison, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 5, i32 4, i32 7, i32 6>
  %_3.i219.i.i5.i232 = shufflevector <8 x i32> %_5423.i.i222, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i74272.i.i6.i233 = shufflevector <8 x i32> %_7184416.i.i223, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i75326.i.i7.i234 = shufflevector <8 x i32> %_9230417.i.i224, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i76380.i.i8.i235 = shufflevector <8 x i32> %_11284418.i.i225, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_3.i77.i.i11.i236 = shufflevector <8 x i32> %_13339419.i.i230, <8 x i32> poison, <8 x i32> <i32 1, i32 0, i32 3, i32 2, i32 4, i32 5, i32 6, i32 7>
  %_6.i.i.i12.i237 = sub <8 x i32> <i32 134217690, i32 poison, i32 67108862, i32 poison, i32 134217690, i32 poison, i32 67108862, i32 poison>, %_3.i.i.i226
  %_6.i10.i.i13.i238 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i74.i.i227
  %_6.i11.i.i14.i239 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i75.i.i228
  %_6.i12.i.i15.i240 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i76.i.i229
  %_6.i13.i.i16.i241 = sub <8 x i32> <i32 134217726, i32 poison, i32 67108862, i32 poison, i32 134217726, i32 poison, i32 67108862, i32 poison>, %_3.i77.i.i231
  %r.i192.i.i17.i242 = shufflevector <8 x i32> %_6.i.i.i12.i237, <8 x i32> %_3.i.i.i226, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i199.i.i18.i243 = shufflevector <8 x i32> %_6.i10.i.i13.i238, <8 x i32> %_3.i74.i.i227, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i206.i.i19.i244 = shufflevector <8 x i32> %_6.i11.i.i14.i239, <8 x i32> %_3.i75.i.i228, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i213.i.i20.i245 = shufflevector <8 x i32> %_6.i12.i.i15.i240, <8 x i32> %_3.i76.i.i229, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %r.i220.i.i21.i246 = shufflevector <8 x i32> %_6.i13.i.i16.i241, <8 x i32> %_3.i77.i.i231, <8 x i32> <i32 0, i32 9, i32 2, i32 11, i32 4, i32 13, i32 6, i32 15>
  %_6.i.i1.i22.i247 = add <8 x i32> %r.i192.i.i17.i242, %_3.i219.i.i5.i232
  %_6.i10.i2.i23.i248 = add <8 x i32> %r.i199.i.i18.i243, %_3.i74272.i.i6.i233
  %_6.i11.i3.i24.i249 = add <8 x i32> %r.i206.i.i19.i244, %_3.i75326.i.i7.i234
  %_6.i12.i4.i25.i250 = add <8 x i32> %r.i213.i.i20.i245, %_3.i76380.i.i8.i235
  %_6.i13.i5.i26.i251 = add <8 x i32> %r.i220.i.i21.i246, %_3.i77.i.i11.i236
  call void @llvm.lifetime.start.p0(ptr nonnull %t0.i188), !noalias !142
  %_3.i204.i.i252 = shufflevector <8 x i32> %_6.i.i1.i22.i247, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i74254.i.i253 = shufflevector <8 x i32> %_6.i10.i2.i23.i248, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i75308.i.i254 = shufflevector <8 x i32> %_6.i11.i3.i24.i249, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i76362.i.i255 = shufflevector <8 x i32> %_6.i12.i4.i25.i250, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  %_3.i77.i37.i256 = shufflevector <8 x i32> %_6.i13.i5.i26.i251, <8 x i32> poison, <8 x i32> <i32 0, i32 5, i32 2, i32 7, i32 5, i32 0, i32 7, i32 2>
  store <8 x i32> %_3.i204.i.i252, ptr %t0.i188, align 32, !alias.scope !152, !noalias !155
  store <8 x i32> %_3.i74254.i.i253, ptr %_3.sroa.4.0._0.sroa_idx.i38.i257, align 32, !alias.scope !152, !noalias !155
  store <8 x i32> %_3.i75308.i.i254, ptr %_3.sroa.5.0._0.sroa_idx.i39.i258, align 32, !alias.scope !152, !noalias !155
  store <8 x i32> %_3.i76362.i.i255, ptr %_3.sroa.6.0._0.sroa_idx.i40.i259, align 32, !alias.scope !152, !noalias !155
  store <8 x i32> %_3.i77.i37.i256, ptr %_3.sroa.7.0._0.sroa_idx.i41.i260, align 32, !alias.scope !152, !noalias !155
  call void @llvm.lifetime.start.p0(ptr nonnull %t1.i187), !noalias !142
  %_3.i209.i.i261 = shufflevector <8 x i32> %_6.i.i1.i22.i247, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i74260.i.i262 = shufflevector <8 x i32> %_6.i10.i2.i23.i248, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i75314.i.i263 = shufflevector <8 x i32> %_6.i11.i3.i24.i249, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i76368.i.i264 = shufflevector <8 x i32> %_6.i12.i4.i25.i250, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  %_3.i77.i48.i265 = shufflevector <8 x i32> %_6.i13.i5.i26.i251, <8 x i32> poison, <8 x i32> <i32 4, i32 1, i32 6, i32 3, i32 4, i32 1, i32 6, i32 3>
  store <8 x i32> %_3.i209.i.i261, ptr %t1.i187, align 32, !alias.scope !157, !noalias !160
  store <8 x i32> %_3.i74260.i.i262, ptr %_3.sroa.4.0._0.sroa_idx.i49.i266, align 32, !alias.scope !157, !noalias !160
  store <8 x i32> %_3.i75314.i.i263, ptr %_3.sroa.5.0._0.sroa_idx.i50.i267, align 32, !alias.scope !157, !noalias !160
  store <8 x i32> %_3.i76368.i.i264, ptr %_3.sroa.6.0._0.sroa_idx.i51.i268, align 32, !alias.scope !157, !noalias !160
  store <8 x i32> %_3.i77.i48.i265, ptr %_3.sroa.7.0._0.sroa_idx.i52.i269, align 32, !alias.scope !157, !noalias !160
  call fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr noalias nofree noundef nonnull align 32 captures(address) dereferenceable(160) %_52, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t0.i188, ptr noalias nofree noundef nonnull readonly align 32 captures(address, read_provenance) dereferenceable(160) %t1.i187) #12, !noalias !162
  call void @llvm.lifetime.end.p0(ptr nonnull %t1.i187), !noalias !142
  call void @llvm.lifetime.end.p0(ptr nonnull %t0.i188), !noalias !142
  call void @llvm.lifetime.end.p0(ptr nonnull %tmp.i190), !noalias !142
  %Q.sroa.0.0.copyload273 = load <8 x i32>, ptr %_52, align 32
  %Q.sroa.14.0.copyload283 = load <8 x i32>, ptr %Q.sroa.14.0._52.sroa_idx, align 32
  %Q.sroa.15.0.copyload293 = load <8 x i32>, ptr %Q.sroa.15.0._52.sroa_idx, align 32
  %Q.sroa.16.0.copyload303 = load <8 x i32>, ptr %Q.sroa.16.0._52.sroa_idx, align 32
  %Q.sroa.17.0.copyload313 = load <8 x i32>, ptr %Q.sroa.17.0._52.sroa_idx, align 32
  call void @llvm.lifetime.end.p0(ptr nonnull %_52)
  br label %bb41

bb42:                                             ; preds = %bb41
  %_70.sroa.0.20.vec.extract = extractelement <8 x i32> %Q.sroa.0.2, i64 5
  %_70.sroa.0.28.vec.extract = extractelement <8 x i32> %Q.sroa.0.2, i64 7
  %_70.sroa.11.48.vec.extract = extractelement <8 x i32> %Q.sroa.14.2, i64 4
  %_70.sroa.11.52.vec.extract = extractelement <8 x i32> %Q.sroa.14.2, i64 5
  %_70.sroa.20.80.vec.extract = extractelement <8 x i32> %Q.sroa.15.2, i64 4
  %_70.sroa.20.88.vec.extract = extractelement <8 x i32> %Q.sroa.15.2, i64 6
  %_70.sroa.29.100.vec.extract = extractelement <8 x i32> %Q.sroa.16.2, i64 1
  %b_2i.3.i.i = zext i32 %_70.sroa.29.100.vec.extract to i64
  %_70.sroa.29.108.vec.extract = extractelement <8 x i32> %Q.sroa.16.2, i64 3
  %b_2i_1.3.i.i = zext i32 %_70.sroa.29.108.vec.extract to i64
  %_27.3.i.i = shl nuw nsw i64 %b_2i_1.3.i.i, 26
  %32 = add nuw nsw i64 %_27.3.i.i, %b_2i.3.i.i
  %_70.sroa.38.148.vec.extract = extractelement <8 x i32> %Q.sroa.17.2, i64 5
  %d_2i.4.i.i = zext i32 %_70.sroa.38.148.vec.extract to i64
  %_70.sroa.38.156.vec.extract = extractelement <8 x i32> %Q.sroa.17.2, i64 7
  %d_2i_1.4.i.i = zext i32 %_70.sroa.38.156.vec.extract to i64
  %_29.4.i.i = shl nuw nsw i64 %d_2i_1.4.i.i, 26
  %33 = add nuw nsw i64 %_29.4.i.i, %d_2i.4.i.i
  %34 = shufflevector <8 x i32> %Q.sroa.0.2, <8 x i32> %Q.sroa.14.2, <2 x i32> <i32 0, i32 8>
  %35 = zext <2 x i32> %34 to <2 x i64>
  %36 = shufflevector <8 x i32> %Q.sroa.0.2, <8 x i32> %Q.sroa.14.2, <2 x i32> <i32 2, i32 10>
  %37 = zext <2 x i32> %36 to <2 x i64>
  %38 = shl nuw nsw <2 x i64> %37, splat (i64 26)
  %39 = add nuw nsw <2 x i64> %38, %35
  store <2 x i64> %39, ptr %_0, align 8, !alias.scope !163, !noalias !169
  %_4.sroa.5.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 16
  %40 = shufflevector <8 x i32> %Q.sroa.15.2, <8 x i32> %Q.sroa.16.2, <2 x i32> <i32 0, i32 8>
  %41 = zext <2 x i32> %40 to <2 x i64>
  %42 = shufflevector <8 x i32> %Q.sroa.15.2, <8 x i32> %Q.sroa.16.2, <2 x i32> <i32 2, i32 10>
  %43 = zext <2 x i32> %42 to <2 x i64>
  %44 = shl nuw nsw <2 x i64> %43, splat (i64 26)
  %45 = add nuw nsw <2 x i64> %44, %41
  store <2 x i64> %45, ptr %_4.sroa.5.0._0.sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  %_4.sroa.7.0._0.sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 32
  %46 = shufflevector <8 x i32> %Q.sroa.17.2, <8 x i32> %Q.sroa.0.2, <4 x i32> <i32 0, i32 9, i32 poison, i32 poison>
  %47 = shufflevector <8 x i32> %Q.sroa.14.2, <8 x i32> poison, <4 x i32> <i32 poison, i32 1, i32 poison, i32 poison>
  %48 = shufflevector <4 x i32> %46, <4 x i32> %47, <4 x i32> <i32 0, i32 1, i32 5, i32 poison>
  %49 = shufflevector <8 x i32> %Q.sroa.15.2, <8 x i32> poison, <4 x i32> <i32 poison, i32 1, i32 poison, i32 poison>
  %50 = shufflevector <4 x i32> %48, <4 x i32> %49, <4 x i32> <i32 0, i32 1, i32 2, i32 5>
  %51 = zext <4 x i32> %50 to <4 x i64>
  %52 = shufflevector <8 x i32> %Q.sroa.17.2, <8 x i32> %Q.sroa.0.2, <4 x i32> <i32 2, i32 11, i32 poison, i32 poison>
  %53 = shufflevector <8 x i32> %Q.sroa.14.2, <8 x i32> poison, <4 x i32> <i32 poison, i32 poison, i32 poison, i32 3>
  %54 = shufflevector <4 x i32> %52, <4 x i32> %53, <4 x i32> <i32 0, i32 1, i32 7, i32 poison>
  %55 = shufflevector <8 x i32> %Q.sroa.15.2, <8 x i32> poison, <4 x i32> <i32 poison, i32 poison, i32 poison, i32 3>
  %56 = shufflevector <4 x i32> %54, <4 x i32> %55, <4 x i32> <i32 0, i32 1, i32 2, i32 7>
  %57 = zext <4 x i32> %56 to <4 x i64>
  %58 = shl nuw nsw <4 x i64> %57, splat (i64 26)
  %59 = add nuw nsw <4 x i64> %58, %51
  store <4 x i64> %59, ptr %_4.sroa.7.0._0.sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  %_5.sroa.6.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 64
  store i64 %32, ptr %_5.sroa.6.0..sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  %_5.sroa.7.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 72
  %60 = shufflevector <8 x i32> %Q.sroa.17.2, <8 x i32> %Q.sroa.0.2, <4 x i32> <i32 1, i32 12, i32 poison, i32 poison>
  %61 = insertelement <4 x i32> %60, i32 %_70.sroa.11.48.vec.extract, i64 2
  %62 = insertelement <4 x i32> %61, i32 %_70.sroa.20.80.vec.extract, i64 3
  %63 = zext <4 x i32> %62 to <4 x i64>
  %64 = shufflevector <8 x i32> %Q.sroa.17.2, <8 x i32> %Q.sroa.0.2, <4 x i32> <i32 3, i32 14, i32 poison, i32 poison>
  %65 = shufflevector <8 x i32> %Q.sroa.14.2, <8 x i32> poison, <4 x i32> <i32 poison, i32 poison, i32 6, i32 poison>
  %66 = shufflevector <4 x i32> %64, <4 x i32> %65, <4 x i32> <i32 0, i32 1, i32 6, i32 poison>
  %67 = insertelement <4 x i32> %66, i32 %_70.sroa.20.88.vec.extract, i64 3
  %68 = zext <4 x i32> %67 to <4 x i64>
  %69 = shl nuw nsw <4 x i64> %68, splat (i64 26)
  %70 = add nuw nsw <4 x i64> %69, %63
  store <4 x i64> %70, ptr %_5.sroa.7.0..sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  %_6.sroa.6.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 104
  %71 = shufflevector <8 x i32> %Q.sroa.16.2, <8 x i32> %Q.sroa.17.2, <4 x i32> <i32 4, i32 12, i32 poison, i32 poison>
  %72 = insertelement <4 x i32> %71, i32 %_70.sroa.0.20.vec.extract, i64 2
  %73 = insertelement <4 x i32> %72, i32 %_70.sroa.11.52.vec.extract, i64 3
  %74 = zext <4 x i32> %73 to <4 x i64>
  %75 = shufflevector <8 x i32> %Q.sroa.16.2, <8 x i32> %Q.sroa.17.2, <4 x i32> <i32 6, i32 14, i32 poison, i32 poison>
  %76 = insertelement <4 x i32> %75, i32 %_70.sroa.0.28.vec.extract, i64 2
  %77 = shufflevector <8 x i32> %Q.sroa.14.2, <8 x i32> poison, <4 x i32> <i32 poison, i32 poison, i32 poison, i32 7>
  %78 = shufflevector <4 x i32> %76, <4 x i32> %77, <4 x i32> <i32 0, i32 1, i32 2, i32 7>
  %79 = zext <4 x i32> %78 to <4 x i64>
  %80 = shl nuw nsw <4 x i64> %79, splat (i64 26)
  %81 = add nuw nsw <4 x i64> %80, %74
  store <4 x i64> %81, ptr %_6.sroa.6.0..sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  %_7.sroa.5.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 136
  %82 = shufflevector <8 x i32> %Q.sroa.15.2, <8 x i32> %Q.sroa.16.2, <2 x i32> <i32 5, i32 13>
  %83 = zext <2 x i32> %82 to <2 x i64>
  %84 = shufflevector <8 x i32> %Q.sroa.15.2, <8 x i32> %Q.sroa.16.2, <2 x i32> <i32 7, i32 15>
  %85 = zext <2 x i32> %84 to <2 x i64>
  %86 = shl nuw nsw <2 x i64> %85, splat (i64 26)
  %87 = add nuw nsw <2 x i64> %86, %83
  store <2 x i64> %87, ptr %_7.sroa.5.0..sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  %_7.sroa.7.0..sroa_idx.i = getelementptr inbounds nuw i8, ptr %_0, i64 152
  store i64 %33, ptr %_7.sroa.7.0..sroa_idx.i, align 8, !alias.scope !163, !noalias !169
  call void @llvm.lifetime.end.p0(ptr nonnull %table_A)
  call void @llvm.lifetime.end.p0(ptr nonnull %b_naf)
  call void @llvm.lifetime.end.p0(ptr nonnull %a_naf)
  ret void
}

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x419square_and_negate_DB1a_NtB2_28___Impl_square_and_negate_D__25__impl_square_and_negate_D(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 32 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 32 captures(none) dereferenceable(160)) unnamed_addr #1

; Function Attrs: inlinehint mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare hidden fastcc void @_RNvXNvXsf_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldRNtB8_18FieldElement2625x4NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mulB1a_NtB2_12___Impl_mul__9__impl_mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 32 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef nonnull readonly align 32 captures(none) dereferenceable(160), ptr noalias nofree noundef nonnull readonly align 32 captures(none) dereferenceable(160)) unnamed_addr #2

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare void @_RNvXNvXsk_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsINtNtBg_6window15NafLookupTable5NtB8_11CachedPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtBg_7edwards12EdwardsPointE4fromB1c_NtB2_13___Impl_from__10__impl_from(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([1280 x i8]) align 32 captures(none) dereferenceable(1280), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #3

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #4

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #5

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #4

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #6

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #7

; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef, i64 noundef, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #8

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare range(i8 -1, 2) i8 @llvm.scmp.i8.i8(i8, i8) #9

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #10

attributes #0 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #1 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #2 = { inlinehint mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #3 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" "target-features"="+avx,+avx2,+sse,+sse2,+sse3,+sse4.1,+sse4.2,+crc32,+ssse3" }
attributes #4 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #5 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { nonlazybind "target-cpu"="x86-64" }
attributes #7 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #8 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #9 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #10 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #11 = { nounwind }
attributes #12 = { inlinehint nounwind }
attributes #13 = { noinline noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 8, !"PIC Level", i32 2}
!1 = !{i32 2, !"RtLibUseGOT", i32 1}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{!"rustc version 1.98.1 (48a229cea 2026-09-01)"}
!4 = !{!5}
!5 = distinct !{!5, !6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %naf"}
!6 = distinct !{!6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form"}
!7 = !{!8}
!8 = distinct !{!8, !6, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %self"}
!9 = !{!5, !8}
!10 = !{!11, !13}
!11 = distinct !{!11, !12, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %dst.0"}
!12 = distinct !{!12, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into"}
!13 = distinct !{!13, !12, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %src.0"}
!14 = !{}
!15 = !{!16}
!16 = distinct !{!16, !17, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %naf"}
!17 = distinct !{!17, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form"}
!18 = !{!19}
!19 = distinct !{!19, !17, !"_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form: %self"}
!20 = !{!16, !19}
!21 = !{!22, !24}
!22 = distinct !{!22, !23, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %dst.0"}
!23 = distinct !{!23, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into"}
!24 = distinct !{!24, !23, !"_RNvNtCsjK63O35OHGN_14solana_ed255196scalar16read_le_u64_into: %src.0"}
!25 = !{!26, !28}
!26 = distinct !{!26, !27, !"_RNvXNvMs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_13ExtendedPoint6doubleB1c_NtB2_15___Impl_double__12__impl_double: %_0"}
!27 = distinct !{!27, !"_RNvXNvMs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_13ExtendedPoint6doubleB1c_NtB2_15___Impl_double__12__impl_double"}
!28 = distinct !{!28, !27, !"_RNvXNvMs7_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtB8_13ExtendedPoint6doubleB1c_NtB2_15___Impl_double__12__impl_double: %self"}
!29 = !{!30}
!30 = distinct !{!30, !31, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!31 = distinct !{!31, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!32 = !{!33, !26, !28}
!33 = distinct !{!33, !31, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!34 = !{!28}
!35 = !{!36}
!36 = distinct !{!36, !37, !"_RNvXs19_NtNtCsgxBkk5gSRhY_4core3cmp5implsaNtB8_3Ord3cmp: %self"}
!37 = distinct !{!37, !"_RNvXs19_NtNtCsgxBkk5gSRhY_4core3cmp5implsaNtB8_3Ord3cmp"}
!38 = !{!39}
!39 = distinct !{!39, !40, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_: %_0"}
!40 = distinct !{!40, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_"}
!41 = !{!42}
!42 = distinct !{!42, !40, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_: %self"}
!43 = !{!39, !42}
!44 = !{!45, !47, !48}
!45 = distinct !{!45, !46, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub: %_0"}
!46 = distinct !{!46, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub"}
!47 = distinct !{!47, !46, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub: %self"}
!48 = distinct !{!48, !46, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub: %other"}
!49 = !{!50}
!50 = distinct !{!50, !51, !"_RNvXNvXsg_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_11CachedPointNtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3negB1c_NtB2_12___Impl_neg__9__impl_neg: %_0"}
!51 = distinct !{!51, !"_RNvXNvXsg_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_11CachedPointNtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3negB1c_NtB2_12___Impl_neg__9__impl_neg"}
!52 = !{!53, !45, !47, !48}
!53 = distinct !{!53, !51, !"_RNvXNvXsg_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_11CachedPointNtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3negB1c_NtB2_12___Impl_neg__9__impl_neg: %self"}
!54 = !{!55, !57, !58, !45, !47, !48}
!55 = distinct !{!55, !56, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %_0"}
!56 = distinct !{!56, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add"}
!57 = distinct !{!57, !56, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %self"}
!58 = distinct !{!58, !56, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %other"}
!59 = !{!55, !57, !45, !47, !48}
!60 = !{!61}
!61 = distinct !{!61, !62, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!62 = distinct !{!62, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!63 = !{!64, !55, !57, !58, !45, !47, !48}
!64 = distinct !{!64, !62, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!65 = !{!66}
!66 = distinct !{!66, !67, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!67 = distinct !{!67, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!68 = !{!69, !55, !57, !58, !45, !47, !48}
!69 = distinct !{!69, !67, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!70 = !{!71}
!71 = distinct !{!71, !72, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!72 = distinct !{!72, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!73 = !{!74, !55, !57, !58, !45, !47, !48}
!74 = distinct !{!74, !72, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!75 = !{!57, !58, !47, !48}
!76 = !{!77, !79}
!77 = distinct !{!77, !78, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_: %_0"}
!78 = distinct !{!78, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_"}
!79 = distinct !{!79, !78, !"_RNvMNtCsjK63O35OHGN_14solana_ed255196windowINtB2_15NafLookupTable5NtNtNtNtNtB4_7backend6vector4avx27edwards11CachedPointE6selectB4_: %self"}
!80 = !{!81, !83, !84}
!81 = distinct !{!81, !82, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %_0"}
!82 = distinct !{!82, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add"}
!83 = distinct !{!83, !82, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %self"}
!84 = distinct !{!84, !82, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %other"}
!85 = !{!86}
!86 = distinct !{!86, !87, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!87 = distinct !{!87, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!88 = !{!89, !81, !83, !84}
!89 = distinct !{!89, !87, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!90 = !{!91}
!91 = distinct !{!91, !92, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!92 = distinct !{!92, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!93 = !{!94, !81, !83, !84}
!94 = distinct !{!94, !92, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!95 = !{!96}
!96 = distinct !{!96, !97, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!97 = distinct !{!97, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!98 = !{!99, !81, !83, !84}
!99 = distinct !{!99, !97, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!100 = !{!83, !84}
!101 = !{!102}
!102 = distinct !{!102, !103, !"_RNvXs19_NtNtCsgxBkk5gSRhY_4core3cmp5implsaNtB8_3Ord3cmp: %self"}
!103 = distinct !{!103, !"_RNvXs19_NtNtCsgxBkk5gSRhY_4core3cmp5implsaNtB8_3Ord3cmp"}
!104 = !{!105}
!105 = distinct !{!105, !106, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_: %_0"}
!106 = distinct !{!106, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_"}
!107 = !{!108, !110, !111}
!108 = distinct !{!108, !109, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub: %_0"}
!109 = distinct !{!109, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub"}
!110 = distinct !{!110, !109, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub: %self"}
!111 = distinct !{!111, !109, !"_RNvXNvXsi_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB8_11CachedPointE3subB1c_NtB2_12___Impl_sub__9__impl_sub: %other"}
!112 = !{!113}
!113 = distinct !{!113, !114, !"_RNvXNvXsg_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_11CachedPointNtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3negB1c_NtB2_12___Impl_neg__9__impl_neg: %_0"}
!114 = distinct !{!114, !"_RNvXNvXsg_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_11CachedPointNtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3negB1c_NtB2_12___Impl_neg__9__impl_neg"}
!115 = !{!116, !108, !110, !111}
!116 = distinct !{!116, !114, !"_RNvXNvXsg_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_11CachedPointNtNtNtCsgxBkk5gSRhY_4core3ops5arith3Neg3negB1c_NtB2_12___Impl_neg__9__impl_neg: %self"}
!117 = !{!118, !120, !121, !108, !110, !111}
!118 = distinct !{!118, !119, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %_0"}
!119 = distinct !{!119, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add"}
!120 = distinct !{!120, !119, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %self"}
!121 = distinct !{!121, !119, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %other"}
!122 = !{!118, !120, !108, !110, !111}
!123 = !{!124}
!124 = distinct !{!124, !125, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!125 = distinct !{!125, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!126 = !{!127, !118, !120, !121, !108, !110, !111}
!127 = distinct !{!127, !125, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!128 = !{!129}
!129 = distinct !{!129, !130, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!130 = distinct !{!130, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!131 = !{!132, !118, !120, !121, !108, !110, !111}
!132 = distinct !{!132, !130, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!133 = !{!134}
!134 = distinct !{!134, !135, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!135 = distinct !{!135, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!136 = !{!137, !118, !120, !121, !108, !110, !111}
!137 = distinct !{!137, !135, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!138 = !{!120, !121, !110, !111}
!139 = !{!140}
!140 = distinct !{!140, !141, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_: %_0"}
!141 = distinct !{!141, !"_RNvMs2_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable8NtNtNtNtNtB7_7backend6vector4avx27edwards11CachedPointE6selectB7_"}
!142 = !{!143, !145, !146}
!143 = distinct !{!143, !144, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %_0"}
!144 = distinct !{!144, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add"}
!145 = distinct !{!145, !144, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %self"}
!146 = distinct !{!146, !144, !"_RNvXNvXsh_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsRNtB8_13ExtendedPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB8_11CachedPointE3addB1c_NtB2_12___Impl_add__9__impl_add: %other"}
!147 = !{!148}
!148 = distinct !{!148, !149, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!149 = distinct !{!149, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!150 = !{!151, !143, !145, !146}
!151 = distinct !{!151, !149, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!152 = !{!153}
!153 = distinct !{!153, !154, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!154 = distinct !{!154, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!155 = !{!156, !143, !145, !146}
!156 = distinct !{!156, !154, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!157 = !{!158}
!158 = distinct !{!158, !159, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %_0"}
!159 = distinct !{!159, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle"}
!160 = !{!161, !143, !145, !146}
!161 = distinct !{!161, !159, !"_RNvXNvMsb_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx25fieldNtB8_18FieldElement2625x47shuffleB1a_NtB2_16___Impl_shuffle__13__impl_shuffle: %self"}
!162 = !{!145, !146}
!163 = !{!164, !166, !168}
!164 = distinct !{!164, !165, !"_RNvXNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtNtBg_7edwards12EdwardsPointINtNtCsgxBkk5gSRhY_4core7convert4FromNtB8_13ExtendedPointE4fromB1c_NtB2_13___Impl_from__10__impl_from: %_0"}
!165 = distinct !{!165, !"_RNvXNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtNtBg_7edwards12EdwardsPointINtNtCsgxBkk5gSRhY_4core7convert4FromNtB8_13ExtendedPointE4fromB1c_NtB2_13___Impl_from__10__impl_from"}
!166 = distinct !{!166, !167, !"_RNvXs1_NtCsgxBkk5gSRhY_4core7convertNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwards13ExtendedPointINtB5_4IntoNtNtBI_7edwards12EdwardsPointE4intoBI_: %_0"}
!167 = distinct !{!167, !"_RNvXs1_NtCsgxBkk5gSRhY_4core7convertNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwards13ExtendedPointINtB5_4IntoNtNtBI_7edwards12EdwardsPointE4intoBI_"}
!168 = distinct !{!168, !167, !"_RNvXs1_NtCsgxBkk5gSRhY_4core7convertNtNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwards13ExtendedPointINtB5_4IntoNtNtBI_7edwards12EdwardsPointE4intoBI_: %self"}
!169 = !{!170}
!170 = distinct !{!170, !165, !"_RNvXNvXs3_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6vector4avx27edwardsNtNtBg_7edwards12EdwardsPointINtNtCsgxBkk5gSRhY_4core7convert4FromNtB8_13ExtendedPointE4fromB1c_NtB2_13___Impl_from__10__impl_from: %P"}
