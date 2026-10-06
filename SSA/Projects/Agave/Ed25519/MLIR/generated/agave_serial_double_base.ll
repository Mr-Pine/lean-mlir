; ModuleID = '/tmp/ed25519-rir-extract/final/generated/agave_serial_double_base.ll'
source_filename = "solana_ed25519.e5f703a99ceb696b-cgu.0"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%"backend::serial::curve_models::ProjectiveNielsPoint" = type { %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51" }
%"backend::serial::u64::field::FieldElement51" = type { [5 x i64] }
%"backend::serial::curve_models::AffineNielsPoint" = type { %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51", %"backend::serial::u64::field::FieldElement51" }

@alloc_d6091242425a18f93aa551ed73483e0d = internal unnamed_addr constant [40 x i8] c"\01\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00\00", align 8
@alloc_8241d8c786577e4be83f121c84457b0a = internal unnamed_addr constant [14 x i8] c"src/window.rs\00", align 1
@alloc_a8fabae8f73f66aef6660ad7c9447c5d = internal unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_8241d8c786577e4be83f121c84457b0a, [16 x i8] c"\0D\00\00\00\00\00\00\00\DD\00\00\00\09\00\00\00" }>, align 8
@alloc_f7b128ba219626851d37833adc9e2368 = internal unnamed_addr constant <{ ptr, [16 x i8] }> <{ ptr @alloc_8241d8c786577e4be83f121c84457b0a, [16 x i8] c"\0D\00\00\00\00\00\00\00\0B\01\00\00\09\00\00\00" }>, align 8
@alloc_eaf951945d20f8425ce4c25607db196f = internal unnamed_addr constant [7680 x i8] c"r;\8C\F5\C6\93\0C\00\F6%\C3\81q\DF\08\00\B6L>\0B\0B\F5\08\001L\A4\85\932\05\00K=\A3\D3\F9|\08\00>\91@\D7\059\00\00\A2s\D6\17(\BA\00\00|\E6\F4'(>\02\004\1A\C2\E0\D23\01\00\81\8F)\F9\D2O\04\00h\AAz\87\05\12\01\00y\D5\93X\95y\04\00\A0g\9B0f\0D\05\00\EE\E5\BE\0D-\D4\02\00\C6\F0\89\B6\17\F1\06\000\97\EEL\A8\B0\05\00\E4Uq\C9\10\1D\06\00\10j\09\C8\9C\05\04\00O\01\A8\8D`z\0C\00\0E\A8\B9\E1d\A1\07\00e\D2\FC\A4\E8\1F\01\00\CC\AAO7\B8\BC\07\00OM\EF\F4Z/\05\00\10\8D\F9\98@1\05\00\BDUuX\91\AB\02\00\89\D8\D0\0D?\93\06\00\95BL\BB\86C\04\00\8CPb1m\CB\03\00\C6\A2r\B8hc\02\00\9B+\F1j\82\A2\05\00 \BB\A5\08D\BC\02\00BT\A0\DD\EBx\08\00\22A5\12\B1\FF\0A\00,\86\F5\8D\EEu\0B\00\1Fn\14\CF\\\94\0A\00\BA\D6G\A4\C3\82\01\00\F2\EF6\E5d)\02\00S\00T\1F\82\92\01\00\\\8Ex\9E\F1\F9\02\00\B5\B1>\E7\A7T\01\00\85\82*\81\F1\DB\03\00\97\97?\BA\17\FA\00\00 8\9C\B4\9C\F6\06\00\8D\85\B3\0DZM\03\00\BB\B3\96\E6\AB:\04\00\BF\A3N\94\D0\\\0A\00bM\1A\B8sV\07\00\D4\C0\D1%\B9P\09\00\13A)\D98?\09\00\C8\83\92\A6\BEa\04\00\B1!2\AA\9A,\07\00M\F7tDwg\02\00\85\80\B2\E9\B0d\00\00\C9';\F5N\F0\03\001\E5\D2\D5\ED\D6\01\00\A2\B3\B8\01\C8m\03\000^\93\D4\A7\E0\00\00}\0D\CC\CE\B7\DE\01\00,\DD N\A9S\00\00\F9\A0\C6\B1\FB\A9\07\00\1Cc\A8\A6\8Ag\06\00e\B3\D8\887\EA\05\00yB\99\D6\D6\1B\0A\00\E2\E4\19Y\E7\AC\07\00\D7\AD8\D3\9EK\0B\00d\80\9D\03~!\06\00m~3\08\A4\DE\06\00\06\82b\12\C1z\05\00s\04\E3e\CBG\06\00\C9\AD\1F\A5\05\9C\04\00\1B\AFE\90\BF\E8\04\00\D6\E0E:\E3\14\05\00\0F\FE\8B[<S\07\00\C9\14~{U\83\05\00\08\B0! \17<\07\00\DE*\80\8A\84\00\0F\00\F6\E5\C4\05F\E0\09\00\FAg\97\1B\D0\C0\05\00\8B8B\9F\88\D7\07\00\D8F%\AEZ'\04\00HC\86I\02[\07\00+&p\10\E1.\05\00\CDZ\FBT\AE7\02\00\B5\AA:\D0\D1\BF\03\00\\\9D\02\98\B5\8A\01\00\E9\89`\FD\C5,\03\00\05\9B\94\\P&\04\00\D2z\0C\88\18j\04\00\DA\CC\88\18\22\A4\04\00\DFS+Re\DC\03\00m\7F\00\A2\22\C2\08\00\EDw\DB\9B\B7V\0B\00\CD\12\FE\1E\E8\1E\04\00}\09\07\BD\A9 \09\00n4\EC~\FD4\02\00\93\BF\7F2;\01\07\00\0Dj\ED\EDn3\01\00\AF\F3\BB\A2e\B5\02\00U\19Y\89\CES\02\00\02v\D1\82x&\00\00x\A3.s\19\A1\00\00l*\8E\BA\F1;\06\00\9A\DF\90\CC\94\9F\06\00H\FC\9Bw\D11\04\00\97\A0\DAo\BA\97\04\00\A0\EA\CF\13\03\CC\06\00\99\A4\8D\84\13\A3\09\00\09#\19BS\CB\07\00`\FD\DE\DE\96\95\03\00\DE\12\7F\91\22\1E\06\00\0B\CF\8CF\86\CD\03\00\81\C0\1A\22S\85\04\00n\0ANKF\C9\06\00\03\04\18\84\BA_\07\00\05\8D!\D4\\;\04\00\16\B5\D0\9B/v\02\00\B3\CB\DD\FB\E7\C6\01\00\BD\E2\AC\C3\09Y\07\00\C9>-\97\01!\04\00M\AE\10\12\D6\11\05\00n\9D\0E\95\EFv\06\00X\F2\89\E0\1A\B8\09\00\82\18\95\22I<\06\0072\9BM\D5\F1\0A\00\84\DBM\92%\D3\0E\00\87\DE DH\86\03\00\02\81\B6]\B2\D6\02\00\C0s(\96\B4P\06\00\94\13'\FD\1C\08\04\00\82$\FE\E6\7F\1A\07\00T\C8\C8\A5\B8\82\01\00\8Em@\E5\CB?\07\00Q\F4\CF04\DE\05\00A\8C\ACg\B9T\05\00\EEYeKlt\04\00+\9A\C6m<{\07\00n\FA\C2>\F1\ED\04\00\C8\EA{\D7Z\E8\0C\00\D9{\8E\B2\A2\DB\07\00\E9O\E3\1D\A5\C9\05\00G\11td\C8F\05\00\90&\09\99\DF\A1\03\00\BB\D6\F4\C9\8C\CA\01\00\03;\CD\C9\7Fk\03\00^\DB\974f\19\02\00g\0E\F1y\CF\F1\00\00\A2~+\0A\CB<\04\00jw\FF\DF\89P\00\00\88\8B\D3\E1\84\DD\01\00\22\08\C6\03E\80\04\00\B4\7F\A3,\D0\9E\0C\00\83x\95\B5\C2t\04\00\83f\81\8E8\B8\05\00\E4k\B7T\C4\B6\0C\00\05eQ\8A9S\0D\00u\D16:\D2!\00\00mG\C6s3\FD\04\00*\D0\EE\1E)\0E\02\00\10r.\CF./\06\00\E4\8D\85\98\E0q\07\00\DF\1EEx\D2\F5\02\00Bs\993\B10\07\00ui\EB T\96\06\00\CF\16\A5\BF\A3\08\03\00Z\FFh\1D\ED\A5\05\00\83\0E\15\FE*\12\0D\001\02\BBf\C9\AF\04\00h\82<\83x\C4\01\00\8F\14\FC\C39x\09\00\F8\8B}\89\CBJ\04\00YsRX\C5\E0\05\00\\\D7\AFs[9\03\00p\B9\E4\A4\AFr\00\00m\0F\9E2\14\22\06\00\FD\FE5\01\B6\19\00\00\83K\13^\14h\00\00\CC\C3\82\09\86\E4\01\00\99\D7\13_\FBh\00\00~TD7(\C9\07\00\D2j\DE\9F\C4P\01\00%\11G\09\95\F2\03\00\CF1\CA\B4\EE)\07\00\BC\BFu\B5\22\9C\06\00\12\E2\BCW\08\91\0C\00\98\BBu\A0\B5\B2\0E\00h\A8\DC\9C<\86\01\00\09\17Z)\0Ew\03\00\13\FD 7Z\D8\00\00\06\ABq\1F\FF\E0\05\00_\E0\91wm\8A\07\00v\B9\A0GKp\07\00\17\AB\1A\E9\82\AE\02\00\CD\06\98B\D6\0B\05\00\EA\D8\8F\15U\80\06\00U\AD\C4\FF\C7%\07\00\B2\99\CF\D1\15g\02\00\88\9C\A6AT \0A\00SK\CD}BH\04\00\C5\BD\8A\E8\91\D1\09\00\1E\CBw\92\CC\94\07\00\C0\98\D0\1C\F7+\00\000\D2l\CC\AB\9D\04\00\B2\05\F93e\0A\04\00\A4\B8.\AC\EFs\05\00_\85_bT\CD\04\00SP\AC\C2&\C4\06\00^\09K\CE^\A6\05\00\B6k\F2\86@\C4\00\00\85x\19h\95B\07\00\C8\FC\B6W\83\00\07\00\EE>w8'g\08\00pa\9Fy\BFR\07\00#3\E3\DA\A6\B4\06\00\DC\D1\EA\96F\B5\07\00\D0\1A\85\E9\F7n\08\004JX\82\BB\9F\03\00\03z%\8FVz\04\00\91\AD\1E\09\88M\01\00$\CE\B1\18[\14\02\00m\9Df\A3\92:\01\00\E5}W\C0\1Cw\03\00R\99\8B\BB\06\CA\03\00\90\03\D5\C5\81\0B\00\00\EC\80\074\125\04\00\AF\A2\F8\DD\96\C2\03\00\13\A7\14\D9\F9\15\05\00\D5U\22\FF\911\07\00\EF\BD\A4\C2\\O\0D\00\CE\8B\11\FCW\DD\03\00\C7\9049\9D\A9\07\00A%\1F\BB.M\03\00\9D\FF#\B7\15\E8\00\00CT\E2\16\B4\86\02\00\E8\BE\D18\FE\BD\00\00wt\00\C7\92\A8\00\00\E8\A3\BD6$\ED\02\00\EA\91\F2\00\FD*\00\00!\A3\DE\81s\BE\00\00\93\B1\B2\D4R\E9\03\00/0(-v\86\02\00\12[\E3<\096\08\00\CE\E9RuM\B6\0B\00_\84\0B\FE\E0\1E\07\00\E5i\C9`\06\9D\06\00\D9\A9F\A0\1D/\0B\00\BD\F5.\CE+\8E\05\00\8Ao\8C\F7\E8\8C\06\00\B2a\92\E3&\EE\06\00\9D\CF\0B\A5\0A=\03\00\17o=*oh\07\00j|Ym\A6\12\05\00Qu\A5p\9A`\00\00LF<\8A\C0&\00\00\E19\EE\C8\1FS\04\00\D2\9A\8A_0a\05\00\BE\AE\92\EC\8D\97\0C\00\00\A2|\AE\ADi\08\00T\0F)#\E9\1E\09\00k\91\8D\89A\96\06\00\D45>\C5\AE\0A\08\00\D5\C0\B0\E7(\CC\02\00\E4l\8A\EB`{\07\00\A6w\C2\85)\04\04\00\EB\D3F{e6\06\00|\C5\F2\AE\A10\00\00\AA\D2:\00s\F7\01\00v\0F\C1,d\05\00\00\A6\FC,\F8H;\00\00)C\EE\10<@\02\00e@\C2\C1\E9\0B\02\00\A6s\96$\D8\87\03\00*|\92\DC\A8\BE\0D\00\EF\0Ee\D5\8E\BD\05\00\E1@\CD?\0E\EF\08\00\AB\F0a3\ABP\07\00`^\02\E2J\E4\00\00\1C\04'\97{\F9\05\00\EC\EC\C0r4h\05\00|\CE\B1.\88\88\01\00~\06E\C5d\97\06\007\10\F8\A2\832\02\00\D1#~\F9\AFw\04\00h\BB\BC\8D\95\B8\00\00\D6\AD\E8\97[ \00\00up\FB\B3\96O\05\00f\92f)\04\F2\05\00\F5AI\AE\AF\8F\08\00\87v\EB\C4\83]\09\00EA\CA\9E7\CF\09\00t\BBR\9C\FE\D7\0B\00\CD\1E\B1\16\C6\AF\05\00\EF\22\8F\ECJ\9F\03\00.\D9%\16\9E\B3\03\00s\88P\D4[\F8\05\00]\E8\FB9h\8E\07\00k\85\B87\F7-\03\00\06N\F1B\83`\00\00uA\D7\89x\96\03\00P\A5\FB\07\19!\01\00\88\005\8F&\0F\07\00G_\80\B1\83E\06\00\D0,\83\AF\1B,\0A\00\16\D7\D4\1B\C02\09\00\8E[\A7\C3\F4\EC\04\00\88\AD\CFE\D3\C0\07\00U\F3\DCp \11\04\00d\E4\22\9C\FF\DC\07\00%3\E0`\DAJ\05\00\9Av\EF\8E\D9\\\02\00\8C\9B\03l\E5\04\04\00\8A3x\8CK\1F\07\00#+\BC\16\FC,\06\00\AA\D9\80\12\F5|\01\00Z\A9 ^\AE\BB\03\00\EC\AAbGu\0D\02\00E\B7;\C7o\C3\07\00\D1Ks\97\C7\A6\04\00\0E\95\B3\8A$\EF\08\00\C7>\A5\C9T1\0E\00\ED<o\E4\F1\B8\0A\00C\F5\B95\B1\FE\04\00\AE\93\AD\92\D1;\06\00\F7\CD\12\A6.N\04\00\AB\83\15\99\F4p\06\00\B4\90\87\DA\8A\8B\03\00]\F9Q\DF\9CJ\00\00\B8\96\D5\FBc\D9\05\00J\E5\ACh\9B-\02\00\99\C56\88\8E\A9\04\00\A1\EB,\B3\AEI\00\001y\FCu\0B}\08\00Iu\BA\E4Lo\01\00I\BE?\C0\E4\AC\05\00\9C\15*\C1\0E~\0A\00f\0FS\17\EE\95\07\00~\FE\DCc<}\06\00\EE\1A\C8\AD\F0\12\01\00eq\82L\F0=\05\00\F00\B43[\FE\02\00b\8D\0C^f\1C\05\00\81\BD\ECR\0A[\02\00\A9\E4\FC\95\06\DC\05\00}\04u\C5(\B9\03\00\E5\86&Q\F3;\02\00T\DCI\BF\19\CD\06\00\86\C3\AFe!a\06\00\FF\03b\A3\1A\17\01\00\AA\A8 \A8.d\0A\00\0F?1{\BB\F3\09\00\E3)t:\1B\E0\05\00\A3\9C\17R\90a\07\00\D0\AF\F0\93e\C1\00\00(t\\y\C4e\02\00BT]Q@\1C\03\00.\0B\B4=\0FR\07\00\A1W\93\D3\E3\0B\05\00\B6\A7\94\D23\AB\03\00\B3\EDY\BAy\C4\04\00o2M\18\0D\C3\04\00<\EF\CC\C9\92\10\07\00\BC\1D\05t\AC\D8\03\00\AD\D0C\F5\B6\0A\09\00\8F\DA\0F\AC\F3\D0\0D\00\E3\E5s%\1D\EF\05\00z\13\B7[:\17\0C\00\8C\91d\03?R\00\00{\8Acm\F5\87\06\00\13\D0\8A\92\96\07\02\003O\A5\05\84\D3\05\00W\02=\B0\15\EA\00\00\8A!\F9\F01n\05\00\F8\02\E1\88_c\05\00\B8\A5i\D9\C5\CB\02\00z4\8B\C9\FB3\05\00\E3\A4\14VV\FC\05\00\8E\98\90w\E6\E1\02\00\12I\E4\9A\8B\E3\09\00SV\07\B4\FBH\06\00r\CD@\D8\F1\8D\0A\00e\D4\09tL!\03\00\E5zm\C4\0DW\06\00m\E2\91\1B\9F\8A\01\00\ABB?\18\B66\04\00\98\81O\AA\ACP\05\00T\C4\14\C4\11'\06\00p\17e\06t\82\01\00e\C2\86\F2D\D1\04\00\81\92\EE\F0\88t\01\00\0Cv\\\DBl\9E\01\00\B8\ECs@\A9\BE\05\00\F8\D2C\F3c\CE\08\00\8D6\1E}\A8\E0\09\00\E9\9E\01\BC\EDE\08\00\D0\D0(\ED\9A\97\0E\00\1AO\94\85\07\AD\04\00\E4\9B\C8\12\09\BF\05\00\83\8C\F3\CA\AD/\06\00,\CE\B3\96\C1^\02\00{\01O\FFUv\07\00a\8F\14\\\CD\AA\03\00\01\831\C34;\06\00\B1\D0\04-\E6\E0\00\00\01gr3\A2v\06\00i\97-\04\9A\9E\02\00(\90\1D\CB\F0\AF\03\00\F24\C5\F4\0BC\06\00DrP\E4\C3d\02\00p\92\A3\19\9FL\07\00G\BC\99\F7\84?\07\00\99\BD2\F7\F9\CC\0A\00^@ :\EB\C7\05\00\F80\D9\AA\B5\FD\05\00G\8C;\E6W\A7\04\00V$\97\92\94\8E\02\00\D2Lo\E8\E7\10\01\00\E4\F5\03\D6\9E\D8\00\00\F8\8A\01\04\16\1E\05\00\18\22J\DC\EE\B8\00\00\D0\84\93\8B\A9\1B\05\00\93\96\0B~U\\\00\00\B0\0E\C2\89\B0\BB\06\00\EE\9E\0B\FBA\DF\06\00o\E1\87\ED\87\10\0D\000\A7\9F\\\DB\02\09\00`\18\84\F0\FE\89\02\00o~\C9\1F1\CE\01\00\1F\DB\B5??\02\06\00\98\FC\E8u\97\B4\07\00EP\BF\ADp\AD\03\00\98\FEx\C1T\E1\06\00\BF\9A\D6\FE6c\01\00\EC\F9)\B9f\F0\04\00\93[l\9E\FF\E9\04\00\BA\B2K\BC\89\8C\01\00\CA\95*d\BF\AF\06\00\B9\A8\13\F9pP\0D\00\BB+\AC\9Eae\07\00Yt\F4%R\AB\0B\00G[\AB\14\EDl\07\00\01\B8\ED<\09,\09\00\C1\D2\F5b\0C\DE\00\00\B5Os\CF\01\96\04\00\F6\F0c\82\C3\B5\06\00\06m\B5\F5>b\04\00\03\95\1B\85K\DB\00\00\0F\19\B8\08\93\7F\04\00\82\1Fb\\#\14\04\00vZ\1A\F4_\1F\03\00m\B9\AAsgs\06\005f\9Cy\A8:\03\00\9El\15\FC\88\F5\08\00h\F0\A4MAc\03\00\EA\8A\B6\D9j)\07\00C\AE\16\13q\D3\04\00X\8D\1C\0C\CD\12\0A\00\F2\\\08\BD\1E\F5\07\00\E1\F5\E3g\FA,\01\00j\D4\E3\F1\0C\80\01\00\A8\F0_a7C\05\00!\8E\9E\F2\C63\02\00\81\C7\18\7F\10\D5\04\00^\1A\A5\D3OJ\06\007\BBH\04\CD\F4\04\00\1E\15C\85\D3q\06\00\14\19\91xw\DB\01\00\B6\1Ap\DDiG\09\00f\B6\B4\F19\83\02\00{\E3\8AK!\AB\04\00\FE\B0\A0\EF\0A_\0A\00\D1\17\A0\A8,\AE\07\00o\C2k|9R\03\00\BE{\22\A0z\8A\01\00\8B_\EA\C1\8C\E6\05\00_\1Dz:>\FE\06\00*n\D2z\D9\1A\03\00b\B9 \09\ED\17\00\00\FD\B6S;\E3\87\01\00c\14z\90)X\05\00\92\A7\E0H\F2A\06\00\22f:\C5\1F\ED\01\00--\09\1C\A6B\06\00\7F\D1\11\E77\19\0B\00!A\CD\EDK\DC\0C\00\DE=\8B\0C\9FV\0A\00\A1z\A5d\D6\03\05\00n\F2\89M\8E\E9\01\00\97\FE\FC\16\AE\10\05\00|\0B\CEr\11\17\02\00\826\BF\ED\91Q\05\00\C0\8B\F26+\B1\05\007\15\A9\90[9\03\00CY\BE\FC\E6\F9\06\00\0F\EA\E6\EA/:\02\00\06\1F\01\95\8Cq\04\00\1F\9A^h\06i\03\00\1Dx\D8O<\BE\04\00\89\8A\FCjqB\0A\00v<\BF\E4\F4l\09\00^2\F7\93\F5\D2\09\00[\80\04\CF\DCU\03\00H\9Ei\B8\D8\0D\01\00c\8D\8F\EB:F\07\003\C0\91n\85`\07\00U\E0\8E\00+\CF\00\00KG\08'\11\B1\05\00\DBu<\CBM\98\05\00w\F9\CF\CA\FE\EA\04\00{\D9~X\06f\01\00[\C4Z\9C\D8\B2\07\00\E4Z\22{X\84\05\00\C3~\A6f\0F\C1\05\00\0A\89\F82r\99\05\00\85\AD\13.\86\C8\0A\00\BF\E9\FF\A7E*\06\00*\98K\BA'^\08\00\A6W/\F1c\A3\03\00r\C6}\85wf\03\00E\D7P\DDn\01\06\00T\04\0C\A4\EDw\07\00\11}\B8\8F\91\D8\03\00M\86Z\1E}\A6\06\00\E0\C7\10B\C5\1B\06\00\B6\BA\96?\AB\A0\05\00uG\88\B05\ED\02\00\A5dMB\F3\F8\07\00\AF\86H\B2\07H\02\00cO\BC_\88\D8\0B\00\B3#U>\95\15\01\00=\D2\18\A9\D72\09\00\0E1\A0\CBU\E7\07\00\D1Ny$6)\06\00\DAa\D1\1E\1E\ED\00\00\C3o\B8\0F\F3\8E\00\00g\0B\FF~Ub\03\0052\9C\05\A7\CA\00\00#0\1AvRO\04\00_\13\CD\DE\D2\04\01\00j8\99fe\91\07\00~\06z#q\18\01\00\B3p\EE*lS\04\00\C3\B9\CC!\F3\EF\0B\00\9B\11\F7*\A4\8C\06\00\FD\E2h.Z\8C\05\00\87\F6/0\EE\D9\03\00I\A4\\\0F]\A1\06\00\FA\B7\9DY\02\A3\01\00\03\DCD\F8\05\FE\06\00\9C\D3\BA5\06\C4\01\00\7F)\FC\0D\FF8\02\00G\BAA\80\DF\BB\07\00\D5\A8\BF\09\F1\E1\05\00\C1\11\9E8D<\07\00\AB\93pc!^\02\00\1B\CD\9C\97}\BD\05\00\CD5@m \\\05\00%v\DE\90\AD\FA\07\00Da\1C9\86\C2\03\00F\9F\08.g)\05\00\10\AE\ED\CC\87\12\0E\00p\EE\229k\CD\05\007=D\B8Y\81\03\00*.\9F\EC\D9Z\05\00m\CF\0A\F0{z\04\00\06`\0A\CE,\\\07\00\E9t\CD\8B\FCx\02\00\C7\EB3\D6\94\A9\04\00\07\DE\F7\F4F\CF\05\00ID\84\AFP4\03\00pO\18\FA)\14\02\00\88\AB\91Rah\04\00o\EBL\D5Q8\08\00\87\E5l\AD\BFY\05\00\A7\88\B4\AF\E4\89\03\00\8C\A9\90V\FAB\02\00\8985/>R\05\00\D2\EF\A5T\9C\09\01\004\EE\F2\F3\0A\1E\04\00\1A\14\D7?\EFS\07\00\89\C7Y\0C\EE\E9\06\00N\89\A5f\DB6\06\00\DE\D4\D0{nS\02\00_S<~\B4l\05\00\96\84=\D40!\07\00Y>\D1zD\CC\07\00\B0YU\F6\8C(\05\00\09\88\D9\F0)\B6\0A\00\F1!\CE\E1\AA|\0A\00\EB\C7\F2\EF\EB.\09\00\A3\C4'\F7/\E9\08\00#E_\C8p,\09\00\9B(\97\0A\C5\C8\05\00R\F6G%P]\07\00\AE\FAc\A5$\DA\05\00\07cy\EB6\0A\03\00d\A9U\B5\01?\06\00\7Fv8\E5\A5\BD\05\00H\8D\19,a\FA\00\00L\A6\80E\CDT\03\00\EA\B4\CFI\9E\AA\04\00b\AB\16T\167\04\00\86\AD\FD\DD\FB\B1\05\00:\BC\F1\CE\96\\\07\00\FE\06\B6~t\03\06\00\CC\8C\0C\BC\B5\DB\08\00q\B9\F1\85\E9o\04\00\9AK\E66(\0A\00\00&,N\A7\92\1E\02\00\93\DA@\D5\91\CD\07\00\A3\A7\912B\1E\01\00\DD\C2r\DCF\EA\03\00\A7\DF\E2\88\85\01\05\00\FES\DD\EB\A0?\00\00\D0\E7\9C\95\D3q\02\00\ECK/\075\A7\04\002\F4}\CA\B0\88\00\00\C0l\FE\FET\0E\07\00\0C\82\B2\A3\1Cu\02\00u\EE:|\8F\D6\04\00\FA\11\87O\FDI\0C\00\ED\F5\0ApU\C7\03\00\9D\AAT|3E\04\00\C8\A4\F9m\C8\CF\07\00:B\DBamF\04\00J\EB\D0\C7\F6\BC\01\00\E1\10aT\B0\D5\07\00\96\05\C7\D7\96:\07\00\13o>`_a\07\00\F9\E3\AB^\03\87\00\00j4#\0B\B2V\05\00w:KV\\\AE\01\008Y\02\03L\AD\01\00A\9BpK\8D\8F\02\00\9B\EFO\90\8A\17\0A\00\03\E0s\80\A21\0B\00\91\8D\19A\A6\01\0A\00[\8Dp>\86\E6\00\00\B1\BFT\B6\14\99\00\00\B7\96'Av\D1\01\00\0Ft>\98\07\C3\03\00\F1\8A\81\1E\CF\D9\05\00+Y\A1\E2;\1D\02\00{\EB\83\18WL\05\00\AAn\AF,1\09\01\00n\9E\A4\BC*\93\05\00\E0\1F6\0C\0A\AA\03\00\93\F6\DF\08\E5_\0C\00\82\B2q\F0\C1l\05\00J@\1F\13\95\DE\09\00\AD\EEt\93#\A0\01\00 \8Bp\0F\19\E6\03\00.\EFI\E1!n\04\00\CF -\CE\00J\00\00\04\833\C2\CC\E2\01\00O\AE:U\D8\94\00\00\1A\0D#\9F0\EE\06\00w\B8g\AC2\AE\00\00)'A\D8\8F\EA\01\00\8A\88\E8\B5&\A1\03\00\D8{\12\BA\B0\A5\03\00\1DO6\98\DEL\06\00\E7Ol\B6\82\B9\0E\00^\08\B9\E0\C3\18\02\00l\D0\E2>\ECT\0E\00\C2\AB<\91\96\03\08\00\02B\14\CCg\97\09\00Pd\1F\07\E4\D6\07\00\E1\E4>\EA\C3\F7\01\00\DA\E3\F4\CD>\A5\00\00\00\D2~y\C2\18\04\00S\B4\E5\80\1A\C4\02\00K\C5\9D\8E\E0\0F\06\00\B7\A0\09\C3\F1\B2\06\00\BC\BB\CB\11;)\03\00\ED\A7X\86W\F4\01\00\1C\C8w{\BC\93\03\00\02\8C\CDh\A8g\0B\00&6\D9\AD\19G\07\00O\14Z\D1J\17\0C\00#\FB\\\F6=K\03\00\D3\C3\9AY\B5\EB\0E\00UG?\B7E\86\03\007]as\07\B1\01\00\D4r}\EA\05\03\07\00\E2\9D\8A\DC\FB1\07\00N\CA\D0\BB\CE\C0\07\00\BDY`0\DA\C5\04\00SH\BF\CC\EF\AC\04\00\AF\B7\99lZ\B2\06\00gh\023\18F\06\00\94\A9v\11\AD\CE\07\00\22\E6M\C6\08\1E\0B\00B\0C*\92q\AF\0F\00\EB\AC\1C!H\C0\06\00\13\0E[\9Bnn\05\00\D0\E4O7\16\B8\07\00\83GVh\DBL\06\00\DFfX\82\CD:\00\00\1D\CALL\8F\BB\04\00\91\F0\C9\E5\BF\A8\02\00\D7\14\C4\D7s.\03\00\CC?\11\04\C1\1B\07\00R\0AkN\19\F1\01\00\F4\F1pQ\90~\01\00\EB:\CE\93\C7\B1\00\00\F0\96\CE\E3j\F5\06\00\A6\B4\F6\86\E1\A3\02\00\EF\A8&\AFd\1E\0C\00}\99\05\FE\DA4\09\002\C7\ED\B9\A2t\08\00\AA\92\FC\96\BC\BC\0A\00s\92\1E\8C\ED\96\00\00\A7\AB\CB\DA\C2h\00\00\ADM~\9B\DC\CB\03\00j\D1\9B\C6\CD\8B\06\00\B3\AF\FE\A9'\FF\06\00)c\1Fa>\F7\01\00\81-\C89\10\D5\00\00\C5\CE\C0\D7\B0\B8\01\00\D2:\02p\A8f\04\00\84\E2m[Z+\07\00\C37\A3(F,\09\00\8D\E7`\F4gl\04\00^rh\DE\E5\90\0C\00A\8C\01\D25\84\06\00\E7\FD\A6zZH\03\00 \E7h\EDt\97\06\00&~\95\E2})\03\00&t\E3w\00E\06\00\AE\9C\B5(\FE\B3\00\00\B7\97\0D\16\A1\1A\06\00\8E\12U\7F{\8A\04\00\A6\E4\B2\C5\B0\BA\06\00-/\DD0!\82\03\00\B4x\F6\B9Y\A1\00\00\8D\EE\03\05\CE\C6\02\00\07\9BFv\E6\17\07\00)\D1c<\04<\04\00\B33\D0\0C)J\04\00\01\DCTp\87\D3\09\008\837\B5\C2\F8\08\00\89(c\9C\B1\DF\02\00\B0Q\9EH%\85\03\003[ziH\DA\03\00M\B6rw\F2\D4\03\00I&\D9\D1z\E7\00\00u\\\DB\F2\1D0\02\00\E3\C5;\A3\01\15\02\00\82\03u?\B5v\02\00\\w\01p\BC\FA\06\00\8D%\C7T\1E\CC\04\00\9C\E1:k\D8\E1\0B\00\12\17\A7\170\8F\02\00\9Ez\0C\E4O\D0\08\00\FE\CF\E1\22\C3;\07\00-\A37\22O)\07\00\8EcCuf\C0\04\00\7F~\1F\C9\89\0C\07\00}\98\D0\9B\ED\A6\02\00\A0S\D7\E4zr\01\00\14u\CE\FD\F3.\06\00\FD>}\F7\17\80\00\00\CBmH>\0D\C7\03\00vG{z\97\09\04\00\A7\1B\E7\D4^R\01\00fV\D1\87\8C\92\01\00)r\08f\D5G\08\00F\C9\18\EB\B2V\01\00\8B\A6\B6l\A48\07\00:0\D4\AA+J\05\00\9FI\D4\C1\0E\AE\04\000!~\B5Z\95\04\00a\A3\BE\9E\C8\B2\07\00\FE\AD\BFe\B2\F4\02\00\84v:\02!\18\03\00\8FEt\17\B4}\07\00\A7}\BE\A2\9B\CB\06\00z\B0\BA\0F\9C\01\03\00v\AC\19\12\FFB\07\00\C9K\D2_W\87\03\001\DAa4\1B\7F\01\00\86(l\03=k\09\003A\F3\9C|\DC\09\00t\1D\EB\02\EC\05\09\00\C9s\AC\E3\D5&\09\00<D?\C4\82\8A\07\00R\CE\034\9B\19\04\00\C9\B1\1C\E2lO\03\00\84\8D\B2\D4\9C\DA\05\00\A2\BD\16\BBh\13\03\00\A9\AD\13\9A\B9\D9\03\00\C4u&p\12\81\03\00\AD\C0\E9(\8Dh\05\00\E7D\BF\FF\B1\12\07\00{\AD\D3\9C\22\C8\01\00\BB\81\BD\08\92\B4\00\00o\07\0D\0A\FBP\05\00\7F\C0\DA\1D\D3-\0E\00\B4#\AB#`\02\0C\006\CC\C9\B1`$\0A\00P-\DAd\0A\E4\0B\00Ar(-\B3\DC\02\00\B7&\98\B0\92\B8\06\00]\F4\EC9`\A3\05\00y~\09\D6\C3\90\02\00(\1F.{\EEW\01\00\9Fp\CA\9D.\A5\05\00\FE\B2\97\FF\E7x\03\00B\8B\94T\FE\B8\04\00x{\D7\AD\0FZ\07\00\FBU\\\11w\A2\05\00BL\85\E5!\D9\08\00gO6\C6\FB\0D\07\00\EC\F1\9C\B8\B9H\08\00&(\B7\B1\F1\B9\0E\00\D2-\89\91\E1\F4\08\00\CC\00\832\150\02\00bU\F8\F4\B0\FA\07\00\1D\FB!\C3\E3\B6\01\00\AC\BE\16\9C'w\07\00\DF\17\AB\02\9Bh\04\00\ED2A\EC\12\1C\05\00w\B8\B7V$\1B\03\00\81\D1\87S\1E\C2\05\00/\CAIz\C3\13\03\00\DD\9E\BC.C\B2\03\00\DC\D8\C7\81\97\89\08\00\DF\02\851\E7\0D\09\00g\AD\90\BE\18\DB\08\00\1B\B1\15\11\DA`\08\00\8C20\13\FDa\0B\00Y.\8C\B7\C2\CC\06\00w\B7\92/8\06\07\00\DCd7\F4X\02\07\00\F6\04\9A\FF\C6\DC\05\00\DB\B2*\1F\\\C5\06\00\86\99\15e\81\0C\03\00E\9A\E8\A1\F8.\02\00\E4\\\E2\12\11\E8\03\00j\0B\B4\ACXC\02\00,{\92Z\84\CD\03\00\CCQ\19,\D7\06\0D\00]\A2\FE\05\1F\BD\0C\00\CC\A8\EF\D79n\08\00#QX\B5\AAV\09\00~$\C7\8A\99_\0C\00\B0\D3o\DF\AD\15\07\00\A2\E3\D6\EB\1A\CF\07\00\A9\C8\01q\1B9\00\00i\AB5\AB\87h\05\00\91\DA\A0\E8!a\03\00\CD>]\C5(\07\03\00\81\F4f*\CD\88\01\00\0D\85[;3Q\01\00\B9ja\A3\FF\8D\01\00\D5f\F0l\08;\02\00|\D5\BD\B4\80`\06\00\AC1F\97\C60\09\00\8F\F2\F5\E6\F0\B2\04\00\80\9A\22\7F\A2\0A\03\00\F1\14\90\A1_l\09\00^\19\05\EA\18Q\03\00m\B8 -\F8F\00\00EQ\C7\CA<J\03\00\96\84\C2\19u:\05\00\E8\C6\88S\BB\1E\00\00;\F5r\E7nA\05\00\E8\A1\12\9Ds\B9\00\00\E3?&C\1CX\02\00\AB\E1\94\FEW(\00\00s\84\81\F1N\86\04\00\1D\B8\D0\0B:\A8\05\00\A1\19\85\86#w\0B\00\AD;\19\D2\FBT\08\00\81M\9F7s(\09\00\BB\F6\D7\AE\03l\0A\00\B3\9Ac\972\C3\07\00\02\DFq\1A\0Dd\05\00\1E\1F\D1<\F0\88\05\00\1D\C4%`.\B6\07\00\BAM\C3\C0\AD\A7\02\00\CE}\1CX/z\06\00\C3\B2-5\05\09\04\00%z\EA\F0\90&\06\00\DC=\A5lH\AA\03\00\1D\9E\95iQ\8B\07\00-\CCiWZ\C8\04\00+\7Fe\BA\E9J\07\00T\FA\9B\DB\A0\1A\06\00*\0B\C5\E5\0E\DA\08\00\D1\BC$\02\ECW\0C\00\0D\18]\DFT\82\01\00\1F\A2\8C:\9D\FF\00\00T\18\D4}\C49\02\00\A4\1A\95\AB\93\84\03\00\1E7\90\BC\14#\00\00\8A\90&\8F\FE\AE\00\00=oZ\A7j\BF\03\00\CC\EEZ\E8;\13\02\00u\9B\BC\C5\DD$\05\00\F0\FC4\C5r\95\07\00\97\95t\E0\00C\0B\00\86\86\98\80\0Cr\0C\00\97\DC|\91&#\02\00\CBU\FBI\0A\0E\05\00\19\7Fn\0B\0C\89\07\00o-[\A3<\B2\05\00s$7\98%W\07\006(\EC\12\A8[\06\00\06\C4\9B\19\82\9F\07\00\0E\B6\98\8D\DF\0D\07\00\C4]\D7\FD\B7@\01\00\92~\D3\02_\0B\03\00\0E\CC\8E\16\12\D2\02\00\F6\18q\AC\15U\00\00\A7\89\1EiiW\04\00\ADC\A6[\DC=\06\00!gm#7=\03\00\FBs!Bv\9E\09\00*\08:\D7E<\0E\00\C6\05kp\0F\EC\02\00\DB-[4\05\E3\03\00\9Cjs]\80\BD\06\000\A7\1E\F5\85W\05\00\EE\F7\AE\11\01\C1\06\00\C1\01/#t\0B\01\00\D8Y\8F`\94\16\02\00\87\9F\8F\A1\C7\F7\03\00\B87%\C2Q8\01\00\157[(\C8S\03\00\F4\A3%\9D\FA\D6\05\00\CA\A6\A3\B2\FEZ\0C\00\84\B5\CC\01\BE\F3\00\00\B4\B3\99\B6r~\0A\00\0B\FBe&\03\8E\0B\00\9D|\88A\FAt\0D\00\BBln\E4\85A\07\00\DBH\CAG\E4%\00\000\A7\A9\18\99\F4\05\00\FA\FB\FA\BF<\BD\04\00\F6u\F7\04\E7E\06\00\FA\1E\89\DE\DA)\05\00%\19\FB\DCE\A2\05\00\CF\E9<DT8\05\00\14\C1\AC\1Ay\99\04\00\AB\CAMW\0EB\07\00\09K#\94?n\06\00\07\1F\82Ch\D3\04\00\87\ED!\97R\11\07\00I\D8\99\A5\A2:\08\00\DB<\9C\FA`\BA\0A\00<Q4\A08\A1\06\00\EC\BEs:\DF\E8\05\00\80\98?\98\92\1B\05\00\C6\80\1CW\94\E9\01\00\1BX+c\F4N\04\00\C9d\D3!\1CI\06\00z\B4DI\A4\8C\05\00\EEh\17]r\1C\00\00\E0\EC\88z\AB\E7\01\00_K\C4\99H\05\07\00", align 8

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable
declare void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), i32 noundef) unnamed_addr #0

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(120)) unnamed_addr #1

; Function Attrs: nounwind nonlazybind uwtable
define hidden fastcc void @_RNvNtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial10scalar_mul19vartime_double_base3mul(ptr dead_on_unwind noalias nofree noundef nonnull writable writeonly align 8 captures(none) dereferenceable(160) %_0, ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32) %a, ptr noalias nofree noundef nonnull readonly align 8 captures(none) dereferenceable(160) %A, ptr noalias nofree noundef nonnull readonly captures(none) dereferenceable(32) %b) unnamed_addr #2 personality ptr @rust_eh_personality {
start:
  %x_u64.i27 = alloca [40 x i8], align 8
  %x_u64.i = alloca [40 x i8], align 8
  %_68 = alloca [120 x i8], align 8
  %_59 = alloca [160 x i8], align 8
  %_49 = alloca [160 x i8], align 8
  %_34 = alloca [160 x i8], align 8
  %_24 = alloca [160 x i8], align 8
  %t = alloca [160 x i8], align 8
  %r = alloca [120 x i8], align 8
  %table_A = alloca [1280 x i8], align 8
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
  call void @llvm.lifetime.start.p0(ptr nonnull %x_u64.i27), !noalias !20
  %11 = getelementptr inbounds nuw i8, ptr %x_u64.i27, i64 32
  store i64 0, ptr %11, align 8, !noalias !20
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(32) %x_u64.i27, ptr noundef nonnull readonly align 1 dereferenceable(32) %b, i64 32, i1 false), !alias.scope !21, !noalias !15
  br label %bb3.lr.ph.i28

bb3.lr.ph.i28:                                    ; preds = %bb11.i46, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit
  %pos.sroa.0.0.ph17.i29 = phi i64 [ 0, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit ], [ %21, %bb11.i46 ]
  %carry.sroa.0.0.ph16.i30 = phi i64 [ 0, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit ], [ %carry.sroa.0.1.i50, %bb11.i46 ]
  br label %bb3.i31

bb3.i31:                                          ; preds = %bb10.i52, %bb3.lr.ph.i28
  %pos.sroa.0.015.i32 = phi i64 [ %pos.sroa.0.0.ph17.i29, %bb3.lr.ph.i28 ], [ %18, %bb10.i52 ]
  %u64_idx11.i33 = lshr i64 %pos.sroa.0.015.i32, 6
  %bit_idx.i34 = and i64 %pos.sroa.0.015.i32, 63
  %_20.i35 = icmp samesign ult i64 %bit_idx.i34, 56
  %12 = getelementptr inbounds nuw i64, ptr %x_u64.i27, i64 %u64_idx11.i33
  %_22.i36 = load i64, ptr %12, align 8, !noalias !20, !noundef !14
  %13 = lshr i64 %_22.i36, %bit_idx.i34
  br i1 %_20.i35, label %bb9.i41, label %bb8.i37

bb8.i37:                                          ; preds = %bb3.i31
  %14 = getelementptr inbounds nuw i8, ptr %12, i64 8
  %_28.i38 = load i64, ptr %14, align 8, !noalias !20, !noundef !14
  %_31.i39 = sub nsw i64 0, %pos.sroa.0.015.i32
  %15 = and i64 %_31.i39, 63
  %_27.i40 = shl i64 %_28.i38, %15
  %16 = or i64 %_27.i40, %13
  br label %bb9.i41

bb9.i41:                                          ; preds = %bb8.i37, %bb3.i31
  %bit_buf.sroa.0.0.i42 = phi i64 [ %16, %bb8.i37 ], [ %13, %bb3.i31 ]
  %_34.i43 = and i64 %bit_buf.sroa.0.0.i42, 255
  %window.i44 = add nuw nsw i64 %_34.i43, %carry.sroa.0.0.ph16.i30
  %_35.i45 = and i64 %window.i44, 1
  %17 = icmp eq i64 %_35.i45, 0
  br i1 %17, label %bb10.i52, label %bb11.i46

bb10.i52:                                         ; preds = %bb9.i41
  %18 = add nuw nsw i64 %pos.sroa.0.015.i32, 1
  %exitcond.not.i53 = icmp eq i64 %18, 256
  br i1 %exitcond.not.i53, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit54, label %bb3.i31

bb11.i46:                                         ; preds = %bb9.i41
  %_36.i47 = icmp samesign ugt i64 %window.i44, 127
  %19 = trunc i64 %window.i44 to i8
  %carry.sroa.0.1.i50 = zext i1 %_36.i47 to i64
  %20 = getelementptr inbounds nuw i8, ptr %b_naf, i64 %pos.sroa.0.015.i32
  store i8 %19, ptr %20, align 1, !alias.scope !15, !noalias !18
  %21 = add nuw nsw i64 %pos.sroa.0.015.i32, 8
  %_1314.i51 = icmp ult i64 %pos.sroa.0.015.i32, 248
  br i1 %_1314.i51, label %bb3.lr.ph.i28, label %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit54

_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit54: ; preds = %bb11.i46, %bb10.i52
  call void @llvm.lifetime.end.p0(ptr nonnull %x_u64.i27), !noalias !20
  br label %bb40

bb40:                                             ; preds = %bb8, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit54
  %iter.sroa.0.075 = phi i64 [ 256, %_RNvMso_NtCsjK63O35OHGN_14solana_ed255196scalarNtB5_6Scalar17non_adjacent_form.exit54 ], [ %_74, %bb8 ]
  %_74 = add nsw i64 %iter.sroa.0.075, -1
  %22 = getelementptr inbounds nuw i8, ptr %a_naf, i64 %_74
  %_8 = load i8, ptr %22, align 1, !noundef !14
  %23 = icmp eq i8 %_8, 0
  br i1 %23, label %bb8, label %bb12

bb12:                                             ; preds = %bb8, %bb40
  call void @llvm.lifetime.start.p0(ptr nonnull %table_A)
  call void @_RNvXs0_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable5NtNtNtNtB7_7backend6serial12curve_models20ProjectiveNielsPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtB7_7edwards12EdwardsPointE4from(ptr noalias nofree noundef nonnull sret([1280 x i8]) align 8 captures(none) dereferenceable(1280) %table_A, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %A) #12
  call void @llvm.lifetime.start.p0(ptr nonnull %r)
  call void @llvm.memset.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %r, i8 0, i64 40, i1 false)
  %24 = getelementptr inbounds nuw i8, ptr %r, i64 40
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %24, ptr noundef nonnull align 8 dereferenceable(40) @alloc_d6091242425a18f93aa551ed73483e0d, i64 40, i1 false)
  %25 = getelementptr inbounds nuw i8, ptr %r, i64 80
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(40) %25, ptr noundef nonnull align 8 dereferenceable(40) @alloc_d6091242425a18f93aa551ed73483e0d, i64 40, i1 false)
  %_4.i55 = getelementptr inbounds nuw i8, ptr %t, i64 120
  %_6.i56 = getelementptr inbounds nuw i8, ptr %t, i64 40
  %_7.i57 = getelementptr inbounds nuw i8, ptr %t, i64 80
  %26 = getelementptr inbounds nuw i8, ptr %_24, i64 40
  %27 = getelementptr inbounds nuw i8, ptr %_24, i64 80
  %28 = getelementptr inbounds nuw i8, ptr %_24, i64 120
  %29 = getelementptr inbounds nuw i8, ptr %_34, i64 40
  %30 = getelementptr inbounds nuw i8, ptr %_34, i64 80
  %31 = getelementptr inbounds nuw i8, ptr %_34, i64 120
  %32 = getelementptr inbounds nuw i8, ptr %_49, i64 40
  %33 = getelementptr inbounds nuw i8, ptr %_49, i64 80
  %34 = getelementptr inbounds nuw i8, ptr %_49, i64 120
  %35 = getelementptr inbounds nuw i8, ptr %_59, i64 40
  %36 = getelementptr inbounds nuw i8, ptr %_59, i64 80
  %37 = getelementptr inbounds nuw i8, ptr %_59, i64 120
  %38 = getelementptr inbounds nuw i8, ptr %_68, i64 40
  %39 = getelementptr inbounds nuw i8, ptr %_68, i64 80
  br label %bb16

bb8:                                              ; preds = %bb40
  %40 = getelementptr inbounds nuw i8, ptr %b_naf, i64 %_74
  %_11 = load i8, ptr %40, align 1, !noundef !14
  %41 = icmp ne i8 %_11, 0
  %_73.not = icmp eq i64 %_74, 0
  %or.cond = or i1 %41, %_73.not
  br i1 %or.cond, label %bb12, label %bb40

bb16:                                             ; preds = %bb38, %bb12
  %i.sroa.0.2 = phi i64 [ %_74, %bb12 ], [ %52, %bb38 ]
  call void @llvm.lifetime.start.p0(ptr nonnull %t)
  call void @_RNvMsa_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint6double(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(120) %r) #12
  %42 = getelementptr inbounds nuw i8, ptr %a_naf, i64 %i.sroa.0.2
  %_77 = load i8, ptr %42, align 1, !noundef !14
  %_18 = tail call i8 @llvm.scmp.i8.i8(i8 %_77, i8 0)
  switch i8 %_18, label %bb4 [
    i8 -1, label %bb17
    i8 0, label %bb26
    i8 1, label %bb18
  ]

bb4:                                              ; preds = %bb26, %bb16
  unreachable

bb17:                                             ; preds = %bb16
  call void @llvm.lifetime.start.p0(ptr nonnull %_34)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %_34, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !25
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %29, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57) #12, !alias.scope !25
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %30, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !25
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %31, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56) #12, !alias.scope !25
  %_39 = sub i8 0, %_77
  %_38 = sext i8 %_39 to i64
  %_8024 = lshr i64 %_38, 1
  %_81 = icmp ult i8 %_39, 16
  br i1 %_81, label %bb43, label %panic4

bb18:                                             ; preds = %bb16
  call void @llvm.lifetime.start.p0(ptr nonnull %_24)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %_24, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !29
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %26, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57) #12, !alias.scope !29
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %27, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !29
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %28, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56) #12, !alias.scope !29
  %_28 = sext i8 %_77 to i64
  %_7823 = lshr i64 %_28, 1
  %_79 = icmp ult i8 %_77, 16
  br i1 %_79, label %bb42, label %panic6

bb43:                                             ; preds = %bb17
  %43 = getelementptr inbounds nuw %"backend::serial::curve_models::ProjectiveNielsPoint", ptr %table_A, i64 %_8024
  call void @_RNvXsc_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_20ProjectiveNielsPointE3sub(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_34, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %43) #12
  call void @llvm.lifetime.end.p0(ptr nonnull %_34)
  br label %bb26

panic4:                                           ; preds = %bb17
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_8024, i64 noundef 8, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_a8fabae8f73f66aef6660ad7c9447c5d) #13
  unreachable

bb42:                                             ; preds = %bb18
  %44 = getelementptr inbounds nuw %"backend::serial::curve_models::ProjectiveNielsPoint", ptr %table_A, i64 %_7823
  call void @_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_24, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %44) #12
  call void @llvm.lifetime.end.p0(ptr nonnull %_24)
  br label %bb26

panic6:                                           ; preds = %bb18
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_7823, i64 noundef 8, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_a8fabae8f73f66aef6660ad7c9447c5d) #13
  unreachable

bb26:                                             ; preds = %bb42, %bb43, %bb16
  %45 = getelementptr inbounds nuw i8, ptr %b_naf, i64 %i.sroa.0.2
  %_82 = load i8, ptr %45, align 1, !noundef !14
  %_43 = tail call i8 @llvm.scmp.i8.i8(i8 %_82, i8 0)
  switch i8 %_43, label %bb4 [
    i8 -1, label %bb27
    i8 0, label %bb35
    i8 1, label %bb28
  ]

bb27:                                             ; preds = %bb26
  call void @llvm.lifetime.start.p0(ptr nonnull %_59)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %_59, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !33
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %35, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57) #12, !alias.scope !33
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %36, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !33
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %37, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56) #12, !alias.scope !33
  %_64 = sub i8 0, %_82
  %_63 = sext i8 %_64 to i64
  %_8526 = lshr i64 %_63, 1
  %_86 = icmp sgt i8 %_64, -1
  br i1 %_86, label %bb45, label %panic9

bb35:                                             ; preds = %bb44, %bb45, %bb26
  call void @llvm.lifetime.start.p0(ptr nonnull %_68)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(120) %_68, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !37
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %38, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57) #12, !alias.scope !37
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %39, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !37
  call void @llvm.memcpy.p0.p0.i64(ptr noundef nonnull align 8 dereferenceable(120) %r, ptr noundef nonnull align 8 dereferenceable(120) %_68, i64 120, i1 false)
  call void @llvm.lifetime.end.p0(ptr nonnull %_68)
  %46 = icmp eq i64 %i.sroa.0.2, 0
  br i1 %46, label %bb37, label %bb38

bb28:                                             ; preds = %bb26
  call void @llvm.lifetime.start.p0(ptr nonnull %_49)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %_49, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !41
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %32, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57) #12, !alias.scope !41
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %33, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_7.i57, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_4.i55) #12, !alias.scope !41
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %34, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %_6.i56) #12, !alias.scope !41
  %_53 = sext i8 %_82 to i64
  %_8325 = lshr i64 %_53, 1
  %_84 = icmp sgt i8 %_82, -1
  br i1 %_84, label %bb44, label %panic11

bb45:                                             ; preds = %bb27
  %47 = getelementptr inbounds nuw %"backend::serial::curve_models::AffineNielsPoint", ptr @alloc_eaf951945d20f8425ce4c25607db196f, i64 %_8526
  call void @_RNvXse_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_16AffineNielsPointE3sub(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_59, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(120) %47) #12
  call void @llvm.lifetime.end.p0(ptr nonnull %_59)
  br label %bb35

panic9:                                           ; preds = %bb27
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_8526, i64 noundef 64, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_f7b128ba219626851d37833adc9e2368) #13
  unreachable

bb44:                                             ; preds = %bb28
  %48 = getelementptr inbounds nuw %"backend::serial::curve_models::AffineNielsPoint", ptr @alloc_eaf951945d20f8425ce4c25607db196f, i64 %_8325
  call void @_RNvXsd_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_16AffineNielsPointE3add(ptr noalias nofree noundef nonnull sret([160 x i8]) align 8 captures(none) dereferenceable(160) %t, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(160) %_49, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(120) %48) #12
  call void @llvm.lifetime.end.p0(ptr nonnull %_49)
  br label %bb35

panic11:                                          ; preds = %bb28
  tail call void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef %_8325, i64 noundef 64, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24) @alloc_f7b128ba219626851d37833adc9e2368) #13
  unreachable

bb37:                                             ; preds = %bb35
  call void @llvm.lifetime.end.p0(ptr nonnull %t)
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(160) %_0, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(120) %r, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %25) #12, !alias.scope !45
  %49 = getelementptr inbounds nuw i8, ptr %_0, i64 40
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %49, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %24, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %25) #12, !alias.scope !45
  %50 = getelementptr inbounds nuw i8, ptr %_0, i64 80
  call void @_RNvMs8_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldNtB5_14FieldElement515pow2k(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %50, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %25, i32 noundef 1) #12, !alias.scope !45
  %51 = getelementptr inbounds nuw i8, ptr %_0, i64 120
  call void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr noalias nofree noundef nonnull sret([40 x i8]) align 8 captures(none) dereferenceable(40) %51, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(120) %r, ptr noalias nofree noundef nonnull readonly align 8 captures(address, read_provenance) dereferenceable(40) %24) #12, !alias.scope !45
  call void @llvm.lifetime.end.p0(ptr nonnull %r)
  call void @llvm.lifetime.end.p0(ptr nonnull %table_A)
  call void @llvm.lifetime.end.p0(ptr nonnull %b_naf)
  call void @llvm.lifetime.end.p0(ptr nonnull %a_naf)
  ret void

bb38:                                             ; preds = %bb35
  %52 = add nsw i64 %i.sroa.0.2, -1
  call void @llvm.lifetime.end.p0(ptr nonnull %t)
  br label %bb16
}

; Function Attrs: nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXs0_NtCsjK63O35OHGN_14solana_ed255196windowINtB5_15NafLookupTable5NtNtNtNtB7_7backend6serial12curve_models20ProjectiveNielsPointEINtNtCsgxBkk5gSRhY_4core7convert4FromRNtNtB7_7edwards12EdwardsPointE4from(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([1280 x i8]) align 8 captures(none) dereferenceable(1280), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #1

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable
declare void @_RNvXs5_NtNtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial3u645fieldRNtB5_14FieldElement51NtNtNtCsgxBkk5gSRhY_4core3ops5arith3Mul3mul(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([40 x i8]) align 8 captures(none) dereferenceable(40) initializes((0, 40)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(40)) unnamed_addr #3

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXsb_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_20ProjectiveNielsPointE3add(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #4

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXsc_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_20ProjectiveNielsPointE3sub(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160)) unnamed_addr #4

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXsd_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3AddRNtB5_16AffineNielsPointE3add(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(120)) unnamed_addr #4

; Function Attrs: mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable
declare void @_RNvXse_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsRNtNtBb_7edwards12EdwardsPointINtNtNtCsgxBkk5gSRhY_4core3ops5arith3SubRNtB5_16AffineNielsPointE3sub(ptr dead_on_unwind noalias nofree noundef writable writeonly sret([160 x i8]) align 8 captures(none) dereferenceable(160) initializes((0, 160)), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(160), ptr noalias nofree noundef readonly align 8 captures(none) dereferenceable(120)) unnamed_addr #4

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.start.p0(ptr captures(none)) #5

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: readwrite)
declare void @llvm.memcpy.p0.p0.i64(ptr noalias writeonly captures(none), ptr noalias readonly captures(none), i64, i1 immarg) #6

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(argmem: readwrite)
declare void @llvm.lifetime.end.p0(ptr captures(none)) #5

; Function Attrs: nonlazybind
declare i32 @rust_eh_personality(...) unnamed_addr #7

; Function Attrs: nocallback nofree nounwind willreturn memory(argmem: write)
declare void @llvm.memset.p0.i64(ptr writeonly captures(none), i8, i64, i1 immarg) #8

; Function Attrs: cold minsize noinline noreturn nounwind nonlazybind optsize uwtable
declare void @_RNvNtCsgxBkk5gSRhY_4core9panicking18panic_bounds_check(i64 noundef, i64 noundef, ptr noalias nofree noundef readonly align 8 captures(address, read_provenance) dereferenceable(24)) unnamed_addr #9

; Function Attrs: nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none)
declare range(i8 -1, 2) i8 @llvm.scmp.i8.i8(i8, i8) #10

; Function Attrs: nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite)
declare void @llvm.experimental.noalias.scope.decl(metadata) #11

attributes #0 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #1 = { nofree norecurse nosync nounwind nonlazybind memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #2 = { nounwind nonlazybind uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #3 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #4 = { mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(argmem: readwrite, inaccessiblemem: readwrite) uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #5 = { nocallback nofree nosync nounwind willreturn memory(argmem: readwrite) }
attributes #6 = { nocallback nofree nounwind willreturn memory(argmem: readwrite) }
attributes #7 = { nonlazybind "target-cpu"="x86-64" }
attributes #8 = { nocallback nofree nounwind willreturn memory(argmem: write) }
attributes #9 = { cold minsize noinline noreturn nounwind nonlazybind optsize uwtable "probe-stack"="inline-asm" "target-cpu"="x86-64" }
attributes #10 = { nocallback nocreateundeforpoison nofree nosync nounwind speculatable willreturn memory(none) }
attributes #11 = { nocallback nofree nosync nounwind willreturn memory(inaccessiblemem: readwrite) }
attributes #12 = { nounwind }
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
!26 = distinct !{!26, !27, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %_0"}
!27 = distinct !{!27, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended"}
!28 = distinct !{!28, !27, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %self"}
!29 = !{!30, !32}
!30 = distinct !{!30, !31, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %_0"}
!31 = distinct !{!31, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended"}
!32 = distinct !{!32, !31, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %self"}
!33 = !{!34, !36}
!34 = distinct !{!34, !35, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %_0"}
!35 = distinct !{!35, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended"}
!36 = distinct !{!36, !35, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %self"}
!37 = !{!38, !40}
!38 = distinct !{!38, !39, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint13as_projective: %_0"}
!39 = distinct !{!39, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint13as_projective"}
!40 = distinct !{!40, !39, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint13as_projective: %self"}
!41 = !{!42, !44}
!42 = distinct !{!42, !43, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %_0"}
!43 = distinct !{!43, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended"}
!44 = distinct !{!44, !43, !"_RNvMs9_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_14CompletedPoint11as_extended: %self"}
!45 = !{!46, !48}
!46 = distinct !{!46, !47, !"_RNvMs8_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint11as_extended: %_0"}
!47 = distinct !{!47, !"_RNvMs8_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint11as_extended"}
!48 = distinct !{!48, !47, !"_RNvMs8_NtNtNtCsjK63O35OHGN_14solana_ed255197backend6serial12curve_modelsNtB5_15ProjectivePoint11as_extended: %self"}
