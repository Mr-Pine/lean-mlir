import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofData
import SSA.Projects.Agave.LatticeHash.MLIR.agave_portable_compress_in_place
import SSA.Projects.Agave.LatticeHash.MLIR.BatchRoundData
namespace AgaveLatticeHash.MLIR.PortableInPlace
open LeanMLIR SLLVM PortableXof
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def input := splitPrefix% agave_portable_compress_in_place.cfgEntry at 75
def rounds := splitPrefix% input.tail at 784

theorem input_parts : input.pre.append input.tail = agave_portable_compress_in_place.cfgEntry := rfl
theorem round_parts : rounds.pre.append rounds.tail = input.tail := rfl

def vars : HVector input.middle.Var preInput.middle.toList :=
  (⟨0, rfl⟩ ::ₕ
   ⟨1, rfl⟩ ::ₕ
   ⟨2, rfl⟩ ::ₕ
   ⟨3, rfl⟩ ::ₕ
   ⟨4, rfl⟩ ::ₕ
   ⟨5, rfl⟩ ::ₕ
   ⟨6, rfl⟩ ::ₕ
   ⟨7, rfl⟩ ::ₕ
   ⟨8, rfl⟩ ::ₕ
   ⟨9, rfl⟩ ::ₕ
   ⟨10, rfl⟩ ::ₕ
   ⟨11, rfl⟩ ::ₕ
   ⟨12, rfl⟩ ::ₕ
   ⟨13, rfl⟩ ::ₕ
   ⟨14, rfl⟩ ::ₕ
   ⟨15, rfl⟩ ::ₕ
   ⟨16, rfl⟩ ::ₕ
   ⟨17, rfl⟩ ::ₕ
   ⟨18, rfl⟩ ::ₕ
   ⟨19, rfl⟩ ::ₕ
   ⟨20, rfl⟩ ::ₕ
   ⟨21, rfl⟩ ::ₕ
   ⟨22, rfl⟩ ::ₕ
   ⟨23, rfl⟩ ::ₕ
   ⟨24, rfl⟩ ::ₕ
   ⟨25, rfl⟩ ::ₕ
   ⟨26, rfl⟩ ::ₕ
   ⟨27, rfl⟩ ::ₕ
   ⟨28, rfl⟩ ::ₕ
   ⟨29, rfl⟩ ::ₕ
   ⟨30, rfl⟩ ::ₕ
   ⟨31, rfl⟩ ::ₕ
   ⟨32, rfl⟩ ::ₕ
   ⟨33, rfl⟩ ::ₕ
   ⟨34, rfl⟩ ::ₕ
   ⟨35, rfl⟩ ::ₕ
   ⟨36, rfl⟩ ::ₕ
   ⟨37, rfl⟩ ::ₕ
   ⟨38, rfl⟩ ::ₕ
   ⟨39, rfl⟩ ::ₕ
   ⟨40, rfl⟩ ::ₕ
   ⟨41, rfl⟩ ::ₕ
   ⟨42, rfl⟩ ::ₕ
   ⟨43, rfl⟩ ::ₕ
   ⟨44, rfl⟩ ::ₕ
   ⟨45, rfl⟩ ::ₕ
   ⟨46, rfl⟩ ::ₕ
   ⟨47, rfl⟩ ::ₕ
   ⟨48, rfl⟩ ::ₕ
   ⟨49, rfl⟩ ::ₕ
   ⟨50, rfl⟩ ::ₕ
   ⟨51, rfl⟩ ::ₕ
   ⟨52, rfl⟩ ::ₕ
   ⟨53, rfl⟩ ::ₕ
   ⟨54, rfl⟩ ::ₕ
   ⟨55, rfl⟩ ::ₕ
   ⟨56, rfl⟩ ::ₕ
   ⟨57, rfl⟩ ::ₕ
   ⟨58, rfl⟩ ::ₕ
   ⟨59, rfl⟩ ::ₕ
   ⟨60, rfl⟩ ::ₕ
   ⟨61, rfl⟩ ::ₕ
   ⟨62, rfl⟩ ::ₕ
   ⟨63, rfl⟩ ::ₕ
   ⟨64, rfl⟩ ::ₕ
   ⟨65, rfl⟩ ::ₕ
   ⟨66, rfl⟩ ::ₕ
   ⟨67, rfl⟩ ::ₕ
   ⟨68, rfl⟩ ::ₕ
   ⟨69, rfl⟩ ::ₕ
   ⟨70, rfl⟩ ::ₕ
   ⟨71, rfl⟩ ::ₕ
   ⟨72, rfl⟩ ::ₕ
   ⟨73, rfl⟩ ::ₕ
   ⟨74, rfl⟩ ::ₕ
   ⟨75, rfl⟩ ::ₕ
   ⟨76, rfl⟩ ::ₕ
   ⟨77, rfl⟩ ::ₕ
   ⟨78, rfl⟩ ::ₕ
   ⟨77, rfl⟩ ::ₕ .nil)
def rename : preInput.middle.Hom input.middle := fun _ v => vars[v]
def map16 : (inputAt% preInput.tail at 16).Hom (inputAt% input.tail at 16) :=
  appendMap% preInput.tail into input.tail using rename skip 0 count 16
def map32 : (inputAt% preInput.tail at 32).Hom (inputAt% input.tail at 32) :=
  appendMap% preInput.tail into input.tail using map16 skip 16 count 16
def map48 : (inputAt% preInput.tail at 48).Hom (inputAt% input.tail at 48) :=
  appendMap% preInput.tail into input.tail using map32 skip 32 count 16
def map64 : (inputAt% preInput.tail at 64).Hom (inputAt% input.tail at 64) :=
  appendMap% preInput.tail into input.tail using map48 skip 48 count 16
def map80 : (inputAt% preInput.tail at 80).Hom (inputAt% input.tail at 80) :=
  appendMap% preInput.tail into input.tail using map64 skip 64 count 16
def map96 : (inputAt% preInput.tail at 96).Hom (inputAt% input.tail at 96) :=
  appendMap% preInput.tail into input.tail using map80 skip 80 count 16
def map112 : (inputAt% preInput.tail at 112).Hom (inputAt% input.tail at 112) :=
  appendMap% preInput.tail into input.tail using map96 skip 96 count 16
def map128 : (inputAt% preInput.tail at 128).Hom (inputAt% input.tail at 128) :=
  appendMap% preInput.tail into input.tail using map112 skip 112 count 16
def map144 : (inputAt% preInput.tail at 144).Hom (inputAt% input.tail at 144) :=
  appendMap% preInput.tail into input.tail using map128 skip 128 count 16
def map160 : (inputAt% preInput.tail at 160).Hom (inputAt% input.tail at 160) :=
  appendMap% preInput.tail into input.tail using map144 skip 144 count 16
def map176 : (inputAt% preInput.tail at 176).Hom (inputAt% input.tail at 176) :=
  appendMap% preInput.tail into input.tail using map160 skip 160 count 16
def map192 : (inputAt% preInput.tail at 192).Hom (inputAt% input.tail at 192) :=
  appendMap% preInput.tail into input.tail using map176 skip 176 count 16
def map208 : (inputAt% preInput.tail at 208).Hom (inputAt% input.tail at 208) :=
  appendMap% preInput.tail into input.tail using map192 skip 192 count 16
def map224 : (inputAt% preInput.tail at 224).Hom (inputAt% input.tail at 224) :=
  appendMap% preInput.tail into input.tail using map208 skip 208 count 16
def map240 : (inputAt% preInput.tail at 240).Hom (inputAt% input.tail at 240) :=
  appendMap% preInput.tail into input.tail using map224 skip 224 count 16
def map256 : (inputAt% preInput.tail at 256).Hom (inputAt% input.tail at 256) :=
  appendMap% preInput.tail into input.tail using map240 skip 240 count 16
def map272 : (inputAt% preInput.tail at 272).Hom (inputAt% input.tail at 272) :=
  appendMap% preInput.tail into input.tail using map256 skip 256 count 16
def map288 : (inputAt% preInput.tail at 288).Hom (inputAt% input.tail at 288) :=
  appendMap% preInput.tail into input.tail using map272 skip 272 count 16
def map304 : (inputAt% preInput.tail at 304).Hom (inputAt% input.tail at 304) :=
  appendMap% preInput.tail into input.tail using map288 skip 288 count 16
def map320 : (inputAt% preInput.tail at 320).Hom (inputAt% input.tail at 320) :=
  appendMap% preInput.tail into input.tail using map304 skip 304 count 16
def map336 : (inputAt% preInput.tail at 336).Hom (inputAt% input.tail at 336) :=
  appendMap% preInput.tail into input.tail using map320 skip 320 count 16
def map352 : (inputAt% preInput.tail at 352).Hom (inputAt% input.tail at 352) :=
  appendMap% preInput.tail into input.tail using map336 skip 336 count 16
def map368 : (inputAt% preInput.tail at 368).Hom (inputAt% input.tail at 368) :=
  appendMap% preInput.tail into input.tail using map352 skip 352 count 16
def map384 : (inputAt% preInput.tail at 384).Hom (inputAt% input.tail at 384) :=
  appendMap% preInput.tail into input.tail using map368 skip 368 count 16
def map400 : (inputAt% preInput.tail at 400).Hom (inputAt% input.tail at 400) :=
  appendMap% preInput.tail into input.tail using map384 skip 384 count 16
def map416 : (inputAt% preInput.tail at 416).Hom (inputAt% input.tail at 416) :=
  appendMap% preInput.tail into input.tail using map400 skip 400 count 16
def map432 : (inputAt% preInput.tail at 432).Hom (inputAt% input.tail at 432) :=
  appendMap% preInput.tail into input.tail using map416 skip 416 count 16
def map448 : (inputAt% preInput.tail at 448).Hom (inputAt% input.tail at 448) :=
  appendMap% preInput.tail into input.tail using map432 skip 432 count 16
def map464 : (inputAt% preInput.tail at 464).Hom (inputAt% input.tail at 464) :=
  appendMap% preInput.tail into input.tail using map448 skip 448 count 16
def map480 : (inputAt% preInput.tail at 480).Hom (inputAt% input.tail at 480) :=
  appendMap% preInput.tail into input.tail using map464 skip 464 count 16
def map496 : (inputAt% preInput.tail at 496).Hom (inputAt% input.tail at 496) :=
  appendMap% preInput.tail into input.tail using map480 skip 480 count 16
def map512 : (inputAt% preInput.tail at 512).Hom (inputAt% input.tail at 512) :=
  appendMap% preInput.tail into input.tail using map496 skip 496 count 16
def map528 : (inputAt% preInput.tail at 528).Hom (inputAt% input.tail at 528) :=
  appendMap% preInput.tail into input.tail using map512 skip 512 count 16
def map544 : (inputAt% preInput.tail at 544).Hom (inputAt% input.tail at 544) :=
  appendMap% preInput.tail into input.tail using map528 skip 528 count 16
def map560 : (inputAt% preInput.tail at 560).Hom (inputAt% input.tail at 560) :=
  appendMap% preInput.tail into input.tail using map544 skip 544 count 16
def map576 : (inputAt% preInput.tail at 576).Hom (inputAt% input.tail at 576) :=
  appendMap% preInput.tail into input.tail using map560 skip 560 count 16
def map592 : (inputAt% preInput.tail at 592).Hom (inputAt% input.tail at 592) :=
  appendMap% preInput.tail into input.tail using map576 skip 576 count 16
def map608 : (inputAt% preInput.tail at 608).Hom (inputAt% input.tail at 608) :=
  appendMap% preInput.tail into input.tail using map592 skip 592 count 16
def map624 : (inputAt% preInput.tail at 624).Hom (inputAt% input.tail at 624) :=
  appendMap% preInput.tail into input.tail using map608 skip 608 count 16
def map640 : (inputAt% preInput.tail at 640).Hom (inputAt% input.tail at 640) :=
  appendMap% preInput.tail into input.tail using map624 skip 624 count 16
def map656 : (inputAt% preInput.tail at 656).Hom (inputAt% input.tail at 656) :=
  appendMap% preInput.tail into input.tail using map640 skip 640 count 16
def map672 : (inputAt% preInput.tail at 672).Hom (inputAt% input.tail at 672) :=
  appendMap% preInput.tail into input.tail using map656 skip 656 count 16
def map688 : (inputAt% preInput.tail at 688).Hom (inputAt% input.tail at 688) :=
  appendMap% preInput.tail into input.tail using map672 skip 672 count 16
def map704 : (inputAt% preInput.tail at 704).Hom (inputAt% input.tail at 704) :=
  appendMap% preInput.tail into input.tail using map688 skip 688 count 16
def map720 : (inputAt% preInput.tail at 720).Hom (inputAt% input.tail at 720) :=
  appendMap% preInput.tail into input.tail using map704 skip 704 count 16
def map736 : (inputAt% preInput.tail at 736).Hom (inputAt% input.tail at 736) :=
  appendMap% preInput.tail into input.tail using map720 skip 720 count 16
def map752 : (inputAt% preInput.tail at 752).Hom (inputAt% input.tail at 752) :=
  appendMap% preInput.tail into input.tail using map736 skip 736 count 16
def map768 : (inputAt% preInput.tail at 768).Hom (inputAt% input.tail at 768) :=
  appendMap% preInput.tail into input.tail using map752 skip 752 count 16
def map784 : (inputAt% preInput.tail at 784).Hom (inputAt% input.tail at 784) :=
  appendMap% preInput.tail into input.tail using map768 skip 768 count 16
abbrev finalMap := map784

end AgaveLatticeHash.MLIR.PortableInPlace
