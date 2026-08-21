/- Scratch differential test: the lifted regions and the specifications, against
   the values the real C kernels produce on one u47 input. Not part of the build. -/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Mem
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.Avx512.Spec.fd_r43x6_quad_sqr_fast

namespace Firedancer.Avx512
open LeanMLIR SLLVM

def x03 : Vector (BitVec 64) 8 := #v[30960967227906, 108191590703196, 99568252651591, 646541902135, 48152783036373, 128256956798327, 116529430256599, 91681032759915]
def x14 : Vector (BitVec 64) 8 := #v[22901890495158, 94110954151580, 55002194563223, 29457295073781, 88798114170026, 29347409075101, 84475341527456, 123784856393599]
def x25 : Vector (BitVec 64) 8 := #v[50767058061139, 112068695425569, 34819516570870, 34272072043382, 1630667224227, 7710969304554, 73095395689235, 129325765239057]
def y03 : Vector (BitVec 64) 8 := #v[60389714239261, 87669313583717, 8106135565391, 20870297766624, 71780904260106, 104264602944321, 68009942243157, 125825684921619]
def y14 : Vector (BitVec 64) 8 := #v[54014996878947, 22641949775185, 13608528965351, 102794987482229, 19576493672750, 44906110569735, 136299457759163, 50709741533289]
def y25 : Vector (BitVec 64) 8 := #v[13281468418447, 116748134932027, 7859948267258, 43472214850669, 76125532317116, 121230986634589, 87675758202868, 21100424593625]

def mz03 : Vector (BitVec 64) 8 := #v[1658286449348157186, 1566743269609104916, 2612885569210377849, 1133168447352768704, 650248434174435624, 1051669960218310812, 1221880231314455796, 1297074465630472948]
def mz14 : Vector (BitVec 64) 8 := #v[1792612736159951596, 1674213140180432896, 1371579254608637170, 1987068657072749515, 423276784423942998, 608820200793805699, 815755907048910909, 723915886831157083]
def mz25 : Vector (BitVec 64) 8 := #v[471089474189703159, 2022438017106623509, 1420487218778428809, 1658290694055201372, 21718392797143450, 34860853003991677, 123752795682703834, 60770870399897688]
def sz03 : Vector (BitVec 64) 8 := #v[820342260104544732, 1352875590689920536, 1939825842987375801, 1177980328143097209, 379797739231612664, 307479322072801824, 692879740471666550, 1239492753638823846]
def sz14 : Vector (BitVec 64) 8 := #v[1322796649243873256, 1309338436365394960, 1584004355914194466, 1327755101666427478, 161496104618139077, 66821914235772289, 903794034691442462, 1023131501319730524]
def sz25 : Vector (BitVec 64) 8 := #v[1319601907272824544, 766998798486670656, 1602813839685532789, 1404546936653680085, 9989957760580706, 12703749157885494, 102070354065316478, 296186269937092872]

def rd {n : Nat} (v : Vector (PoisonOr (BitVec 64)) n) : List (Option Nat) :=
  v.toList.map (fun x => match x with | .value b => some b.toNat | .poison => none)
def ex {n : Nat} (v : Vector (BitVec 64) n) : List (Option Nat) := rd (v.map PoisonOr.value)

/-! ## The specifications against the C kernels -/

#eval ex (quadMulResult ⟨x03, x14, x25⟩ ⟨y03, y14, y25⟩).v03 == ex mz03
    && ex (quadMulResult ⟨x03, x14, x25⟩ ⟨y03, y14, y25⟩).v14 == ex mz14
    && ex (quadMulResult ⟨x03, x14, x25⟩ ⟨y03, y14, y25⟩).v25 == ex mz25
#eval ex (quadSqrResult ⟨x03, x14, x25⟩).v03 == ex sz03
    && ex (quadSqrResult ⟨x03, x14, x25⟩).v14 == ex sz14
    && ex (quadSqrResult ⟨x03, x14, x25⟩).v25 == ex sz25

/-! ## The lifted kernels against the C kernels

Both regions are lifted verbatim, so they write their results through three
pointers rather than returning them. Running one means supplying a machine
state; reading the result back means loading from those pointers afterwards.

This is the check that exercises the flat in-memory encoding against something
outside the formalisation -- a proof of store-then-load cannot, since the two
share the encoding and any consistent lane order round-trips. -/

/-- Three fresh, zeroed 64-byte blocks, and pointers to their starts. -/
def blk : Block := .live { length := 64, bytes := 0#(8 * 64) }
def st : GlobalState where
  alloc := ⟨3⟩
  mem := ⟨((∅ : Std.HashMap BlockId Block).insert ⟨0⟩ blk).insert ⟨1⟩ blk |>.insert ⟨2⟩ blk⟩
def pt (i : Nat) : Pointer := { id := ⟨i⟩, offset := 0 }

/-- Read the three destinations back out of a final state. -/
def readBack3 (s' : GlobalState) :
    List (Option Nat) × List (Option Nat) × List (Option Nat) :=
  let load1 (p : Pointer) : List (Option Nat) :=
    match (SLLVM.load (.value p) QVecTy).run s'.mem with
    | .poison => []
    | .value (v, _) => rd v
  (load1 (pt 0), load1 (pt 1), load1 (pt 2))

def sqrRun : Option (List (Option Nat) × List (Option Nat) × List (Option Nat)) :=
  match (fd_r43x6_quad_sqr_fast.denote
      (quadValMem (.value (pt 0)) (.value (pt 1)) (.value (pt 2)) x03 x14 x25)).run st with
  | .poison => none
  | .value (_, s') => some (readBack3 s')

def mulRun : Option (List (Option Nat) × List (Option Nat) × List (Option Nat)) :=
  match (fd_r43x6_quad_mul_fast.denote
      (quadValMem6 (.value (pt 0)) (.value (pt 1)) (.value (pt 2))
        x03 x14 x25 y03 y14 y25)).run st with
  | .poison => none
  | .value (_, s') => some (readBack3 s')

#eval sqrRun == some (ex sz03, ex sz14, ex sz25)
#eval mulRun == some (ex mz03, ex mz14, ex mz25)

-- Lane `i` of the flat encoding really does live at bits [i*64, (i+1)*64).
#eval
  let bits := vecBits sz03
  (List.range 8).map (fun i => (bits.extractLsb' (i * 64) 64).toNat) == (ex sz03).map (·.getD 0)

end Firedancer.Avx512
