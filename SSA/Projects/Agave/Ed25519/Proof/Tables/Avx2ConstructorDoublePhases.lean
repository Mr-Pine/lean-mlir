import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2Constructor
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGPhases

/-! Exact original constructor doubling instructions, with inbounds GEPs,
all vector operations and stores retained. Mathematical vector equations
reuse the checked point-double preparation and mixing semantics. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Double
open LeanMLIR.RIR Avx2PointDouble
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
open Avx2PointAdd.Phases (packed_unflatten)
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

structure Constants (E : ⟪kernel.Γ⟫) : Prop where
  c32 : E.read (%4) = .value 32#64
  c64 : E.read (%8) = .value 64#64
  c96 : E.read (%12) = .value 96#64
  c128 : E.read (%16) = .value 128#64
  poison : E.read (%31) = Ty.poisoned (.vec 8 32)
  one : E.read (%230) = Ty.wrap (#v[1, 1, 1, 1, 1, 1, 1, 1] : Vec32)
  «prefix» : E.read (%247) = zeroPrefix
  difference : E.read (%264) = zeroDifference
  lazy0 : E.read (%281) = lazyConstants 134217690#32 67108862#32
  lazyN : E.read (%298) = lazyConstants 134217726#32 67108862#32
  sum : E.read (%315) = zeroSum

structure Pointers (E : ⟪kernel.Γ⟫) (prepared square result : Pointer) : Prop where
  r357 : E.read (%357) = .value (prepared)
  r694 : E.read (%694) = .value (prepared.add 32#64)
  r695 : E.read (%695) = .value (prepared.add 64#64)
  r696 : E.read (%696) = .value (prepared.add 96#64)
  r697 : E.read (%697) = .value (prepared.add 128#64)
  r356 : E.read (%356) = .value (square)
  r703 : E.read (%703) = .value (square.add 32#64)
  r704 : E.read (%704) = .value (square.add 64#64)
  r705 : E.read (%705) = .value (square.add 96#64)
  r706 : E.read (%706) = .value (square.add 128#64)
  r359 : E.read (%359) = .value (result)

def inputReads (E : ⟪kernel.Γ⟫) (a : Blocks) : Prop :=
  E.read (%504) = Ty.wrap (a 0) ∧
  E.read (%485) = Ty.wrap (a 1) ∧
  E.read (%489) = Ty.wrap (a 2) ∧
  E.read (%493) = Ty.wrap (a 3) ∧
  E.read (%497) = Ty.wrap (a 4)

def prepareEnv (E : ⟪kernel.Γ⟫) (a b : Pointer) : ⟪kernel.Γ⟫ :=
  let v689 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%504)) (E.read (%31))
  let v690 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%485)) (E.read (%31))
  let v691 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%489)) (E.read (%31))
  let v692 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%493)) (E.read (%31))
  let v693 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 1, none, some 3] (E.read (%497)) (E.read (%31))
  let v698 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%504)) (E.read (%31))
  let v699 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%485)) (E.read (%31))
  let v700 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%489)) (E.read (%31))
  let v701 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%493)) (E.read (%31))
  let v702 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[none, none, none, none, none, some 0, none, some 2] (E.read (%497)) (E.read (%31))
  let v707 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v698 v689
  let v708 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v699 v690
  let v709 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v700 v691
  let v710 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v701 v692
  let v711 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v702 v693
  let v712 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%504)) v707
  let v713 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%485)) v708
  let v714 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%489)) v709
  let v715 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%493)) v710
  let v716 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] (E.read (%497)) v711
  E[%689 := v689,
    %690 := v690,
    %691 := v691,
    %692 := v692,
    %693 := v693,
    %694 := .value (a.add 32#64),
    %695 := .value (a.add 64#64),
    %696 := .value (a.add 96#64),
    %697 := .value (a.add 128#64),
    %698 := v698,
    %699 := v699,
    %700 := v700,
    %701 := v701,
    %702 := v702,
    %703 := .value (b.add 32#64),
    %704 := .value (b.add 64#64),
    %705 := .value (b.add 96#64),
    %706 := .value (b.add 128#64),
    %707 := v707,
    %708 := v708,
    %709 := v709,
    %710 := v710,
    %711 := v711,
    %712 := v712,
    %713 := v713,
    %714 := v714,
    %715 := v715,
    %716 := v716]

theorem prepare_frame (E : ⟪kernel.Γ⟫) (a b : Pointer) :
    RegisterFrame 689 kernel.Γ.n E (prepareEnv E a b) := by
  unfold prepareEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem prepare_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (a b : Pointer) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hc : Constants E) (hpa : E.read (%357) = .value a) (hpb : E.read (%356) = .value b) :
    runSlice (kernel.bb0 p) E 729 31 s = .value (prepareEnv E a b, s) := by
  have ha32 := ha.gep (k := 32) (by decide)
  have ha64 := ha.gep (k := 64) (by decide)
  have ha96 := ha.gep (k := 96) (by decide)
  have ha128 := ha.gep (k := 128) (by decide)
  have hb32 := hb.gep (k := 32) (by decide)
  have hb64 := hb.gep (k := 64) (by decide)
  have hb96 := hb.gep (k := 96) (by decide)
  have hb128 := hb.gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at ha32 ha64 ha96 ha128 hb32 hb64 hb96 hb128
  simp [runSlice, kernel.bb0, prepareEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env,
    GepIndex.inboundsOffset, hpa, hpb, hc.c32, hc.c64, hc.c96, hc.c128,
    ha32, ha64, ha96, ha128, hb32, hb64, hb96, hb128, -reduceShufflevector]

def preparedReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%712), E.read (%713), E.read (%714), E.read (%715), E.read (%716)]

theorem prepare_field (E : ⟪kernel.Γ⟫) (a b : Pointer) (v : Blocks)
    (hc : Constants E) (ha : inputReads E v) (k : Fin 5) :
    preparedReads (prepareEnv E a b) k = Ty.wrap (prepareBlocks v k) := by
  rcases ha with ⟨h0, h1, h2, h3, h4⟩
  have hnetwork : preparedReads (prepareEnv E a b) k = prepareOperation (Ty.wrap (v k)) := by
    fin_cases k <;> simp [preparedReads, prepareEnv, prepareOperation, maskA, maskB,
      maskBlend, hc.poison, h0, h1, h2, h3, h4, mlir_env]
  exact hnetwork.trans (prepareOperation_value (v k))

def mixEnv (E : ⟪kernel.Γ⟫) (v : Blocks) : ⟪kernel.Γ⟫ :=
  let v717 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 0)
  let v718 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 1)
  let v719 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 2)
  let v720 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 3)
  let v721 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v717 (E.read (%31))
  let v722 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v718 (E.read (%31))
  let v723 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v719 (E.read (%31))
  let v724 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v720 (E.read (%31))
  let v725 : ⟦Ty.vec 8 32⟧ := Ty.wrap (v 4)
  let v726 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 0, some 2, some 2, some 0, some 0, some 2, some 2] v725 (E.read (%31))
  let v727 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v717 (E.read (%31))
  let v728 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v718 (E.read (%31))
  let v729 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v719 (E.read (%31))
  let v730 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v720 (E.read (%31))
  let v731 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 1, some 1, some 3, some 3, some 1, some 1, some 3, some 3] v725 (E.read (%31))
  let v732 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v717 (E.read (%230))
  let v733 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v718 (E.read (%230))
  let v734 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v719 (E.read (%230))
  let v735 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v720 (E.read (%230))
  let v736 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.shl {}) v725 (E.read (%230))
  let v737 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%247)) v732
  let v738 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%247)) v733
  let v739 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%247)) v734
  let v740 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%247)) v735
  let v741 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 12, none, some 14, none] (E.read (%247)) v736
  let v742 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v737 v717
  let v743 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v738 v718
  let v744 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v739 v719
  let v745 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v740 v720
  let v746 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 1, some 2, some 3, some 4, some 13, some 6, some 15] v741 v725
  let v747 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v727 (E.read (%264))
  let v748 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v728 (E.read (%264))
  let v749 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v729 (E.read (%264))
  let v750 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v730 (E.read (%264))
  let v751 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] v731 (E.read (%264))
  let v752 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%281)) v727
  let v753 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%298)) v728
  let v754 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%298)) v729
  let v755 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%298)) v730
  let v756 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.sub {}) (E.read (%298)) v731
  let v757 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%315)) v752
  let v758 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%315)) v753
  let v759 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%315)) v754
  let v760 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%315)) v755
  let v761 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 9, some 2, some 11, some 12, some 5, some 14, some 7] (E.read (%315)) v756
  let v762 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v747 v721
  let v763 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v762 v742
  let v764 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v763 v757
  let v765 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v748 v722
  let v766 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v765 v743
  let v767 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v766 v758
  let v768 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v749 v723
  let v769 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v768 v744
  let v770 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v769 v759
  let v771 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v750 v724
  let v772 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v771 v745
  let v773 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v772 v760
  let v774 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v751 v726
  let v775 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v774 v746
  let v776 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.add {}) v775 v761
  let v777 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v764 (E.read (%31))
  let v778 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v767 (E.read (%31))
  let v779 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v770 (E.read (%31))
  let v780 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v773 (E.read (%31))
  let v781 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7] v776 (E.read (%31))
  E[%717 := v717,
    %718 := v718,
    %719 := v719,
    %720 := v720,
    %721 := v721,
    %722 := v722,
    %723 := v723,
    %724 := v724,
    %725 := v725,
    %726 := v726,
    %727 := v727,
    %728 := v728,
    %729 := v729,
    %730 := v730,
    %731 := v731,
    %732 := v732,
    %733 := v733,
    %734 := v734,
    %735 := v735,
    %736 := v736,
    %737 := v737,
    %738 := v738,
    %739 := v739,
    %740 := v740,
    %741 := v741,
    %742 := v742,
    %743 := v743,
    %744 := v744,
    %745 := v745,
    %746 := v746,
    %747 := v747,
    %748 := v748,
    %749 := v749,
    %750 := v750,
    %751 := v751,
    %752 := v752,
    %753 := v753,
    %754 := v754,
    %755 := v755,
    %756 := v756,
    %757 := v757,
    %758 := v758,
    %759 := v759,
    %760 := v760,
    %761 := v761,
    %762 := v762,
    %763 := v763,
    %764 := v764,
    %765 := v765,
    %766 := v766,
    %767 := v767,
    %768 := v768,
    %769 := v769,
    %770 := v770,
    %771 := v771,
    %772 := v772,
    %773 := v773,
    %774 := v774,
    %775 := v775,
    %776 := v776,
    %777 := v777,
    %778 := v778,
    %779 := v779,
    %780 := v780,
    %781 := v781]

theorem mix_frame (E : ⟪kernel.Γ⟫) (v : Blocks) :
    RegisterFrame 717 kernel.Γ.n E (mixEnv E v) := by
  unfold mixEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem mix_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks)
    (hr : SmallRange s.mem r 160)
    (hv : Avx2FieldMul.Execution.readBlocks s.mem r = v)
    (hp0 : E.read (%356) = .value r)
    (hp1 : E.read (%703) = .value (r.add 32#64))
    (hp2 : E.read (%704) = .value (r.add 64#64))
    (hp3 : E.read (%705) = .value (r.add 96#64))
    (hp4 : E.read (%706) = .value (r.add 128#64)) :
    runSlice (kernel.bb0 p) E 766 65 s = .value (mixEnv E v, s) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hv0 := packed_unflatten s.mem r v hv 0
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 0#64) 256) = Ty.wrap (v 0) at hv0
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv0
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hv1 := packed_unflatten s.mem r v hv 1
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 32#64) 256) = Ty.wrap (v 1) at hv1
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv1
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hv2 := packed_unflatten s.mem r v hv 2
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 64#64) 256) = Ty.wrap (v 2) at hv2
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv2
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hv3 := packed_unflatten s.mem r v hv 3
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 96#64) 256) = Ty.wrap (v 3) at hv3
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv3
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  have hv4 := packed_unflatten s.mem r v hv 4
  change (Ty.vec 8 32).unflatten (s.mem.readAt (r.add 128#64) 256) = Ty.wrap (v 4) at hv4
  simp only [Ty.unflatten_vec, Pointer.add_zero] at hv4
  simp only [Pointer.add_zero] at hf0 hv0
  simp (config := {maxSteps := 500000}) [runSlice, kernel.bb0, mixEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.load, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hf0, hv0, hp1, hf1, hv1,
    hp2, hf2, hv2, hp3, hf3, hv3, hp4, hf4, hv4, -reduceShufflevector]

def mixedReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%764), E.read (%767), E.read (%770), E.read (%773), E.read (%776)]
def rightReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%777), E.read (%778), E.read (%779), E.read (%780), E.read (%781)]

theorem mix_network (E : ⟪kernel.Γ⟫) (v : Blocks)
    (hc : Constants E) (k : Fin 5) :
    mixedReads (mixEnv E v) k = mixOperation (Ty.wrap (v k))
      (Avx2PointAdd.Phases.evenConstant k) (Avx2PointAdd.Phases.oddConstant k) := by
  fin_cases k <;> simp [mixedReads, mixEnv, mixOperation, hc.poison, hc.one,
    hc.prefix, hc.difference, hc.lazy0, hc.lazyN, hc.sum,
    Avx2PointAdd.Phases.evenConstant, Avx2PointAdd.Phases.oddConstant,
    Avx2PointAdd.Phases.evenIndex, Avx2PointAdd.Phases.oddIndex,
    Avx2PointAdd.twiceP, Avx2PointAdd.word, mlir_env]

theorem mix_field (E : ⟪kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    mixedReads (mixEnv E (packCoordinates q)) k = Ty.wrap (packCoordinates (mix q) k) := by
  rw [mix_network E _ hc k, mixOperation_value, mixBlock_packed hq]

theorem right_field (E : ⟪kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    rightReads (mixEnv E (packCoordinates q)) k = Ty.wrap (packCoordinates (right q) k) := by
  have h : rightReads (mixEnv E (packCoordinates q)) k =
      Operation.shufflevector #v[some 5, some 1, some 7, some 3, some 1, some 5, some 3, some 7]
        (mixedReads (mixEnv E (packCoordinates q)) k) (Ty.poisoned (.vec 8 32)) := by
    fin_cases k <;> simp [rightReads, mixedReads, mixEnv, hc.poison, mlir_env]
  rw [h, mix_field E q hc hq k, rightBlock_shuffle, rightBlock_packed]

def leftEnv (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v782 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%764)) (E.read (%31))
  let v783 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%767)) (E.read (%31))
  let v784 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%770)) (E.read (%31))
  let v785 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%773)) (E.read (%31))
  let v786 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2] (E.read (%776)) (E.read (%31))
  E[%782 := v782,
    %783 := v783,
    %784 := v784,
    %785 := v785,
    %786 := v786]

theorem left_frame (E : ⟪kernel.Γ⟫) :
    RegisterFrame 717 kernel.Γ.n E (leftEnv E) := by
  unfold leftEnv
  repeat' apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem left_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb0 p) E 836 5 s = .value (leftEnv E, s) := by
  simp [runSlice, kernel.bb0, leftEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env]

def leftReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%782), E.read (%783), E.read (%784), E.read (%785), E.read (%786)]

theorem left_field (E : ⟪kernel.Γ⟫) (q : Coordinates)
    (hc : Constants E) (hq : PointBound q) (k : Fin 5) :
    leftReads (leftEnv (mixEnv E (packCoordinates q))) k = Ty.wrap (packCoordinates (left q) k) := by
  have h : leftReads (leftEnv (mixEnv E (packCoordinates q))) k =
      Operation.shufflevector #v[some 4, some 0, some 6, some 2, some 4, some 0, some 6, some 2]
        (mixedReads (mixEnv E (packCoordinates q)) k) (Ty.poisoned (.vec 8 32)) := by
    fin_cases k <;> simp [leftReads, leftEnv, mixedReads, mixEnv, hc.poison, mlir_env]
  rw [h, mix_field E q hc hq k, leftBlock_shuffle, leftBlock_packed]

theorem prepared_stores (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hp0 : E.read (%357) = .value r)
    (hv0 : E.read (%712) = Ty.wrap (v 0))
    (hp1 : E.read (%694) = .value (r.add 32#64))
    (hv1 : E.read (%713) = Ty.wrap (v 1))
    (hp2 : E.read (%695) = .value (r.add 64#64))
    (hv2 : E.read (%714) = Ty.wrap (v 2))
    (hp3 : E.read (%696) = .value (r.add 96#64))
    (hv3 : E.read (%715) = Ty.wrap (v 3))
    (hp4 : E.read (%697) = .value (r.add 128#64))
    (hv4 : E.read (%716) = Ty.wrap (v 4)) :
    runSlice (kernel.bb0 p) E 760 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb0, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem right_stores (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hp0 : E.read (%356) = .value r)
    (hv0 : E.read (%777) = Ty.wrap (v 0))
    (hp1 : E.read (%703) = .value (r.add 32#64))
    (hv1 : E.read (%778) = Ty.wrap (v 1))
    (hp2 : E.read (%704) = .value (r.add 64#64))
    (hv2 : E.read (%779) = Ty.wrap (v 2))
    (hp3 : E.read (%705) = .value (r.add 96#64))
    (hv3 : E.read (%780) = Ty.wrap (v 3))
    (hp4 : E.read (%706) = .value (r.add 128#64))
    (hv4 : E.read (%781) = Ty.wrap (v 4)) :
    runSlice (kernel.bb0 p) E 831 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb0, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]

theorem left_stores (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (r : Pointer) (v : Blocks) (hr : SmallRange s.mem r 160)
    (hp0 : E.read (%357) = .value r)
    (hv0 : E.read (%782) = Ty.wrap (v 0))
    (hp1 : E.read (%694) = .value (r.add 32#64))
    (hv1 : E.read (%783) = Ty.wrap (v 1))
    (hp2 : E.read (%695) = .value (r.add 64#64))
    (hv2 : E.read (%784) = Ty.wrap (v 2))
    (hp3 : E.read (%696) = .value (r.add 96#64))
    (hv3 : E.read (%785) = Ty.wrap (v 3))
    (hp4 : E.read (%697) = .value (r.add 128#64))
    (hv4 : E.read (%786) = Ty.wrap (v 4)) :
    runSlice (kernel.bb0 p) E 841 5 s =
      .value (E, {s with mem := Avx2FieldMul.Execution.storeBlocks s.mem r v}) := by
  have hf0 := hr.fits_add (k := 0) (count := 32) (by decide)
  have hf1 := hr.fits_add (k := 32) (count := 32) (by decide)
  have hf2 := hr.fits_add (k := 64) (count := 32) (by decide)
  have hf3 := hr.fits_add (k := 96) (count := 32) (by decide)
  have hf4 := hr.fits_add (k := 128) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hf0
  simp [runSlice, kernel.bb0, Avx2FieldMul.Execution.storeBlocks,
    List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.store,
    Ty.flatten_wrap_vec, Fits.storeAt_iff, EffectM.bind_eq, EffectM.pure_eq,
    mlir_effect, mlir_env, throwUBIf, hp0, hv0, hf0, hp1, hv1, hf1, hp2, hv2, hf2, hp3, hv3, hf3, hp4, hv4, hf4]


end Agave.Ed25519.Tables.Avx2Constructor.Double
