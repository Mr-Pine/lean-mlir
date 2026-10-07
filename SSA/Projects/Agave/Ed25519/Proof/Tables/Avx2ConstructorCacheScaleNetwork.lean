import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScalePacking
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCachePhases
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorConstantValues
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMultiplication

namespace Agave.Ed25519.Tables.Avx2Constructor.CacheScale
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases Avx2PointAdd.CFG
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def initialScale (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v530 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%525)) (E.read (%88))
  let v531 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%525)) (E.read (%105))
  let v532 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v530
  let v533 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v531
  let v534 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%526)) (E.read (%88))
  let v535 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%526)) (E.read (%105))
  let v536 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v534
  let v537 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v535
  let v538 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%527)) (E.read (%88))
  let v539 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%527)) (E.read (%105))
  let v540 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v538
  let v541 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v539
  let v542 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%528)) (E.read (%88))
  let v543 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%528)) (E.read (%105))
  let v544 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v542
  let v545 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v543
  let v546 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%529)) (E.read (%88))
  let v547 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%529)) (E.read (%105))
  let v548 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v546
  let v549 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v547
  let v550 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v532 (E.read (%106))
  let v551 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v533 (E.read (%106))
  let v552 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v536 (E.read (%106))
  let v553 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v537 (E.read (%106))
  let v554 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v540 (E.read (%106))
  let v555 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v541 (E.read (%106))
  let v556 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v544 (E.read (%106))
  let v557 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v545 (E.read (%106))
  let v558 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v548 (E.read (%106))
  let v559 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v549 (E.read (%106))
  let v560 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v550 (E.read (%27))
  let v561 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v560 v551
  let v562 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v550 (E.read (%107))
  let v563 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v554 (E.read (%27))
  let v564 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v563 v555
  let v565 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v554 (E.read (%107))
  let v566 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v561 (E.read (%108))
  let v567 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v566 v552
  let v568 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v561 (E.read (%109))
  let v569 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v564 (E.read (%108))
  let v570 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v569 v556
  let v571 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v564 (E.read (%109))
  let v572 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v567 (E.read (%27))
  let v573 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v572 v553
  let v574 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v570 (E.read (%27))
  let v575 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v574 v557
  let v576 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v573 (E.read (%108))
  let v577 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v576 v565
  let v578 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v575 (E.read (%108))
  let v579 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v578 v558
  let v580 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v577 (E.read (%27))
  let v581 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v580 v571
  let v582 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v579 (E.read (%27))
  let v583 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v582 v559
  let v584 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v583 (E.read (%108))
  let v585 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v584 (E.read (%32))
  let v586 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v585 v562
  let v587 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v586 (E.read (%27))
  let v588 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v587 v568
  let v589 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v586
  let v590 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v589 (E.read (%127))
  let v591 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v588
  let v592 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v590 v591
  let v593 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v567
  let v594 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v593 (E.read (%127))
  let v595 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v573
  let v596 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v595 (E.read (%145))
  let v597 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v594 v596
  let v598 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v581
  let v599 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v577
  let v600 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v599 (E.read (%127))
  let v601 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v600 v598
  let v602 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v570
  let v603 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v602 (E.read (%127))
  let v604 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v575
  let v605 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v604 (E.read (%145))
  let v606 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v603 v605
  let v607 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v579
  let v608 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v607 (E.read (%127))
  let v609 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v583
  let v610 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v609 (E.read (%145))
  let v611 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v608 v610
  E[%530 := v530,
    %531 := v531,
    %532 := v532,
    %533 := v533,
    %534 := v534,
    %535 := v535,
    %536 := v536,
    %537 := v537,
    %538 := v538,
    %539 := v539,
    %540 := v540,
    %541 := v541,
    %542 := v542,
    %543 := v543,
    %544 := v544,
    %545 := v545,
    %546 := v546,
    %547 := v547,
    %548 := v548,
    %549 := v549,
    %550 := v550,
    %551 := v551,
    %552 := v552,
    %553 := v553,
    %554 := v554,
    %555 := v555,
    %556 := v556,
    %557 := v557,
    %558 := v558,
    %559 := v559,
    %560 := v560,
    %561 := v561,
    %562 := v562,
    %563 := v563,
    %564 := v564,
    %565 := v565,
    %566 := v566,
    %567 := v567,
    %568 := v568,
    %569 := v569,
    %570 := v570,
    %571 := v571,
    %572 := v572,
    %573 := v573,
    %574 := v574,
    %575 := v575,
    %576 := v576,
    %577 := v577,
    %578 := v578,
    %579 := v579,
    %580 := v580,
    %581 := v581,
    %582 := v582,
    %583 := v583,
    %584 := v584,
    %585 := v585,
    %586 := v586,
    %587 := v587,
    %588 := v588,
    %589 := v589,
    %590 := v590,
    %591 := v591,
    %592 := v592,
    %593 := v593,
    %594 := v594,
    %595 := v595,
    %596 := v596,
    %597 := v597,
    %598 := v598,
    %599 := v599,
    %600 := v600,
    %601 := v601,
    %602 := v602,
    %603 := v603,
    %604 := v604,
    %605 := v605,
    %606 := v606,
    %607 := v607,
    %608 := v608,
    %609 := v609,
    %610 := v610,
    %611 := v611]

theorem initialScale_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb0 p) E 530 82 s = .value (initialScale E, s) := by
  simp [runSlice, kernel.bb0, initialScale, List.foldlM_cons, List.foldlM_nil,
    Instr.run, UnOp.compute, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, -reduceShufflevector]

def successorScale (E : ⟪kernel.Γ⟫) : ⟪kernel.Γ⟫ :=
  let v906 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%901)) (E.read (%88))
  let v907 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%901)) (E.read (%105))
  let v908 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v906
  let v909 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v907
  let v910 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%902)) (E.read (%88))
  let v911 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%902)) (E.read (%105))
  let v912 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v910
  let v913 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v911
  let v914 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%903)) (E.read (%88))
  let v915 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%903)) (E.read (%105))
  let v916 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v914
  let v917 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v915
  let v918 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%904)) (E.read (%88))
  let v919 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%904)) (E.read (%105))
  let v920 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v918
  let v921 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v919
  let v922 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 8, some 1, some 9, some 4, some 12, some 5, some 13] (E.read (%905)) (E.read (%88))
  let v923 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 2, some 10, some 3, some 11, some 6, some 14, some 7, some 15] (E.read (%905)) (E.read (%105))
  let v924 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v922
  let v925 : ⟦Ty.vec 4 64⟧ := Operation.bitcast (by decide) v923
  let v926 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v908 (E.read (%106))
  let v927 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v909 (E.read (%106))
  let v928 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v912 (E.read (%106))
  let v929 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v913 (E.read (%106))
  let v930 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v916 (E.read (%106))
  let v931 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v917 (E.read (%106))
  let v932 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v920 (E.read (%106))
  let v933 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v921 (E.read (%106))
  let v934 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v924 (E.read (%106))
  let v935 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v925 (E.read (%106))
  let v936 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v926 (E.read (%27))
  let v937 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v936 v927
  let v938 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v926 (E.read (%107))
  let v939 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v930 (E.read (%27))
  let v940 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v939 v931
  let v941 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v930 (E.read (%107))
  let v942 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v937 (E.read (%108))
  let v943 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v942 v928
  let v944 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v937 (E.read (%109))
  let v945 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v940 (E.read (%108))
  let v946 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v945 v932
  let v947 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.and) v940 (E.read (%109))
  let v948 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v943 (E.read (%27))
  let v949 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v948 v929
  let v950 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v946 (E.read (%27))
  let v951 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v950 v933
  let v952 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v949 (E.read (%108))
  let v953 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v952 v941
  let v954 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v951 (E.read (%108))
  let v955 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v954 v934
  let v956 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v953 (E.read (%27))
  let v957 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v956 v947
  let v958 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v955 (E.read (%27))
  let v959 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v958 v935
  let v960 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v959 (E.read (%108))
  let v961 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.mul {nsw := true, nuw := true}) v960 (E.read (%32))
  let v962 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v961 v938
  let v963 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.lshr false) v962 (E.read (%27))
  let v964 : ⟦Ty.vec 4 64⟧ := Vector.zipWith (Operation.add {nsw := true, nuw := true}) v963 v944
  let v965 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v962
  let v966 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v965 (E.read (%127))
  let v967 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v964
  let v968 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v966 v967
  let v969 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v943
  let v970 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v969 (E.read (%127))
  let v971 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v949
  let v972 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v971 (E.read (%145))
  let v973 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v970 v972
  let v974 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v957
  let v975 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v953
  let v976 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v975 (E.read (%127))
  let v977 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v976 v974
  let v978 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v946
  let v979 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v978 (E.read (%127))
  let v980 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v951
  let v981 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v980 (E.read (%145))
  let v982 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v979 v981
  let v983 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v955
  let v984 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v983 (E.read (%127))
  let v985 : ⟦Ty.vec 8 32⟧ := Operation.bitcast (by decide) v959
  let v986 : ⟦Ty.vec 8 32⟧ := Vector.zipWith (Operation.and) v985 (E.read (%145))
  let v987 : ⟦Ty.vec 8 32⟧ := Operation.shufflevector #v[some 0, some 2, some 8, some 10, some 4, some 6, some 12, some 14] v984 v986
  E[%906 := v906,
    %907 := v907,
    %908 := v908,
    %909 := v909,
    %910 := v910,
    %911 := v911,
    %912 := v912,
    %913 := v913,
    %914 := v914,
    %915 := v915,
    %916 := v916,
    %917 := v917,
    %918 := v918,
    %919 := v919,
    %920 := v920,
    %921 := v921,
    %922 := v922,
    %923 := v923,
    %924 := v924,
    %925 := v925,
    %926 := v926,
    %927 := v927,
    %928 := v928,
    %929 := v929,
    %930 := v930,
    %931 := v931,
    %932 := v932,
    %933 := v933,
    %934 := v934,
    %935 := v935,
    %936 := v936,
    %937 := v937,
    %938 := v938,
    %939 := v939,
    %940 := v940,
    %941 := v941,
    %942 := v942,
    %943 := v943,
    %944 := v944,
    %945 := v945,
    %946 := v946,
    %947 := v947,
    %948 := v948,
    %949 := v949,
    %950 := v950,
    %951 := v951,
    %952 := v952,
    %953 := v953,
    %954 := v954,
    %955 := v955,
    %956 := v956,
    %957 := v957,
    %958 := v958,
    %959 := v959,
    %960 := v960,
    %961 := v961,
    %962 := v962,
    %963 := v963,
    %964 := v964,
    %965 := v965,
    %966 := v966,
    %967 := v967,
    %968 := v968,
    %969 := v969,
    %970 := v970,
    %971 := v971,
    %972 := v972,
    %973 := v973,
    %974 := v974,
    %975 := v975,
    %976 := v976,
    %977 := v977,
    %978 := v978,
    %979 := v979,
    %980 := v980,
    %981 := v981,
    %982 := v982,
    %983 := v983,
    %984 := v984,
    %985 := v985,
    %986 := v986,
    %987 := v987]

theorem successorScale_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (s : GlobalState) :
    runSlice (kernel.bb2 p) E 130 82 s = .value (successorScale E, s) := by
  simp [runSlice, kernel.bb2, successorScale, List.foldlM_cons, List.foldlM_nil,
    Instr.run, UnOp.compute, BinOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, -reduceShufflevector]

/-- Only the ten compiler constants consumed by the scale/reduce interval. -/
structure ConstantsReady (E : ⟪kernel.Γ⟫) : Prop where
  r27 : E.read (%27) = replicateWord 26
  r32 : E.read (%32) = replicateWord 19
  r88 : E.read (%88) = Avx2SquareNegateD.evenZeros
  r105 : E.read (%105) = Avx2SquareNegateD.oddZeros
  r106 : E.read (%106) = Ty.wrap (t := .vec 4 64) (wideVec scaleConstant)
  r107 : E.read (%107) = replicateWord 67108862
  r108 : E.read (%108) = replicateWord 25
  r109 : E.read (%109) = replicateWord 33554431
  r127 : E.read (%127) = lowMask 67108863
  r145 : E.read (%145) = lowMask 33554431

theorem constants_ready (E : ⟪kernel.Γ⟫) : ConstantsReady (Constants.result E) := by
  constructor
  · rw [Constants.read_27]; rfl
  · rw [Constants.read_32]; rfl
  · rw [Constants.read_88]; rfl
  · rw [Constants.read_105]; rfl
  · rw [Constants.read_106]
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [Ty.wrap_vec, wideVec, scaleConstant]
  · rw [Constants.read_107]; rfl
  · rw [Constants.read_108]; rfl
  · rw [Constants.read_109]; rfl
  · rw [Constants.read_127]; rfl
  · rw [Constants.read_145]; rfl

def initialInputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%525), E.read (%526), E.read (%527), E.read (%528), E.read (%529)]

def initialOutputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%592), E.read (%597), E.read (%601), E.read (%606), E.read (%611)]

theorem initial_network (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E) (k : Fin 5) :
    initialOutputReads (initialScale E) k =
      packInstructions (reductionInstructions (scaleInstructions (initialInputReads E))) k := by
  rcases hc with ⟨h27,h32,h88,h105,h106,h107,h108,h109,h127,h145⟩
  fin_cases k <;>
    simp only [initialOutputReads, initialScale, initialInputReads,
      packInstructions, reductionInstructions, scaleInstructions, widenInstructions,
      evenIndex, oddIndex, pairMask, Avx2SquareNegateD.evenMask, Avx2SquareNegateD.oddMask,
      h27,h32,h88,h105,h106,h107,h108,h109,h127,h145, mlir_env]
  all_goals rfl

theorem initial_point (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E)
    {P : Point} (hP : pointWide P)
    (hin : ∀ k, initialInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint P k))
    (k : Fin 5) :
    initialOutputReads (initialScale E) k = Ty.wrap (packPoint (scaledPoint P) k) := by
  rw [initial_network E hc]
  have hi := funext hin
  rw [hi, instructions_point hP]

def successorInputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%901), E.read (%902), E.read (%903), E.read (%904), E.read (%905)]

def successorOutputReads (E : ⟪kernel.Γ⟫) : Fin 5 → ⟦Ty.vec 8 32⟧ :=
  ![E.read (%968), E.read (%973), E.read (%977), E.read (%982), E.read (%987)]

theorem successor_network (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E) (k : Fin 5) :
    successorOutputReads (successorScale E) k =
      packInstructions (reductionInstructions (scaleInstructions (successorInputReads E))) k := by
  rcases hc with ⟨h27,h32,h88,h105,h106,h107,h108,h109,h127,h145⟩
  fin_cases k <;>
    simp only [successorOutputReads, successorScale, successorInputReads,
      packInstructions, reductionInstructions, scaleInstructions, widenInstructions,
      evenIndex, oddIndex, pairMask, Avx2SquareNegateD.evenMask, Avx2SquareNegateD.oddMask,
      h27,h32,h88,h105,h106,h107,h108,h109,h127,h145, mlir_env]
  all_goals rfl

theorem successor_point (E : ⟪kernel.Γ⟫) (hc : ConstantsReady E)
    {P : Point} (hP : pointWide P)
    (hin : ∀ k, successorInputReads E k = Ty.wrap (t := .vec 8 32) (packPoint P k))
    (k : Fin 5) :
    successorOutputReads (successorScale E) k = Ty.wrap (packPoint (scaledPoint P) k) := by
  rw [successor_network E hc]
  have hi := funext hin
  rw [hi, instructions_point hP]

end Agave.Ed25519.Tables.Avx2Constructor.CacheScale
