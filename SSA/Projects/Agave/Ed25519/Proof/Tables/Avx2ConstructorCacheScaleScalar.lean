import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheScaleWords

namespace Agave.Ed25519.Tables.Avx2Constructor.CacheScale
open LeanMLIR.RIR Avx2PointAdd
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

/-- The ten values before the source's final bitcast/mask/shuffle packing. -/
def scalarInstructions (z : Fin 10 → Operation.IntW 64) : Fin 10 → Operation.IntW 64 :=
  let v550 := z 0
  let v551 := z 1
  let v552 := z 2
  let v553 := z 3
  let v554 := z 4
  let v555 := z 5
  let v556 := z 6
  let v557 := z 7
  let v558 := z 8
  let v559 := z 9
  let v560 := Operation.lshr false v550 (natWord 26)
  let v561 := Operation.add {nsw := true, nuw := true} v560 v551
  let v562 := Operation.and v550 (natWord 67108862)
  let v563 := Operation.lshr false v554 (natWord 26)
  let v564 := Operation.add {nsw := true, nuw := true} v563 v555
  let v565 := Operation.and v554 (natWord 67108862)
  let v566 := Operation.lshr false v561 (natWord 25)
  let v567 := Operation.add {nsw := true, nuw := true} v566 v552
  let v568 := Operation.and v561 (natWord 33554431)
  let v569 := Operation.lshr false v564 (natWord 25)
  let v570 := Operation.add {nsw := true, nuw := true} v569 v556
  let v571 := Operation.and v564 (natWord 33554431)
  let v572 := Operation.lshr false v567 (natWord 26)
  let v573 := Operation.add {nsw := true, nuw := true} v572 v553
  let v574 := Operation.lshr false v570 (natWord 26)
  let v575 := Operation.add {nsw := true, nuw := true} v574 v557
  let v576 := Operation.lshr false v573 (natWord 25)
  let v577 := Operation.add {nsw := true, nuw := true} v576 v565
  let v578 := Operation.lshr false v575 (natWord 25)
  let v579 := Operation.add {nsw := true, nuw := true} v578 v558
  let v580 := Operation.lshr false v577 (natWord 26)
  let v581 := Operation.add {nsw := true, nuw := true} v580 v571
  let v582 := Operation.lshr false v579 (natWord 26)
  let v583 := Operation.add {nsw := true, nuw := true} v582 v559
  let v584 := Operation.lshr false v583 (natWord 25)
  let v585 := Operation.mul {nsw := true, nuw := true} v584 (natWord 19)
  let v586 := Operation.add {nsw := true, nuw := true} v585 v562
  let v587 := Operation.lshr false v586 (natWord 26)
  let v588 := Operation.add {nsw := true, nuw := true} v587 v568
  ![v586, v588, v567, v573, v577, v581, v570, v575, v579, v583]

def scalarNat (z : Reduce64.Columns) : Reduce64.Columns :=
  let n550 := z 0
  let n551 := z 1
  let n552 := z 2
  let n553 := z 3
  let n554 := z 4
  let n555 := z 5
  let n556 := z 6
  let n557 := z 7
  let n558 := z 8
  let n559 := z 9
  let n560 := n550 / 2^26
  let n561 := n560 + n551
  let n562 := n550 % 2^26
  let n563 := n554 / 2^26
  let n564 := n563 + n555
  let n565 := n554 % 2^26
  let n566 := n561 / 2^25
  let n567 := n566 + n552
  let n568 := n561 % 2^25
  let n569 := n564 / 2^25
  let n570 := n569 + n556
  let n571 := n564 % 2^25
  let n572 := n567 / 2^26
  let n573 := n572 + n553
  let n574 := n570 / 2^26
  let n575 := n574 + n557
  let n576 := n573 / 2^25
  let n577 := n576 + n565
  let n578 := n575 / 2^25
  let n579 := n578 + n558
  let n580 := n577 / 2^26
  let n581 := n580 + n571
  let n582 := n579 / 2^26
  let n583 := n582 + n559
  let n584 := n583 / 2^25
  let n585 := n584 * 19
  let n586 := n585 + n562
  let n587 := n586 / 2^26
  let n588 := n587 + n568
  ![n586, n588, n567, n573, n577, n581, n570, n575, n579, n583]

theorem scalarInstructions_nat (z : Reduce64.Columns)
    (hz : ∀ i, z i < 2^50) (he : ∀ i, z i % 2 = 0) :
    scalarInstructions (fun i => natWord (z i)) = fun i => natWord (scalarNat z i) := by
  have h0 := hz 0; have h1 := hz 1; have h2 := hz 2; have h3 := hz 3
  have h4 := hz 4; have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have h8 := hz 8; have h9 := hz 9
  have he0 := he 0; have he4 := he 4
  let n550 := z 0
  let n551 := z 1
  let n552 := z 2
  let n553 := z 3
  let n554 := z 4
  let n555 := z 5
  let n556 := z 6
  let n557 := z 7
  let n558 := z 8
  let n559 := z 9
  let n560 := n550 / 2^26
  let n561 := n560 + n551
  let n562 := n550 % 2^26
  let n563 := n554 / 2^26
  let n564 := n563 + n555
  let n565 := n554 % 2^26
  let n566 := n561 / 2^25
  let n567 := n566 + n552
  let n568 := n561 % 2^25
  let n569 := n564 / 2^25
  let n570 := n569 + n556
  let n571 := n564 % 2^25
  let n572 := n567 / 2^26
  let n573 := n572 + n553
  let n574 := n570 / 2^26
  let n575 := n574 + n557
  let n576 := n573 / 2^25
  let n577 := n576 + n565
  let n578 := n575 / 2^25
  let n579 := n578 + n558
  let n580 := n577 / 2^26
  let n581 := n580 + n571
  let n582 := n579 / 2^26
  let n583 := n582 + n559
  let n584 := n583 / 2^25
  let n585 := n584 * 19
  let n586 := n585 + n562
  let n587 := n586 / 2^26
  let n588 := n587 + n568
  have h560 : Operation.lshr false (natWord n550) (natWord 26) = natWord n560 := shr_nat n550 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h561 : Operation.add {nsw := true, nuw := true} (natWord n560) (natWord n551) = natWord n561 := add_nat n560 n551 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h562 : Operation.and (natWord n550) (natWord 67108862) = natWord n562 := and_even_mask26 n550 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (he 0)
  have h563 : Operation.lshr false (natWord n554) (natWord 26) = natWord n563 := shr_nat n554 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h564 : Operation.add {nsw := true, nuw := true} (natWord n563) (natWord n555) = natWord n564 := add_nat n563 n555 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h565 : Operation.and (natWord n554) (natWord 67108862) = natWord n565 := and_even_mask26 n554 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (he 4)
  have h566 : Operation.lshr false (natWord n561) (natWord 25) = natWord n566 := shr_nat n561 25 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h567 : Operation.add {nsw := true, nuw := true} (natWord n566) (natWord n552) = natWord n567 := add_nat n566 n552 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h568 : Operation.and (natWord n561) (natWord 33554431) = natWord n568 := and_mask25 n561 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h569 : Operation.lshr false (natWord n564) (natWord 25) = natWord n569 := shr_nat n564 25 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h570 : Operation.add {nsw := true, nuw := true} (natWord n569) (natWord n556) = natWord n570 := add_nat n569 n556 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h571 : Operation.and (natWord n564) (natWord 33554431) = natWord n571 := and_mask25 n564 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h572 : Operation.lshr false (natWord n567) (natWord 26) = natWord n572 := shr_nat n567 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h573 : Operation.add {nsw := true, nuw := true} (natWord n572) (natWord n553) = natWord n573 := add_nat n572 n553 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h574 : Operation.lshr false (natWord n570) (natWord 26) = natWord n574 := shr_nat n570 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h575 : Operation.add {nsw := true, nuw := true} (natWord n574) (natWord n557) = natWord n575 := add_nat n574 n557 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h576 : Operation.lshr false (natWord n573) (natWord 25) = natWord n576 := shr_nat n573 25 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h577 : Operation.add {nsw := true, nuw := true} (natWord n576) (natWord n565) = natWord n577 := add_nat n576 n565 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h578 : Operation.lshr false (natWord n575) (natWord 25) = natWord n578 := shr_nat n575 25 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h579 : Operation.add {nsw := true, nuw := true} (natWord n578) (natWord n558) = natWord n579 := add_nat n578 n558 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h580 : Operation.lshr false (natWord n577) (natWord 26) = natWord n580 := shr_nat n577 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h581 : Operation.add {nsw := true, nuw := true} (natWord n580) (natWord n571) = natWord n581 := add_nat n580 n571 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h582 : Operation.lshr false (natWord n579) (natWord 26) = natWord n582 := shr_nat n579 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h583 : Operation.add {nsw := true, nuw := true} (natWord n582) (natWord n559) = natWord n583 := add_nat n582 n559 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h584 : Operation.lshr false (natWord n583) (natWord 25) = natWord n584 := shr_nat n583 25 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h585 : Operation.mul {nsw := true, nuw := true} (natWord n584) (natWord 19) = natWord n585 := mul_nat n584 19 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h586 : Operation.add {nsw := true, nuw := true} (natWord n585) (natWord n562) = natWord n586 := add_nat n585 n562 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  have h587 : Operation.lshr false (natWord n586) (natWord 26) = natWord n587 := shr_nat n586 26 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by decide)
  have h588 : Operation.add {nsw := true, nuw := true} (natWord n587) (natWord n568) = natWord n588 := add_nat n587 n568 (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega) (by dsimp [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588]; norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ⊢; omega)
  dsimp only [n550, n551, n552, n553, n554, n555, n556, n557, n558, n559, n560, n561, n562, n563, n564, n565, n566, n567, n568, n569, n570, n571, n572, n573, n574, n575, n576, n577, n578, n579, n580, n581, n582, n583, n584, n585, n586, n587, n588] at h560 h561 h562 h563 h564 h565 h566 h567 h568 h569 h570 h571 h572 h573 h574 h575 h576 h577 h578 h579 h580 h581 h582 h583 h584 h585 h586 h587 h588
  unfold scalarInstructions
  simp only [h560, h561, h562, h563, h564, h565, h566, h567, h568, h569, h570, h571, h572, h573, h574, h575, h576, h577, h578, h579, h580, h581, h582, h583, h584, h585, h586, h587, h588]
  funext i
  fin_cases i <;> rfl

/-- Bounds specific to the smaller constructor columns justify its single fold. -/
theorem carry_small (z : Reduce64.Columns) (hz : ∀ i, z i < 2^50) :
    Reduce64.carry z < 2^26 := by
  have h5 := hz 5; have h6 := hz 6; have h7 := hz 7
  have h8 := hz 8; have h9 := hz 9; have h4 := hz 4
  simp only [Reduce64.carry, Reduce64.t9, Reduce64.t8, Reduce64.t7,
    Reduce64.t6, Reduce64.t5]
  norm_num at *
  omega

def finalMask (z : Reduce64.Columns) : Reduce64.Columns := fun i =>
  if i = 1 ∨ i = 5 then z i else z i % 2^(if i.val % 2 = 0 then 26 else 25)

theorem scalarNat_reduce (z : Reduce64.Columns) (hz : ∀ i, z i < 2^50) :
    finalMask (scalarNat z) = Reduce64.reduce z := by
  have hc := carry_small z hz
  have hcmod : Reduce64.carry z % 2^26 = Reduce64.carry z := Nat.mod_eq_of_lt hc
  have hcdiv : Reduce64.carry z / 2^26 = 0 := Nat.div_eq_of_lt hc
  funext i
  fin_cases i <;>
    simp only [finalMask, Reduce64.reduce, Reduce64.u1, Reduce64.u0, hcmod, hcdiv]
  all_goals simp only [scalarNat, Reduce64.t1, Reduce64.t2, Reduce64.t3, Reduce64.t4, Reduce64.t5,
      Reduce64.t6, Reduce64.t7, Reduce64.t8, Reduce64.t9, Reduce64.u5, Reduce64.carry,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals norm_num
  all_goals ac_rfl

end Agave.Ed25519.Tables.Avx2Constructor.CacheScale
