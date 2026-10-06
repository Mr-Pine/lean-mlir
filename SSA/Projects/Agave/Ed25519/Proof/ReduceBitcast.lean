module

public import SSA.Projects.RIR.Semantics.Operations.Scalar

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

namespace Agave.Ed25519
open LeanMLIR.RIR
@[expose] public section

 theorem bitcast_wrap_vec (x : Vector (BitVec w) n)
    (h : (Ty.vec n w).width = (Ty.vec m v).width) :
    Operation.bitcast h (Ty.wrap x) =
      Ty.wrap (Vector.ofFn fun i : Fin m =>
        (BitVec.packLanes x).extractLsb' (i.val * v) v) := by
  ext i hi
  simp [Operation.bitcast, Ty.wrap_vec, Vector.map_map, Function.comp_def]


abbrev V32 := Vector (BitVec 32) 8
abbrev V64 := Vector (BitVec 64) 4

def split32 (x : V64) : V32 :=
  #v[x[0].extractLsb' 0 32, x[0].extractLsb' 32 32,
     x[1].extractLsb' 0 32, x[1].extractLsb' 32 32,
     x[2].extractLsb' 0 32, x[2].extractLsb' 32 32,
     x[3].extractLsb' 0 32, x[3].extractLsb' 32 32]

def join64 (x : V32) : V64 :=
  #v[x[1] ++ x[0], x[3] ++ x[2], x[5] ++ x[4], x[7] ++ x[6]]

theorem extract_pack_part (x : Vector (BitVec w) n) (i k len : Nat)
    (hi : i < n) (hk : k + len ≤ w) :
    (BitVec.packLanes x).extractLsb' (i * w + k) len =
      x[i].extractLsb' k len := by
  rw [← BitVec.extractLsb'_packLanes x i hi]
  apply BitVec.eq_of_getElem_eq
  intro j hj
  simp [show k + j < w by omega, Nat.add_assoc]

theorem bitcast_split32 (x : V64) :
    Operation.bitcast (t := .vec 4 64) (t' := .vec 8 32) (by decide) (Ty.wrap x) =
      Ty.wrap (split32 x) := by
  erw [bitcast_wrap_vec]
  congr 1
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|_|_|_|_|i := i
  all_goals try omega
  all_goals simp only [Vector.getElem_ofFn, split32, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first
    | exact extract_pack_part x 0 0 32 (by decide) (by decide)
    | exact extract_pack_part x 0 32 32 (by decide) (by decide)
    | exact extract_pack_part x 1 0 32 (by decide) (by decide)
    | exact extract_pack_part x 1 32 32 (by decide) (by decide)
    | exact extract_pack_part x 2 0 32 (by decide) (by decide)
    | exact extract_pack_part x 2 32 32 (by decide) (by decide)
    | exact extract_pack_part x 3 0 32 (by decide) (by decide)
    | exact extract_pack_part x 3 32 32 (by decide) (by decide)

theorem extract_pack_pair (x : Vector (BitVec 32) n) (i : Nat)
    (hi : 2*i+1 < n) :
    (BitVec.packLanes x).extractLsb' (i*64) 64 = x[2*i+1] ++ x[2*i] := by
  rw [← BitVec.extractLsb'_packLanes x (2*i+1) hi,
    ← BitVec.extractLsb'_packLanes x (2*i) (by omega)]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  congr 1
  omega

theorem bitcast_join64 (x : V32) :
    Operation.bitcast (t := .vec 8 32) (t' := .vec 4 64) (by decide) (Ty.wrap x) =
      Ty.wrap (join64 x) := by
  erw [bitcast_wrap_vec]
  congr 1
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|i := i
  all_goals try omega
  all_goals simp only [Vector.getElem_ofFn, join64, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first
    | exact extract_pack_pair x 0 (by decide)
    | exact extract_pack_pair x 1 (by decide)
    | exact extract_pack_pair x 2 (by decide)
    | exact extract_pack_pair x 3 (by decide)

theorem split32_join64 (x : V32) : split32 (join64 x) = x := by
  apply Vector.ext
  intro i hi
  obtain _|_|_|_|_|_|_|_|i := i
  · change (x[1] ++ x[0]).extractLsb' 0 32 = x[0]
    exact BitVec.extractLsb'_append_eq_right (a := x[1]) (b := x[0])
  · change (x[1] ++ x[0]).extractLsb' 32 32 = x[1]
    exact BitVec.extractLsb'_append_eq_left (a := x[1]) (b := x[0])
  · change (x[3] ++ x[2]).extractLsb' 0 32 = x[2]
    exact BitVec.extractLsb'_append_eq_right (a := x[3]) (b := x[2])
  · change (x[3] ++ x[2]).extractLsb' 32 32 = x[3]
    exact BitVec.extractLsb'_append_eq_left (a := x[3]) (b := x[2])
  · change (x[5] ++ x[4]).extractLsb' 0 32 = x[4]
    exact BitVec.extractLsb'_append_eq_right (a := x[5]) (b := x[4])
  · change (x[5] ++ x[4]).extractLsb' 32 32 = x[5]
    exact BitVec.extractLsb'_append_eq_left (a := x[5]) (b := x[4])
  · change (x[7] ++ x[6]).extractLsb' 0 32 = x[6]
    exact BitVec.extractLsb'_append_eq_right (a := x[7]) (b := x[6])
  · change (x[7] ++ x[6]).extractLsb' 32 32 = x[7]
    exact BitVec.extractLsb'_append_eq_left (a := x[7]) (b := x[6])
  · omega


end
end Agave.Ed25519
