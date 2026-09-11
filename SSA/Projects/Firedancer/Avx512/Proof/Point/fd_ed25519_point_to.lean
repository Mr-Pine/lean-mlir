/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_to
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/- Scaffolding for the `fd_ed25519_point_to` derivation. Only
`fd_ed25519_point_to_conforms`, below, escapes. -/
namespace PointTo

/-- `%20`: zeros in the even lanes, poison in the odd. Only the even lanes are
ever selected out of it. -/
def blendEven : Vector (LLVM.IntW 64) 8 :=
  #v[.value 0, .poison, .value 0, .poison, .value 0, .poison, .value 0, .poison]

/-- `%29`: the same vector at the other parity. -/
def blendOdd : Vector (LLVM.IntW 64) 8 :=
  #v[.poison, .value 0, .poison, .value 0, .poison, .value 0, .poison, .value 0]

/-! ### The four gathers

`e`/`o` are `%35`/`%36`, the even- and odd-lane halves of `v03` interleaved
with `v14`; `ce`/`co` are `%37`/`%38`, the same halves of `v25` interleaved
with the zero blends. `%1` gathers limbs `0, 1, 2` (coordinates `X`, `Y`),
`%0` limbs `3, 4, 5` (coordinates `Z`, `T`). -/

set_option maxHeartbeats 1000000 in
/-- **`%39`, the `X` out-parameter**: lanes `0-5` are `a[0] b[0] c[0] a[4] b[4]
c[4]`, which is `quadElemVec`'s lane `0`; lanes `6, 7` are the blend's
zeros. -/
theorem denote_pointTo_X {a b c : Vector (BitVec 64) 8}
    {e ce gX : Vector (LLVM.IntW 64) 8}
    (he : e = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, 4, 12, 6, 14] (a.map PoisonOr.value) (b.map PoisonOr.value))
    (hce : ce = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, 4, 12, 6, 14] (c.map PoisonOr.value) blendEven)
    (hgX : gX = LLVM.Ty.vpermi2var e (toBitVecValue 64 #v[0, 1, 8, 4, 5, 12, 9, 9]) ce) :
    gX = (widenVec (quadElemVec a b c 0)).map PoisonOr.value := by
  subst he hce hgX
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, widenVec, quadElemVec, blendEven,
      Vector.getElem_map]

set_option maxHeartbeats 1000000 in
/-- **`%40`, the `Y` out-parameter**: the same gather on the odd halves. -/
theorem denote_pointTo_Y {a b c : Vector (BitVec 64) 8}
    {o co gY : Vector (LLVM.IntW 64) 8}
    (ho : o = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, 5, 13, 7, 15] (a.map PoisonOr.value) (b.map PoisonOr.value))
    (hco : co = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, 5, 13, 7, 15] (c.map PoisonOr.value) blendOdd)
    (hgY : gY = LLVM.Ty.vpermi2var o (toBitVecValue 64 #v[0, 1, 8, 4, 5, 12, 9, 9]) co) :
    gY = (widenVec (quadElemVec a b c 1)).map PoisonOr.value := by
  subst ho hco hgY
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, widenVec, quadElemVec, blendOdd,
      Vector.getElem_map]

set_option maxHeartbeats 1000000 in
/-- **`%41`, the `Z` out-parameter**: the even halves again, gathered through
the second mask. -/
theorem denote_pointTo_Z {a b c : Vector (BitVec 64) 8}
    {e ce gZ : Vector (LLVM.IntW 64) 8}
    (he : e = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, 4, 12, 6, 14] (a.map PoisonOr.value) (b.map PoisonOr.value))
    (hce : ce = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, 4, 12, 6, 14] (c.map PoisonOr.value) blendEven)
    (hgZ : gZ = LLVM.Ty.vpermi2var e (toBitVecValue 64 #v[2, 3, 10, 6, 7, 14, 9, 9]) ce) :
    gZ = (widenVec (quadElemVec a b c 2)).map PoisonOr.value := by
  subst he hce hgZ
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, widenVec, quadElemVec, blendEven,
      Vector.getElem_map]

set_option maxHeartbeats 1000000 in
/-- **`%42`, the `T` out-parameter**. -/
theorem denote_pointTo_T {a b c : Vector (BitVec 64) 8}
    {o co gT : Vector (LLVM.IntW 64) 8}
    (ho : o = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, 5, 13, 7, 15] (a.map PoisonOr.value) (b.map PoisonOr.value))
    (hco : co = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, 5, 13, 7, 15] (c.map PoisonOr.value) blendOdd)
    (hgT : gT = LLVM.Ty.vpermi2var o (toBitVecValue 64 #v[2, 3, 10, 6, 7, 14, 9, 9]) co) :
    gT = (widenVec (quadElemVec a b c 3)).map PoisonOr.value := by
  subst ho hco hgT
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, widenVec, quadElemVec, blendOdd,
      Vector.getElem_map]

/-! ### Reading the four stores back

The out-parameters are pairwise distinct blocks (`hNodup`), so each readback
walks the splices above its own with `readVec?_splice_ne` and lands on
`readVec?_splice_self`. -/

/-- The `x` store, read back through the three that follow it. -/
theorem readVec?_out₁ {m : MemoryState} {x y z t : Pointer}
    {vx vy vz vt : Vector (BitVec 64) 8} (hx : IsVecPtr m x)
    (hyx : y.id ≠ x.id) (hzx : z.id ≠ x.id) (htx : t.id ≠ x.id) :
    readVec? x ((((m.splice x (vecBV vx)).splice y (vecBV vy)).splice
      z (vecBV vz)).splice t (vecBV vt)) = some vx := by
  rw [readVec?_splice_ne htx, readVec?_splice_ne hzx, readVec?_splice_ne hyx,
    readVec?_splice_self vx hx]

/-- ... the `y` store, through the two that follow it. -/
theorem readVec?_out₂ {m : MemoryState} {x y z t : Pointer}
    {vx vy vz vt : Vector (BitVec 64) 8} (hy : IsVecPtr m y)
    (hzy : z.id ≠ y.id) (hty : t.id ≠ y.id) :
    readVec? y ((((m.splice x (vecBV vx)).splice y (vecBV vy)).splice
      z (vecBV vz)).splice t (vecBV vt)) = some vy := by
  rw [readVec?_splice_ne hty, readVec?_splice_ne hzy,
    readVec?_splice_self vy (isVecPtr_splice hy)]

/-- ... the `z` store, through the one that follows it. -/
theorem readVec?_out₃ {m : MemoryState} {x y z t : Pointer}
    {vx vy vz vt : Vector (BitVec 64) 8} (hz : IsVecPtr m z)
    (htz : t.id ≠ z.id) :
    readVec? z ((((m.splice x (vecBV vx)).splice y (vecBV vy)).splice
      z (vecBV vz)).splice t (vecBV vt)) = some vz := by
  rw [readVec?_splice_ne htz,
    readVec?_splice_self vz (isVecPtr_splice (isVecPtr_splice hz))]

/-- ... and the `t` store, which is the last one. -/
theorem readVec?_out₄ {m : MemoryState} {x y z t : Pointer}
    {vx vy vz vt : Vector (BitVec 64) 8} (ht : IsVecPtr m t) :
    readVec? t ((((m.splice x (vecBV vx)).splice y (vecBV vy)).splice
      z (vecBV vz)).splice t (vecBV vt)) = some vt :=
  readVec?_splice_self vt (isVecPtr_splice (isVecPtr_splice (isVecPtr_splice ht)))

/-- The region allocates nothing, so the frame kill at `return` is invisible:
every block at or above the entry counter is dead, four splices or none. -/
theorem popFrame_equiv {s : GlobalState} (hs : s.WF) {x y z t : Pointer}
    {vx vy vz vt : Vector (BitVec 64) 8} :
    ({ s with mem := (((s.mem.splice x (vecBV vx)).splice y (vecBV vy)).splice
        z (vecBV vz)).splice t (vecBV vt) } : GlobalState)
      ≈ s.popFrame ((((s.mem.splice x (vecBV vx)).splice y (vecBV vy)).splice
        z (vecBV vz)).splice t (vecBV vt)) :=
  GlobalState.Equiv.symm (killFrom_equiv_of_none fun q hq =>
    live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none
      (live?_splice_eq_none (hs q hq)))))

end PointTo

open PointTo in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
theorem fd_ed25519_point_to_conforms (x y z t a : Pointer) (s : GlobalState)
    (hs : s.WF) (hNodup : ([x, y, z, t].map Pointer.id).Nodup)
    (ha : IsQuadPtr s.mem a)
    (hx : IsVecPtr s.mem x) (hy : IsVecPtr s.mem y)
    (hz : IsVecPtr s.mem z) (ht : IsVecPtr s.mem t) :
    fd_ed25519_point_to_spec x y z t a s hNodup ha hx hy hz ht := by
  simp only [fd_ed25519_point_to_spec, Cfg.denote]

  -- The four out-parameters are pairwise distinct blocks: what carries each
  -- readback down through the stores that follow it.
  obtain ⟨hxy, hxz, hxt, hyz, hyt, hzt⟩ :
      y.id ≠ x.id ∧ z.id ≠ x.id ∧ t.id ≠ x.id ∧ z.id ≠ y.id ∧ t.id ≠ y.id ∧ t.id ≠ z.id := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil, not_or] at hNodup
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all

  refine ⟨⟨_, run_runFunction (s' := { s with mem := _ }) ?_, popFrame_equiv hs⟩,
    readVec_eq_of (readVec?_out₁ hx hxy hxz hxt),
    readVec_eq_of (readVec?_out₂ hy hyz hyt),
    readVec_eq_of (readVec?_out₃ hz hzt),
    readVec_eq_of (readVec?_out₄ ht), ?_, ?_, ?_, ?_⟩
  case refine_2 =>
    rw [readVec_eq_of (readVec?_out₁ hx hxy hxz hxt), vecValue_widenVec]; rfl
  case refine_3 =>
    rw [readVec_eq_of (readVec?_out₂ hy hyz hyt), vecValue_widenVec]; rfl
  case refine_4 =>
    rw [readVec_eq_of (readVec?_out₃ hz hzt), vecValue_widenVec]; rfl
  case refine_5 =>
    rw [readVec_eq_of (readVec?_out₄ ht), vecValue_widenVec]; rfl

  -- `%0 … %29`: the two gather masks, and the two zero blends the odd/even
  -- halves of `v25` are shuffled against.
  denote_step_all v 29
  denote_eval v 0 29

  have hb20 : v20 = blendEven := by
    simp only [hv20, hv19, hv18, hv17, hv16, hv15, hv14, hv13, hv12, hv11, hv10, hv9,
      hv8, hv7, hv6, hv5, hv4, hv3, hv2]
    rfl
  have hb29 : v29 = blendOdd := by
    simp only [hv29, hv28, hv27, hv26, hv25, hv24, hv23, hv22, hv21, hv11, hv10, hv9,
      hv8, hv7, hv6, hv5, hv4, hv3, hv2]
    rfl
  have hm1 : v1 = toBitVecValue 64 #v[0, 1, 8, 4, 5, 12, 9, 9] := by denote_dense hv1
  have hm0 : v0 = toBitVecValue 64 #v[2, 3, 10, 6, 7, 14, 9, 9] := by denote_dense hv0
  clear hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15
  clear hv16 hv17 hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29

  -- `%30 … %34`: the QUAD's three vectors, at 0, 64 and 128 bytes in.
  obtain ⟨ablk, hablkE, halen⟩ := ha.1
  have halive : s.mem.live? a.id = some ablk := by simp [MemoryState.live?, hablkE]
  have h64 : (64 : BitVec 64).toNat = 64 := rfl
  have h128 : (128 : BitVec 64).toNat = 128 := rfl

  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, a, hablkE, s
  rw [unflatten_readQuad_v03 ha halive]

  peel_gep 64 with a, ha.1, s as aField
  have hoffA : aField.offsetInBits = a.offsetInBits + 512 := by
    have hb := ha.2
    simp only [aField, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h64] at hb ⊢
    omega
  have haFieldE : s.mem[aField.id]? = some (.live ablk) := hablkE
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField, haFieldE, s
  rw [hoffA, unflatten_readQuad_v14 ha halive]

  peel_gep 128 with a, ha.1, s as aField25
  have hoffA25 : aField25.offsetInBits = a.offsetInBits + 1024 := by
    have hb := ha.2
    simp only [aField25, Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, h128] at hb ⊢
    omega
  have haField25E : s.mem[aField25.id]? = some (.live ablk) := hablkE
  peel_load (.vector 8 (.bitvec (.concrete 64))), ablk, aField25, haField25E, s
  rw [hoffA25, unflatten_readQuad_v25 ha halive]

  -- `%35 … %39`: the four parity splits, and the first gather.
  denote_step_all v 39
  denote_eval v 35 39
  rw [hb20] at hv37
  rw [hb29] at hv38

  -- `%39` gathers `X`; the store lands it in `%arg0`.
  rw [hm1] at hv39
  have hX : v39 = (widenVec (readQuad ha).PointVecs.X).map PoisonOr.value :=
    denote_pointTo_X hv35 hv37 hv39
  subst hX
  refine name_of ({ s with mem := s.mem.splice x (vecBV (widenVec (readQuad ha).PointVecs.X)) })
    fun s₁ hs₁ => ?_
  peel_store (widenVec (readQuad ha).PointVecs.X), x, hx.1, s as s₁ := hs₁
  have fy : Fits s₁.mem y (8 * 64) := by rw [hs₁]; exact fits_splice hy.1

  -- `%40` gathers `Y`, off the odd halves.
  denote_step_all v 40
  denote_eval v 40 40
  rw [hm1] at hv40
  have hY : v40 = (widenVec (readQuad ha).PointVecs.Y).map PoisonOr.value :=
    denote_pointTo_Y hv36 hv38 hv40
  subst hY
  refine name_of ({ s₁ with mem := s₁.mem.splice y (vecBV (widenVec (readQuad ha).PointVecs.Y)) })
    fun s₂ hs₂ => ?_
  peel_store (widenVec (readQuad ha).PointVecs.Y), y, fy, s₁ as s₂ := hs₂
  have fz : Fits s₂.mem z (8 * 64) := by
    rw [hs₂, hs₁]; exact fits_splice (fits_splice hz.1)

  -- `%41` gathers `Z`: the even halves again, through the second mask.
  denote_step_all v 41
  denote_eval v 41 41
  rw [hm0] at hv41
  have hZ : v41 = (widenVec (readQuad ha).PointVecs.Z).map PoisonOr.value :=
    denote_pointTo_Z hv35 hv37 hv41
  subst hZ
  refine name_of ({ s₂ with mem := s₂.mem.splice z (vecBV (widenVec (readQuad ha).PointVecs.Z)) })
    fun s₃ hs₃ => ?_
  peel_store (widenVec (readQuad ha).PointVecs.Z), z, fz, s₂ as s₃ := hs₃
  have ft : Fits s₃.mem t (8 * 64) := by
    rw [hs₃, hs₂, hs₁]; exact fits_splice (fits_splice (fits_splice ht.1))

  -- `%42` gathers `T`, the last of the four.
  denote_step_all v 42
  denote_eval v 42 42
  rw [hm0] at hv42
  have hT : v42 = (widenVec (readQuad ha).PointVecs.T).map PoisonOr.value :=
    denote_pointTo_T hv36 hv38 hv42
  subst hT
  peel_store (widenVec (readQuad ha).PointVecs.T), t, ft, s₃

  simp_return
  -- The four states, unfolded: the `splice` on the right is the same `match`.
  rw [hs₃, hs₂, hs₁]
  exact ⟨rfl, rfl, rfl⟩

end Firedancer.Avx512
