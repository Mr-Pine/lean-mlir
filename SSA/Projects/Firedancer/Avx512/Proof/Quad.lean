/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Avx512.Spec.Vec
import SSA.Projects.Firedancer.Proof.Overflow
import SSA.Projects.Firedancer.Avx512.Proof.Fold

/-!
# Shared scaffolding for the `fd_r43x6_quad_*` proofs

The quad kernels take three or six `vector<8xi64>` block arguments, ahead of
three `!llvm.ptr` out-parameters, and write their three results through those
pointers. This file fixes the QUAD layout and the readback of a result vector;
the valuations that feed the kernels live in `Proof/Mem.lean`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The dialect type of an 8-lane 64-bit vector. -/
abbrev QTy : SLLVM.Ty := SLLVM.Ty.arith (.vector 8 (.bitvec (.concrete 64)))

/-- `wwl_shl` applied to a *block argument*: the operand is a bare lane rather
than a `BitVec.ofNat`, so the `ofNat_shl*` family of `Proof/Common.lean` does
not match it. The shift amount comes in as a `BitVec`, hence `k.toNat`, which
`Nat.reduceMod` and `Nat.reducePow` finish off.

Deliberately *not* in `quad_vecbin`'s fixed simp set: it also matches
`BitVec.ofNat 64 x <<< k`, where it shadows the sharper `ofNat_shl` and routes
the operand through `.toNat`, leaving a vacuous `% 2^64` that only a bound on
`x` could discharge. The two instructions that shift a block argument name it
through `with` instead. -/
theorem shl_lane (v k : BitVec 64) :
    v <<< k = BitVec.ofNat 64 (2 ^ k.toNat * v.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

/-! ## A faster `vpmadd52` lane derivation

`denote_vpmadd52` of `Proof/Common.lean` finishes with a full `simp` -- the
whole default simp set -- once per lane, so eight times per instruction. On
these programs that one call is 3.18s of the 3.27s an instruction costs.

Replacing it with `simp only` over an explicit set brings an instruction to
0.83s. Two lemmas have to change for that to work:

* `Nat.mul_mod` is dropped. It loops under `simp only` (its right-hand side
  matches its own left-hand side), and it is not needed: the lane is
  `(u % 2^52) * (v % 2^52)`, and the `u47` operand bounds passed in through
  `with` rewrite each factor to itself, leaving `u * v` directly.
* `Nat.reducePow` has to be named, since `simp only` does not run the default
  simprocs and the operand bounds are stated over the literal `2^52`.

`Nat.mod_mod_of_dvd _ dvd52_64` stays, for the `% 2^64` a `BitVec.ofNat`
operand carries in under the `% 2^52`. -/

/-- As `denote_vpmadd52`, but with an explicit simp set. See above. -/
macro "quad_vpmadd52 " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_denote_only
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta only
               [LLVM.Ty.vpmadd52, LLVM.Ty.vpmadd52Lane, toBitVecValue,
                Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                Array.getElem_replicate, Vector.getElem_replicate,
                quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat, pl, phRaw,
                ← BitVec.ofNat_add, BitVec.toNat_ofNat,
                Nat.mod_mod_of_dvd _ dvd52_64, toNat_mod_two_pow_64,
                Nat.reducePow, Nat.reduceMod, reduceIte,
                Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                false_and, and_false, true_and, and_true, $hs,*]))

/-- As `denote_vecbin`, but taking extra simp lemmas through `with`.

The shared tactic has no `with` clause, so an instruction whose operand is a
block argument -- `two_x03 = wwl_shl( x03, 1 )` and friends -- cannot read that
argument out of the valuation. Tries `vec8_lemma`, then lanes as `denote_vecbin`. -/
macro "quad_vecbin " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_denote_only
             simp only [HVector.head]
             first
               | vec8_lemma
               | (apply Vector.ext
                  intro i hi
                  interval_cases i
                  all_goals first
                    | (simp +zetaDelta +decide only
                       [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                        LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, LLVM.Ty.poison,
                        toBitVecValue, and_allOnes_64, and_neg_one_64,
                        ofNat_shl1', ofNat_shl9', ofNat_shl7', ofNat_mul24,
                        ofNat_shl, ofNat_shl7, BitVec.toNat_ofNat,
                        ← BitVec.ofNat_add, ← BitVec.ofNat_mul,
                        Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                        Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                        Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                        Array.getElem_replicate, Vector.getElem_replicate,
                        PoisonOr.value_bind, PoisonOr.poison_bind, PoisonOr.map_value,
                        PoisonOr.map_poison, PoisonOr.bind₂_value, PoisonOr.pure_def,
                        PoisonOr.mk_some, PoisonOr.mk_none, toNat_mod_two_pow_64,
                        Nat.reducePow, Nat.reduceMod, reduceIte,
                        Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                        false_and, and_false, true_and, and_true,
                        quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat, $hs,*]
                       try rfl
                       done)
                    | simp +zetaDelta +decide only
                       [InstCombine.binaryDenote, LLVM.shl, LLVM.shl?, LLVM.and, LLVM.and?,
                        LLVM.add, LLVM.add?, LLVM.mul, LLVM.mul?, LLVM.Ty.poison,
                        toBitVecValue, and_allOnes_64,
                        ofNat_shl1', ofNat_shl9', ofNat_shl7', ofNat_mul24,
                        ofNat_shl, ofNat_shl7, BitVec.toNat_ofNat,
                        ← BitVec.ofNat_add, ← BitVec.ofNat_mul, ph, phRaw, add_assoc,
                        Ctxt.Valuation.cons_zero, Ctxt.Valuation.cons_eval,
                        Ctxt.Valuation.cons_last, Ctxt.Valuation.cons_toCons,
                        Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
                        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
                        Array.getElem_replicate, Vector.getElem_replicate,
                        PoisonOr.value_bind, PoisonOr.poison_bind, PoisonOr.map_value,
                        PoisonOr.map_poison, PoisonOr.bind₂_value, PoisonOr.pure_def,
                        PoisonOr.mk_some, PoisonOr.mk_none,
                        quadLimb, vlane, Fin.reduceCastAdd, Fin.reduceAddNat, toNat_mod_two_pow_64,
                        Nat.reducePow, Nat.reduceMod, reduceIte,
                        Bool.false_eq_true, ite_false, ite_true, Nat.zero_add,
                        false_and, and_false, true_and, and_true, $hs,*])))

/-- `quad_vecbin` followed by `ring_nf`, for the `wwl_shl( ..., 9 )` steps only.

A `madd52hi` chain is summed *before* it is scaled, so such a lane arrives as
`(r₁ + r₂) * 512` where the specification has `ph .. + ph ..`. `ring_nf` closes
that gap, but it is expensive on the wide lanes further down the program -- the
`za + 152*zb` fold blows a 4M heartbeat budget with it -- so it is applied only
where the distribution is actually needed. -/
macro "quad_vecbin_ring " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| ((quad_vecbin $h with $hs,*); all_goals try ring_nf))


/-! ## Memory layout of a QUAD

What a whole-vector load or store sees of `Quad.BV`: the bit-level lemmas the
`fd_ed25519_point_*` derivations run on. None of them appear in a spec. -/

/-- A whole-vector load at `p` reads back the QUAD's `v03`. -/
theorem unflatten_readQuad_v03 {m : MemoryState} {p : Pointer} (h : IsQuadPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' p.offsetInBits 512)
      = (readQuad h).v03.map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [readQuad, readQuad?, hblk, LLVM.Ty.unflatten]
  show (blk.bytes.extractLsb' p.offsetInBits 512).extractLsb' (i * 64) 64
      = blk.bytes.extractLsb' (p.offsetInBits + 64 * i) 64
  rw [BitVec.extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega), Nat.mul_comm i 64]

/-- 512 bits up from `p`: `v14`. -/
theorem unflatten_readQuad_v14 {m : MemoryState} {p : Pointer} (h : IsQuadPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' (p.offsetInBits + 512) 512)
      = (readQuad h).v14.map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [readQuad, readQuad?, hblk, LLVM.Ty.unflatten]
  show (blk.bytes.extractLsb' (p.offsetInBits + 512) 512).extractLsb' (i * 64) 64
      = blk.bytes.extractLsb' (p.offsetInBits + 512 + 64 * i) 64
  rw [BitVec.extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega), Nat.mul_comm i 64]

/-- 1024 bits up from `p`: `v25`. -/
theorem unflatten_readQuad_v25 {m : MemoryState} {p : Pointer} (h : IsQuadPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' (p.offsetInBits + 1024) 512)
      = (readQuad h).v25.map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [readQuad, readQuad?, hblk, LLVM.Ty.unflatten]
  show (blk.bytes.extractLsb' (p.offsetInBits + 1024) 512).extractLsb' (i * 64) 64
      = blk.bytes.extractLsb' (p.offsetInBits + 1024 + 64 * i) 64
  rw [BitVec.extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega), Nat.mul_comm i 64]

/-- A whole-vector load reads back what a whole-vector store wrote. -/
theorem unflatten_vecBV (v : Vector (BitVec 64) 8) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64))) (vecBV v) = v.map PoisonOr.value :=
  LLVM.Ty.unflatten_flattenBV _ _ (by
    intro i
    show LLVM.Ty.ofBitvec ((v.map PoisonOr.value)[i.val]) ≠ .poison
    rw [Vector.getElem_map]
    exact PoisonOr.value_ne_poison _)

/-- Lane `j` of a flattened `fd_r43x6_t` is at bits `[64j, 64j + 64)`. -/
theorem extractLsb'_vecBV (v : Vector (BitVec 64) 8) (j : Nat) (h : j < 8) :
    (vecBV v).extractLsb' (j * 64) 64 = v[j] := by
  have := LLVM.Ty.extractLsb'_flattenBV_vector (l := 8) (e := .bitvec (.concrete 64))
    (v.map PoisonOr.value) j h
  simpa [vecBV] using this

/-! The three vectors sit at the offsets `readQuad?` reads them back at:
`i * (64 * 8)` bits from the pointer, `v03` first. Together with
`extractLsb'_vecBV` these pin the layout down completely -- a transposition of
either the vectors or the lanes would still round-trip through a matching
reader, so the order is not implied by anything else here. -/

theorem extractLsb'_BV_v03 (q : Quad) : q.BV.extractLsb' (0 * (64 * 8)) 512 = vecBV q.v03 :=
  BitVec.extractLsb'_packLanes _ 0 (by omega)

theorem extractLsb'_BV_v14 (q : Quad) : q.BV.extractLsb' (1 * (64 * 8)) 512 = vecBV q.v14 :=
  BitVec.extractLsb'_packLanes _ 1 (by omega)

theorem extractLsb'_BV_v25 (q : Quad) : q.BV.extractLsb' (2 * (64 * 8)) 512 = vecBV q.v25 :=
  BitVec.extractLsb'_packLanes _ 2 (by omega)

/-! A QUAD written whole at offset `0` of a block reads back a vector at a time,
which is what the three loads after a `fd_ed25519_point_set_zero` see. -/

theorem unflatten_spliced_v03 {n : Nat} (bytes : BitVec n) (q : Quad) (h : 3 * 8 * 64 ≤ n) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        ((spliceBits bytes 0 q.BV).extractLsb' 0 512) = q.v03.map PoisonOr.value := by
  rw [extractLsb'_spliceBits_of_subrange _ 0 0 _ (by omega) (by omega) (by omega),
    show (0 : Nat) - 0 = 0 * (64 * 8) from rfl, extractLsb'_BV_v03, unflatten_vecBV]

theorem unflatten_spliced_v14 {n : Nat} (bytes : BitVec n) (q : Quad) (h : 3 * 8 * 64 ≤ n) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        ((spliceBits bytes 0 q.BV).extractLsb' 512 512) = q.v14.map PoisonOr.value := by
  rw [extractLsb'_spliceBits_of_subrange _ 0 512 _ (by omega) (by omega) (by omega),
    show (512 : Nat) - 0 = 1 * (64 * 8) from rfl, extractLsb'_BV_v14, unflatten_vecBV]

theorem unflatten_spliced_v25 {n : Nat} (bytes : BitVec n) (q : Quad) (h : 3 * 8 * 64 ≤ n) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        ((spliceBits bytes 0 q.BV).extractLsb' 1024 512) = q.v25.map PoisonOr.value := by
  rw [extractLsb'_spliceBits_of_subrange _ 0 1024 _ (by omega) (by omega) (by omega),
    show (1024 : Nat) - 0 = 2 * (64 * 8) from rfl, extractLsb'_BV_v25, unflatten_vecBV]

/-- `Quad.BV` in `packLanes`' own width shape: the three flattened vectors
appended, `v03` lowest. Definitional -- `packLanes` unfolds structurally, which
is the only form in which the `BitVec` append lemmas can see it (its `we * n`
widths block unification otherwise). -/
theorem Quad.BV_append (q : Quad) :
    q.BV = 0#(512 * 0) ++ vecBV q.v25 ++ vecBV q.v14 ++ vecBV q.v03 := rfl

/-- Lane extensionality: two `w * n`-bit vectors agreeing on every `w`-wide
lane are equal. `flattenBV`/`packLanes` do not compute -- their `Vector.ofFn`
and `we * n` widths defeat both `rfl` and `simp` -- so concrete facts about
`vecBV` are proved lane by lane through `extractLsb'_vecBV` instead. -/
theorem eq_of_lanes {w n : Nat} (hw : 0 < w) {x y : BitVec (w * n)}
    (h : ∀ j, j < n → x.extractLsb' (j * w) w = y.extractLsb' (j * w) w) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hjn : i / w < n := by
    refine (Nat.div_lt_iff_lt_mul hw).mpr ?_
    rw [Nat.mul_comm]; exact hi
  have := congrArg (fun z : BitVec w => z.getLsbD (i % w)) (h (i / w) hjn)
  simpa [BitVec.getLsbD_extractLsb', Nat.mod_lt _ hw, Nat.div_add_mod' i w] using this

/-- A zeroed `fd_r43x6_t` flattens to zero bits. -/
theorem vecBV_zero : vecBV #v[0, 0, 0, 0, 0, 0, 0, 0] = 0#512 := by
  refine eq_of_lanes (w := 64) (n := 8) (by omega) (fun j hj => ?_)
  rw [extractLsb'_vecBV _ j hj]
  interval_cases j <;> simp

set_option maxRecDepth 20000 in
/-- The 128 zero bytes a `memset` writes, as the two zeroed vectors the QUAD's
top two fields flatten to. -/
theorem zero_append_eq_replicate :
    (0#(512 * 0) ++ (0#512) ++ (0#512)) = BitVec.replicate 128 (0#8) := by
  simp

/-! ## `FD_R43X6_QUAD_PACK`

Eleven instructions in the caller's block: four `vpermi2var`s gathering the
four coordinates two limbs at a time, then five `shufflevector`s interleaving
them into the transposed layout. `Spec/Quad.lean`'s `encodeQuad` is the same
map on six-limb vectors; `packQuad` is it on the eight-lane `fd_r43x6_t`s the
block actually holds, which is what keeps the call site's statement down to
four `fvar`s. The two agree lane for lane -- `packQuad x y z t` is
`encodeQuad (x.take 6) …` -- and the bridge is due where the point's
coordinates are read back out, not here.
-/

/-- The QUAD `FD_R43X6_QUAD_PACK( q, x, y, z, t )` builds. `encodeQuad` at
eight lanes: limb `k` of coordinate `c` goes to lane `c` (for `k < 3`) or
`c + 4` (for `k ≥ 3`) of the `k % 3`-th third. -/
def packQuad (x y z t : Vector (BitVec 64) 8) : Quad where
  v03 := #v[x[0], y[0], z[0], t[0], x[3], y[3], z[3], t[3]]
  v14 := #v[x[1], y[1], z[1], t[1], x[4], y[4], z[4], t[4]]
  v25 := #v[x[2], y[2], z[2], t[2], x[5], y[5], z[5], t[5]]

set_option maxHeartbeats 1000000 in
/-- **`FD_R43X6_QUAD_PACK`'s `v03`**, as `denote_eval` leaves the instructions
that reach it: the two `%12` gathers, the two `%11` gathers, their even/odd
interleaves, and the splice of the two low halves.

Three lemmas rather than one because the block *stores* each output as soon as
it has it, so `v14` and `v25` are computed after the first store and their
hypotheses are not in scope when `v03` is proved.

Stated here rather than inline: each lane reduction costs on the order of a
million heartbeats against the caller's context, and a walk that has already
peeled a hundred instructions has none to spare. Here the context is four
vectors. -/
theorem denote_quadPack_v03 {x y z t : Vector (BitVec 64) 8}
    {g0 g1 g2 g3 s0 s3 o03 : Vector (LLVM.IntW 64) 8}
    (hg0 : g0 = LLVM.Ty.vpermi2var (x.map PoisonOr.value)
      (toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]) (z.map PoisonOr.value))
    (hg1 : g1 = LLVM.Ty.vpermi2var (y.map PoisonOr.value)
      (toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]) (t.map PoisonOr.value))
    (hg2 : g2 = LLVM.Ty.vpermi2var (x.map PoisonOr.value)
      (toBitVecValue 64 #v[2, 3, 10, 11, 6, 7, 12, 13]) (z.map PoisonOr.value))
    (hg3 : g3 = LLVM.Ty.vpermi2var (y.map PoisonOr.value)
      (toBitVecValue 64 #v[2, 3, 10, 11, 6, 7, 12, 13]) (t.map PoisonOr.value))
    (hs0 : s0 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, 4, 12, 6, 14] g0 g1)
    (hs3 : s3 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, -1, -1, -1, -1] g2 g3)
    (h03 : o03 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 1, 2, 3, 8, 9, 10, 11] s0 s3) :
    o03 = (packQuad x y z t).v03.map PoisonOr.value := by
  subst hg0 hg1 hg2 hg3 hs0 hs3 h03
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, packQuad, Vector.getElem_map]

set_option maxHeartbeats 1000000 in
/-- ... its `v14`: the odd interleave's low half over the even one's high
half. -/
theorem denote_quadPack_v14 {x y z t : Vector (BitVec 64) 8}
    {g0 g1 s0 s1 o14 : Vector (LLVM.IntW 64) 8}
    (hg0 : g0 = LLVM.Ty.vpermi2var (x.map PoisonOr.value)
      (toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]) (z.map PoisonOr.value))
    (hg1 : g1 = LLVM.Ty.vpermi2var (y.map PoisonOr.value)
      (toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]) (t.map PoisonOr.value))
    (hs0 : s0 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, 4, 12, 6, 14] g0 g1)
    (hs1 : s1 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, 5, 13, 7, 15] g0 g1)
    (h14 : o14 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 1, 2, 3, 12, 13, 14, 15] s1 s0) :
    o14 = (packQuad x y z t).v14.map PoisonOr.value := by
  subst hg0 hg1 hs0 hs1 h14
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, packQuad, Vector.getElem_map]

set_option maxHeartbeats 1000000 in
/-- ... and its `v25`. -/
theorem denote_quadPack_v25 {x y z t : Vector (BitVec 64) 8}
    {g0 g1 g2 g3 s1 s2 o25 : Vector (LLVM.IntW 64) 8}
    (hg0 : g0 = LLVM.Ty.vpermi2var (x.map PoisonOr.value)
      (toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]) (z.map PoisonOr.value))
    (hg1 : g1 = LLVM.Ty.vpermi2var (y.map PoisonOr.value)
      (toBitVecValue 64 #v[0, 1, 8, 9, 4, 5, 12, 13]) (t.map PoisonOr.value))
    (hg2 : g2 = LLVM.Ty.vpermi2var (x.map PoisonOr.value)
      (toBitVecValue 64 #v[2, 3, 10, 11, 6, 7, 12, 13]) (z.map PoisonOr.value))
    (hg3 : g3 = LLVM.Ty.vpermi2var (y.map PoisonOr.value)
      (toBitVecValue 64 #v[2, 3, 10, 11, 6, 7, 12, 13]) (t.map PoisonOr.value))
    (hs1 : s1 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [1, 9, 3, 11, 5, 13, 7, 15] g0 g1)
    (hs2 : s2 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 8, 2, 10, -1, -1, -1, -1] g2 g3)
    (h25 : o25 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [0, 1, 2, 3, 12, 13, 14, 15] s2 s1) :
    o25 = (packQuad x y z t).v25.map PoisonOr.value := by
  subst hg0 hg1 hg2 hg3 hs1 hs2 h25
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, LLVM.Ty.vpermi2var, LLVM.Ty.vpermi2varLane,
      LLVM.Ty.poison, toBitVecValue, packQuad, Vector.getElem_map]

/-- **What `FD_R43X6_QUAD_PACK` holds**: the four elements it was given. The
transpose is a permutation of lanes, so this is a lane identity. -/
theorem toPoint_packQuad (X Y Z T : Vector (BitVec 64) 8) :
    (packQuad X Y Z T).toPoint = ⟨vecValue X, vecValue Y, vecValue Z, vecValue T⟩ := rfl

/-! ## `FD_R43X6_QUAD_FOLD_UNSIGNED`

The reduce that follows the pack: each limb keeps its low `43` bits (`40` for
limb 5) and passes the rest up, limb 5's carry wrapping to limb 0 scaled by
`19` -- `Fold.lean`'s `foldVec` on all four elements at once, in the
transposed layout.

Two things this shape forces:

* **The shift amount is a `Nat`.** `LLVM.lshr?` shifts by a `BitVec`, but by
  the time the lane script reaches the operation `simp` has normalised it and
  the goal carries `BitVec.instHShiftRightNat` with `43 : Nat`. A bare `43` in
  `y >>> 43` elaborates to the *homogeneous* `BitVec` instance instead, which
  prints identically and matches nothing.
* **`lshr` is peeled by lemma, not by unfolding.** `lshr?` is
  `if op2 ≥ n then poison else …`, and `simp` will not rewrite inside an
  `ite`'s condition here; unfolding it leaves the guard standing in all eight
  lanes. `lshr_43`/`lshr_40` discharge it once.

The `mul` and the three `add`s carry `nsw nuw` and, unlike `fd_r43x6_neg`'s
bias add, need no hypothesis: a masked lane is below `2 ^ 43` and a `>>> 40`
is below `2 ^ 24` whatever the input, so no sum here can reach `2 ^ 63`.
-/

/-- `%1`, the reduce's mask on the `03` and `14` thirds. -/
def quadMask43 : Vector Nat 8 :=
  #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
     8796093022207, 8796093022207, 8796093022207, 8796093022207]

/-- `%0`, its mask on the `25` third: limb 5 keeps only `40` bits. -/
def quadMask48 : Vector Nat 8 :=
  #v[8796093022207, 8796093022207, 8796093022207, 8796093022207,
     1099511627775, 1099511627775, 1099511627775, 1099511627775]

/-- `%10`/`%9`, the reduce's shifts. -/
def quadShift43 : Vector Nat 8 := #v[43, 43, 43, 43, 43, 43, 43, 43]
def quadShift48 : Vector Nat 8 := #v[43, 43, 43, 43, 40, 40, 40, 40]

/-- `%44`, the `undef`/`insertelement` chain: `19` in the top four lanes and
poison in the bottom four, which `%285` never reads. -/
def quadMul19 : Vector (LLVM.IntW 64) 8 :=
  #v[PoisonOr.poison, PoisonOr.poison, PoisonOr.poison, PoisonOr.poison,
     .value 19#64, .value 19#64, .value 19#64, .value 19#64]

/-- **The QUAD the reduce leaves.** Every lane written out: a `Vector.ofFn`
here would leave a mask lookup on the right-hand side of all eight lane
goals. -/
def foldQuad (q : Quad) : Quad where
  v03 := #v[
    (q.v25[4] >>> (40 : ℕ)) * 19#64 + (q.v03[0] &&& 8796093022207#64),
    (q.v25[5] >>> (40 : ℕ)) * 19#64 + (q.v03[1] &&& 8796093022207#64),
    (q.v25[6] >>> (40 : ℕ)) * 19#64 + (q.v03[2] &&& 8796093022207#64),
    (q.v25[7] >>> (40 : ℕ)) * 19#64 + (q.v03[3] &&& 8796093022207#64),
    (q.v25[0] >>> (43 : ℕ)) + (q.v03[4] &&& 8796093022207#64),
    (q.v25[1] >>> (43 : ℕ)) + (q.v03[5] &&& 8796093022207#64),
    (q.v25[2] >>> (43 : ℕ)) + (q.v03[6] &&& 8796093022207#64),
    (q.v25[3] >>> (43 : ℕ)) + (q.v03[7] &&& 8796093022207#64)]
  v14 := #v[
    (q.v14[0] &&& 8796093022207#64) + (q.v03[0] >>> (43 : ℕ)),
    (q.v14[1] &&& 8796093022207#64) + (q.v03[1] >>> (43 : ℕ)),
    (q.v14[2] &&& 8796093022207#64) + (q.v03[2] >>> (43 : ℕ)),
    (q.v14[3] &&& 8796093022207#64) + (q.v03[3] >>> (43 : ℕ)),
    (q.v14[4] &&& 8796093022207#64) + (q.v03[4] >>> (43 : ℕ)),
    (q.v14[5] &&& 8796093022207#64) + (q.v03[5] >>> (43 : ℕ)),
    (q.v14[6] &&& 8796093022207#64) + (q.v03[6] >>> (43 : ℕ)),
    (q.v14[7] &&& 8796093022207#64) + (q.v03[7] >>> (43 : ℕ))]
  v25 := #v[
    (q.v25[0] &&& 8796093022207#64) + (q.v14[0] >>> (43 : ℕ)),
    (q.v25[1] &&& 8796093022207#64) + (q.v14[1] >>> (43 : ℕ)),
    (q.v25[2] &&& 8796093022207#64) + (q.v14[2] >>> (43 : ℕ)),
    (q.v25[3] &&& 8796093022207#64) + (q.v14[3] >>> (43 : ℕ)),
    (q.v25[4] &&& 1099511627775#64) + (q.v14[4] >>> (43 : ℕ)),
    (q.v25[5] &&& 1099511627775#64) + (q.v14[5] >>> (43 : ℕ)),
    (q.v25[6] &&& 1099511627775#64) + (q.v14[6] >>> (43 : ℕ)),
    (q.v25[7] &&& 1099511627775#64) + (q.v14[7] >>> (43 : ℕ))]

/-! ### The lane operations

Each is stated at the shape the lane script actually reaches, so that `simp`
never has to unfold `LLVM.lshr`, `LLVM.add` or `LLVM.mul` and never has to
rewrite inside a guard. -/

private theorem toNat_and_le' (x m : BitVec 64) : (x &&& m).toNat ≤ m.toNat := by
  simp only [BitVec.toNat_and]
  exact Nat.and_le_right

private theorem toNat_ushr (x : BitVec 64) (k : ℕ) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem shift_lt (y : BitVec 64) {k : ℕ} (hk : 40 ≤ k) : (y >>> k).toNat < 2 ^ 24 := by
  have h2 : (y >>> k).toNat ≤ y.toNat / 2 ^ 40 := by
    rw [toNat_ushr]
    exact Nat.div_le_div_left (Nat.pow_le_pow_right (by omega) hk) (by positivity)
  have h3 : y.toNat < 2 ^ 64 := y.isLt
  omega

/-- `lshr` by `43`: the poison guard is `43 ≥ 64`, discharged once here rather
than in all eight lanes. -/
private theorem lshr_43 (x : BitVec 64) :
    LLVM.lshr (PoisonOr.value x) (PoisonOr.value 43#64) = PoisonOr.value (x >>> (43 : ℕ)) := by
  simp [LLVM.lshr, LLVM.lshr?]

private theorem lshr_40 (x : BitVec 64) :
    LLVM.lshr (PoisonOr.value x) (PoisonOr.value 40#64) = PoisonOr.value (x >>> (40 : ℕ)) := by
  simp [LLVM.lshr, LLVM.lshr?]

private theorem sadd_false' {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 63) :
    a.saddOverflow b = false := Firedancer.saddOverflow_eq_false h

private theorem uadd_false' {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 63) :
    a.uaddOverflow b = false := Firedancer.uaddOverflow_eq_false (by omega)

private theorem add_nswnuw' {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 63) :
    LLVM.add (PoisonOr.value a) (PoisonOr.value b) { nsw := true, nuw := true }
      = PoisonOr.value (a + b) := by
  simp [LLVM.add, sadd_false' h, uadd_false' h, LLVM.add?]

/-- `%289`/`%292`: a masked lane plus a shifted one. -/
private theorem add_m43_s43 (x y : BitVec 64) :
    LLVM.add (PoisonOr.value (x &&& 8796093022207#64))
        (PoisonOr.value (y >>> (43 : ℕ))) { nsw := true, nuw := true }
      = PoisonOr.value ((x &&& 8796093022207#64) + (y >>> (43 : ℕ))) :=
  add_nswnuw' (by
    have := toNat_and_le' x 8796093022207#64
    have := shift_lt y (k := 43) (by omega)
    simp only [BitVec.toNat_ofNat] at *
    omega)

private theorem add_m40_s43 (x y : BitVec 64) :
    LLVM.add (PoisonOr.value (x &&& 1099511627775#64))
        (PoisonOr.value (y >>> (43 : ℕ))) { nsw := true, nuw := true }
      = PoisonOr.value ((x &&& 1099511627775#64) + (y >>> (43 : ℕ))) :=
  add_nswnuw' (by
    have := toNat_and_le' x 1099511627775#64
    have := shift_lt y (k := 43) (by omega)
    simp only [BitVec.toNat_ofNat] at *
    omega)

/-- `%286` on the lanes limb 5's carry did not wrap into. -/
private theorem add_s43_m43 (x y : BitVec 64) :
    LLVM.add (PoisonOr.value (y >>> (43 : ℕ)))
        (PoisonOr.value (x &&& 8796093022207#64)) { nsw := true, nuw := true }
      = PoisonOr.value ((y >>> (43 : ℕ)) + (x &&& 8796093022207#64)) :=
  add_nswnuw' (by
    have := toNat_and_le' x 8796093022207#64
    have := shift_lt y (k := 43) (by omega)
    simp only [BitVec.toNat_ofNat] at *
    omega)

/-- `%283`'s `mul`: limb 5's carry scaled by `19`, below `2 ^ 29`. -/
private theorem mul19_s40 (y : BitVec 64) :
    LLVM.mul (PoisonOr.value (y >>> (40 : ℕ))) (PoisonOr.value 19#64)
        { nsw := true, nuw := true }
      = PoisonOr.value ((y >>> (40 : ℕ)) * 19#64) := by
  have hy := shift_lt y (k := 40) (by omega)
  have hb : (y >>> (40 : ℕ)).toNat * (19#64 : BitVec 64).toNat < 2 ^ 63 := by
    simp only [BitVec.toNat_ofNat]
    omega
  have hs : (y >>> (40 : ℕ)).smulOverflow 19#64 = false :=
    Firedancer.smulOverflow_eq_false (by omega) (by simp) hb
  have hu : (y >>> (40 : ℕ)).umulOverflow 19#64 = false :=
    Firedancer.umulOverflow_eq_false (by omega)
  simp [LLVM.mul, hs, hu, LLVM.mul?]

/-- ... and `%286` on the lanes it wrapped into. -/
private theorem add_mul19_m43 (x y : BitVec 64) :
    LLVM.add (PoisonOr.value ((y >>> (40 : ℕ)) * 19#64))
        (PoisonOr.value (x &&& 8796093022207#64)) { nsw := true, nuw := true }
      = PoisonOr.value ((y >>> (40 : ℕ)) * 19#64 + (x &&& 8796093022207#64)) :=
  add_nswnuw' (by
    have h1 := toNat_and_le' x 8796093022207#64
    have hy := shift_lt y (k := 40) (by omega)
    have hmul : ((y >>> (40 : ℕ)) * 19#64).toNat = (y >>> (40 : ℕ)).toNat * 19 := by
      rw [Firedancer.toNat_mul (by simp only [BitVec.toNat_ofNat]; omega)]
      simp
    simp only [BitVec.toNat_ofNat] at *
    omega)

/-! The three projections, as `rfl` lemmas: unfolding `foldQuad` itself
normalises all twenty-four lanes in every one of the eight lane goals. -/

@[simp] theorem foldQuad_v14_eq (q : Quad) : (foldQuad q).v14 = #v[
    (q.v14[0] &&& 8796093022207#64) + (q.v03[0] >>> (43 : ℕ)),
    (q.v14[1] &&& 8796093022207#64) + (q.v03[1] >>> (43 : ℕ)),
    (q.v14[2] &&& 8796093022207#64) + (q.v03[2] >>> (43 : ℕ)),
    (q.v14[3] &&& 8796093022207#64) + (q.v03[3] >>> (43 : ℕ)),
    (q.v14[4] &&& 8796093022207#64) + (q.v03[4] >>> (43 : ℕ)),
    (q.v14[5] &&& 8796093022207#64) + (q.v03[5] >>> (43 : ℕ)),
    (q.v14[6] &&& 8796093022207#64) + (q.v03[6] >>> (43 : ℕ)),
    (q.v14[7] &&& 8796093022207#64) + (q.v03[7] >>> (43 : ℕ))] := rfl

set_option maxHeartbeats 1000000 in
/-- **The reduce's `v14`**: `%278`, `%288`, `%289`. -/
theorem denote_quadFold_v14 {q : Quad} {a282 a292 a293 : Vector (LLVM.IntW 64) 8}
    (h282 : a282 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .lshr
      (q.v03.map PoisonOr.value)[i.val] (toBitVecValue 64 quadShift43)[i.val])
    (h292 : a292 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (q.v14.map PoisonOr.value)[i.val] (toBitVecValue 64 quadMask43)[i.val])
    (h293 : a293 = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote (.add { nsw := true, nuw := true }) a292[i.val] a282[i.val]) :
    a293 = (foldQuad q).v14.map PoisonOr.value := by
  subst h282 h292 h293
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      InstCombine.binaryDenote, toBitVecValue, quadShift43, quadMask43,
      foldQuad_v14_eq, LLVM.and, LLVM.and?, PoisonOr.value_bind, lshr_43, add_m43_s43]

@[simp] theorem foldQuad_v25_eq (q : Quad) : (foldQuad q).v25 = #v[
    (q.v25[0] &&& 8796093022207#64) + (q.v14[0] >>> (43 : ℕ)),
    (q.v25[1] &&& 8796093022207#64) + (q.v14[1] >>> (43 : ℕ)),
    (q.v25[2] &&& 8796093022207#64) + (q.v14[2] >>> (43 : ℕ)),
    (q.v25[3] &&& 8796093022207#64) + (q.v14[3] >>> (43 : ℕ)),
    (q.v25[4] &&& 1099511627775#64) + (q.v14[4] >>> (43 : ℕ)),
    (q.v25[5] &&& 1099511627775#64) + (q.v14[5] >>> (43 : ℕ)),
    (q.v25[6] &&& 1099511627775#64) + (q.v14[6] >>> (43 : ℕ)),
    (q.v25[7] &&& 1099511627775#64) + (q.v14[7] >>> (43 : ℕ))] := rfl

@[simp] theorem foldQuad_v03_eq (q : Quad) : (foldQuad q).v03 = #v[
    (q.v25[4] >>> (40 : ℕ)) * 19#64 + (q.v03[0] &&& 8796093022207#64),
    (q.v25[5] >>> (40 : ℕ)) * 19#64 + (q.v03[1] &&& 8796093022207#64),
    (q.v25[6] >>> (40 : ℕ)) * 19#64 + (q.v03[2] &&& 8796093022207#64),
    (q.v25[7] >>> (40 : ℕ)) * 19#64 + (q.v03[3] &&& 8796093022207#64),
    (q.v25[0] >>> (43 : ℕ)) + (q.v03[4] &&& 8796093022207#64),
    (q.v25[1] >>> (43 : ℕ)) + (q.v03[5] &&& 8796093022207#64),
    (q.v25[2] >>> (43 : ℕ)) + (q.v03[6] &&& 8796093022207#64),
    (q.v25[3] >>> (43 : ℕ)) + (q.v03[7] &&& 8796093022207#64)] := rfl

set_option maxHeartbeats 1000000 in
/-- **... its `v25`**: `%280`, `%291`, `%292`. Limb 5 keeps only `40` bits, so
the mask is `%0` rather than `%1`. -/
theorem denote_quadFold_v25 {q : Quad} {a284 a295 a296 : Vector (LLVM.IntW 64) 8}
    (h284 : a284 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .lshr
      (q.v14.map PoisonOr.value)[i.val] (toBitVecValue 64 quadShift43)[i.val])
    (h295 : a295 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (q.v25.map PoisonOr.value)[i.val] (toBitVecValue 64 quadMask48)[i.val])
    (h296 : a296 = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote (.add { nsw := true, nuw := true }) a295[i.val] a284[i.val]) :
    a296 = (foldQuad q).v25.map PoisonOr.value := by
  subst h284 h295 h296
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp only [Vector.getElem_ofFn, Vector.getElem_map, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      InstCombine.binaryDenote, toBitVecValue, quadShift43, quadMask48,
      foldQuad_v25_eq, LLVM.and, LLVM.and?, PoisonOr.value_bind, lshr_43,
      add_m43_s43, add_m40_s43]

set_option maxHeartbeats 1000000 in
/-- **... and its `v03`**, the one that wraps: `%282`-`%286`. `%283`'s low
four lanes are poison -- `%44` is poison there -- and `%285` takes only its
high four, which is why nothing downstream sees them. -/
theorem denote_quadFold_v03 {q : Quad} {a286 a287 a288 a289 a290 : Vector (LLVM.IntW 64) 8}
    (h286 : a286 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .lshr
      (q.v25.map PoisonOr.value)[i.val] (toBitVecValue 64 quadShift48)[i.val])
    (h287 : a287 = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote (.mul { nsw := true, nuw := true })
        a286[i.val] quadMul19[i.val])
    (h288 : a288 = Vector.ofFn fun i : Fin 8 => InstCombine.binaryDenote .and
      (q.v03.map PoisonOr.value)[i.val] (toBitVecValue 64 quadMask43)[i.val])
    (h289 : a289 = LLVM.Ty.shufflevector (e := .bitvec (.concrete 64))
      [4, 5, 6, 7, 8, 9, 10, 11] a287 a286)
    (h290 : a290 = Vector.ofFn fun i : Fin 8 =>
      InstCombine.binaryDenote (.add { nsw := true, nuw := true }) a289[i.val] a288[i.val]) :
    a290 = (foldQuad q).v03.map PoisonOr.value := by
  subst h286 h287 h288 h289 h290
  apply Vector.ext
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [LLVM.Ty.shufflevector, InstCombine.binaryDenote, toBitVecValue, quadShift48,
      quadMask43, quadMul19, foldQuad_v03_eq, LLVM.and, LLVM.and?,
      lshr_43, lshr_40, mul19_s40, add_mul19_m43, add_s43_m43]

/-! ### The reduce, at the limb level

Lane `j` of the three vectors holds element `j`'s limbs `0,1,2` and lane
`j+4` its `3,4,5`, so the transposed reduce is `Fold.lean`'s `foldLimb` on
each of the four elements -- and hence the identity on the point. -/

private theorem and43 (x : BitVec 64) : (x &&& 8796093022207#64).toNat = x.toNat % 2 ^ 43 := by
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show (8796093022207 : ℕ) = 2 ^ 43 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

private theorem and40 (x : BitVec 64) : (x &&& 1099511627775#64).toNat = x.toNat % 2 ^ 40 := by
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show (1099511627775 : ℕ) = 2 ^ 40 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]

/-- A carry-in lane: the mask keeps 43 bits, the shift brings at most 21. -/
private theorem laneA (x y : BitVec 64) :
    ((x &&& 8796093022207#64) + (y >>> (43 : ℕ))).toNat
      = x.toNat % 2 ^ 43 + y.toNat / 2 ^ 43 := by
  have hy : y.toNat < 2 ^ 64 := y.isLt
  have hd : y.toNat / 2 ^ 43 < 2 ^ 21 := Nat.div_lt_of_lt_mul (by omega)
  have hm : x.toNat % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  rw [Firedancer.toNat_add (by rw [and43, toNat_ushr]; omega), and43, toNat_ushr]

/-- Limb 3's lane: `laneA` with the operands the other way round. -/
private theorem laneD (x y : BitVec 64) :
    ((y >>> (43 : ℕ)) + (x &&& 8796093022207#64)).toNat
      = x.toNat % 2 ^ 43 + y.toNat / 2 ^ 43 := by
  have hy : y.toNat < 2 ^ 64 := y.isLt
  have hd : y.toNat / 2 ^ 43 < 2 ^ 21 := Nat.div_lt_of_lt_mul (by omega)
  have hm : x.toNat % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  rw [Firedancer.toNat_add (by rw [and43, toNat_ushr]; omega), and43, toNat_ushr]
  omega

/-- Limb 5's lane: the mask keeps 40 bits. -/
private theorem laneB (x y : BitVec 64) :
    ((x &&& 1099511627775#64) + (y >>> (43 : ℕ))).toNat
      = x.toNat % 2 ^ 40 + y.toNat / 2 ^ 43 := by
  have hy : y.toNat < 2 ^ 64 := y.isLt
  have hd : y.toNat / 2 ^ 43 < 2 ^ 21 := Nat.div_lt_of_lt_mul (by omega)
  have hm : x.toNat % 2 ^ 40 < 2 ^ 40 := Nat.mod_lt _ (by norm_num)
  rw [Firedancer.toNat_add (by rw [and40, toNat_ushr]; omega), and40, toNat_ushr]

/-- Limb 0's lane: the wrap-around, scaled by `19`. -/
private theorem laneC (x y : BitVec 64) :
    ((y >>> (40 : ℕ)) * 19#64 + (x &&& 8796093022207#64)).toNat
      = x.toNat % 2 ^ 43 + 19 * (y.toNat / 2 ^ 40) := by
  have hy : y.toNat < 2 ^ 64 := y.isLt
  have hd : y.toNat / 2 ^ 40 < 2 ^ 24 := Nat.div_lt_of_lt_mul (by omega)
  have hm : x.toNat % 2 ^ 43 < 2 ^ 43 := Nat.mod_lt _ (by norm_num)
  have hmul : ((y >>> (40 : ℕ)) * 19#64).toNat = y.toNat / 2 ^ 40 * 19 := by
    rw [Firedancer.toNat_mul (by rw [toNat_ushr]; simp only [BitVec.toNat_ofNat]; omega),
      toNat_ushr]
    simp
  rw [Firedancer.toNat_add (by rw [hmul, and43]; omega), hmul, and43]
  omega

/-- **The reduce is `foldLimb` on each element.** -/
theorem laneFunc_foldQuad (q : Quad) (j : Fin 4) :
    (foldQuad q).vectorFunc j = foldLimb (q.vectorFunc j) := by
  funext k
  simp only [Quad.vectorFunc, Function.comp_apply, Quad.vector, quadElemVec, laneFunc,
    foldQuad_v03_eq, foldQuad_v14_eq, foldQuad_v25_eq]
  fin_cases j <;> fin_cases k <;>
    simp only [foldLimb, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, laneFunc, Nat.reduceAdd,
      Fin.getElem_fin, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.mod_succ,
      laneA, laneB, laneC, laneD]

/-- The reduce leaves every element of the QUAD unchanged in `GF(2^255-19)`. -/
theorem quadElem_foldQuad (q : Quad) (j : Fin 4) :
    quadElem (foldQuad q) j = quadElem q j := by
  rw [quadElem, quadElem, laneFunc_foldQuad, decodeNat_foldLimb_zmod]

/-- **`FD_R43X6_QUAD_FOLD_UNSIGNED` is the identity on the point.** -/
theorem toPoint_foldQuad (q : Quad) : (foldQuad q).toPoint = q.toPoint := by
  show Ed25519.Point.mk (quadElem (foldQuad q) 0) (quadElem (foldQuad q) 1)
      (quadElem (foldQuad q) 2) (quadElem (foldQuad q) 3) = _
  rw [quadElem_foldQuad, quadElem_foldQuad, quadElem_foldQuad, quadElem_foldQuad]
  rfl

end Firedancer.Avx512
