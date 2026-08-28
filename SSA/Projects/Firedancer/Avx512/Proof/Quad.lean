/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Common
import SSA.Projects.Firedancer.Avx512.Spec.Quad

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

/-- `BitVec.toNat_ofNat` reintroduces a `% 2^64` that is always vacuous on a
lane read back out of a 64-bit vector. The default simp set cancels it; under
`simp only` it has to be named. -/
@[simp] theorem toNat_mod_two_pow_64 (v : BitVec 64) :
    v.toNat % 18446744073709551616 = v.toNat :=
  Nat.mod_eq_of_lt v.isLt

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
             simp_peephole
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
argument out of the valuation. -/
macro "quad_vecbin " h:term " with " hs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp only [HVector.head]
             apply Vector.ext
             intro i hi
             interval_cases i
             all_goals simp +zetaDelta +decide only
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
                false_and, and_false, true_and, and_true, $hs,*]))

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

/-- An inner extract window sits at the sum of the two offsets. -/
theorem extractLsb'_extractLsb'_of_le {w : Nat} {x : BitVec w} {s n s' n' : Nat}
    (h : s' + n' ≤ n) :
    (x.extractLsb' s n).extractLsb' s' n' = x.extractLsb' (s + s') n' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  rw [show s + (s' + i) = s + s' + i from by omega]
  simp [hi, show s' + i < n from by omega]

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
  rw [extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega), Nat.mul_comm i 64]

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
  rw [extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega), Nat.mul_comm i 64]

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
  rw [extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega), Nat.mul_comm i 64]

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

end Firedancer.Avx512
