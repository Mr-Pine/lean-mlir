import SSA.Projects.Firedancer.Conformance.Spec.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_frombytes_2x

namespace Firedancer
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-! ## `pointOutMem`, read back and passed over

`live?_pointOutMem_ne` and `live?_pointOutMem_congr` are the liveness halves
of these two facts; what a conformance proof actually asks for is the
`readPoint`-level statement, so it is stated here. -/

/-- A field-element read passes over a splice that misses all five of its
limbs: `readLimb?_splice_of_disjoint`, once for the whole element. -/
theorem Ref.readFieldElem?_splice_of_disjoint {m : MemoryState} {p q : Pointer}
    {w : Nat} {x : BitVec w}
    (h : ∀ i : Fin 5, q.id ≠ p.id ∨ q.offsetInBits + w ≤ p.offsetInBits + 64 * i.toNat
      ∨ p.offsetInBits + 64 * i.toNat + 64 ≤ q.offsetInBits) :
    Ref.readFieldElem? p (m.splice q x) = Ref.readFieldElem? p m := by
  have e : ∀ i, Ref.readLimb? p i (m.splice q x) = Ref.readLimb? p i m :=
    fun i => Ref.readLimb?_splice_of_disjoint i (h i)
  simp only [Ref.readFieldElem?, e]

/-- **Noninterference.** The four coordinate stores at `r` leave a point at
another block alone. -/
theorem Ref.readPoint_pointOutMem_ne {m : MemoryState} {q r : Pointer}
    {oX oY oZ oT : Fin 5 → BitVec 64} (hne : r.id ≠ q.id)
    (hq : Ref.IsPointPtr m q)
    (hq' : Ref.IsPointPtr (Ref.pointOutMem m r oX oY oZ oT) q) :
    Ref.readPoint hq' = Ref.readPoint hq :=
  Ref.readPoint_of_live?_eq (Ref.live?_pointOutMem_ne hne) hq hq'

/-- **Readback.** The point at `r` after the four stores is the one they
wrote. Note the field order: the struct is `X, Y, T, Z` at 0, 40, 80, 120
bytes, so `oZ` -- stored at 120 -- is the `Z` field. -/
theorem Ref.readPoint_pointOutMem {m : MemoryState} {r : Pointer}
    (hr : Ref.IsPointPtr m r) (oX oY oZ oT : Fin 5 → BitVec 64) :
    Ref.readPoint (Ref.isPointPtr_pointOutMem hr oX oY oZ oT)
      = { X := Ref.decodeFieldElem fun i => (oX i).toNat,
          Y := Ref.decodeFieldElem fun i => (oY i).toNat,
          Z := Ref.decodeFieldElem fun i => (oZ i).toNat,
          T := Ref.decodeFieldElem fun i => (oT i).toNat } := by
  have hnw : r.offset.toNat + 4 * 5 * 8 ≤ 2 ^ 64 := hr.right
  -- the four coordinate windows, in bits from `r`: 0, 320, 640, 960
  have off40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    rw [Ref.withOffset_offsetInBits (by simp; omega)]; simp
  have off80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    rw [Ref.withOffset_offsetInBits (by simp; omega)]; simp
  have off120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    rw [Ref.withOffset_offsetInBits (by simp; omega)]; simp
  have hf0 : Ref.IsFieldElemPtr m r := Ref.coordPtr_zero r ▸ Ref.isCoordPtr hr 0
  have hf1 : Ref.IsFieldElemPtr m (r.withOffset 40) := by
    simpa [Ref.coordPtr_one] using Ref.isCoordPtr hr 1
  have hf2 : Ref.IsFieldElemPtr m (r.withOffset 80) := by
    simpa [Ref.coordPtr_two] using Ref.isCoordPtr hr 2
  have hf3 : Ref.IsFieldElemPtr m (r.withOffset 120) := by
    simpa [Ref.coordPtr_three] using Ref.isCoordPtr hr 3
  -- `X` is written first, so its read passes over the other three
  have hvX : Ref.readFieldElem? r (Ref.pointOutMem m r oX oY oZ oT)
      = some (Ref.decodeFieldElem fun i => (oX i).toNat) := by
    simp only [Ref.pointOutMem]
    rw [Ref.readFieldElem?_splice_of_disjoint
          (fun i => Or.inr (Or.inr (by have hi : i.toNat < 5 := i.isLt; rw [off80]; omega))),
        Ref.readFieldElem?_splice_of_disjoint
          (fun i => Or.inr (Or.inr (by have hi : i.toNat < 5 := i.isLt; rw [off120]; omega))),
        Ref.readFieldElem?_splice_of_disjoint
          (fun i => Or.inr (Or.inr (by have hi : i.toNat < 5 := i.isLt; rw [off40]; omega))),
        Ref.readFieldElem?_splice (Ref.packLimbs oX) hf0.left]
    simp only [Ref.extractLsb'_packLimbs]
  have hvY : Ref.readFieldElem? (r.withOffset 40) (Ref.pointOutMem m r oX oY oZ oT)
      = some (Ref.decodeFieldElem fun i => (oY i).toNat) := by
    simp only [Ref.pointOutMem]
    rw [Ref.readFieldElem?_splice_of_disjoint
          (fun i => Or.inr (Or.inr (by have hi : i.toNat < 5 := i.isLt; rw [off40, off80]; omega))),
        Ref.readFieldElem?_splice_of_disjoint
          (fun i => Or.inr (Or.inr (by have hi : i.toNat < 5 := i.isLt; rw [off40, off120]; omega))),
        Ref.readFieldElem?_splice (Ref.packLimbs oY) (fits_splice hf1.left)]
    simp only [Ref.extractLsb'_packLimbs]
  -- `T` is written last, so nothing stands between its store and its read
  have hvT : Ref.readFieldElem? (r.withOffset 80) (Ref.pointOutMem m r oX oY oZ oT)
      = some (Ref.decodeFieldElem fun i => (oT i).toNat) := by
    simp only [Ref.pointOutMem]
    rw [Ref.readFieldElem?_splice (Ref.packLimbs oT)
      (fits_splice (fits_splice (fits_splice hf2.left)))]
    simp only [Ref.extractLsb'_packLimbs]
  have hvZ : Ref.readFieldElem? (r.withOffset 120) (Ref.pointOutMem m r oX oY oZ oT)
      = some (Ref.decodeFieldElem fun i => (oZ i).toNat) := by
    simp only [Ref.pointOutMem]
    rw [Ref.readFieldElem?_splice_of_disjoint
          (fun i => Or.inr (Or.inl (by rw [off80, off120]; omega))),
        Ref.readFieldElem?_splice (Ref.packLimbs oZ)
          (fits_splice (fits_splice hf3.left))]
    simp only [Ref.extractLsb'_packLimbs]
  -- the same four pointers, at the memory the stores left
  have lift : ∀ {q : Pointer}, Ref.IsFieldElemPtr m q →
      Ref.IsFieldElemPtr (Ref.pointOutMem m r oX oY oZ oT) q := by
    intro q hq
    simp only [Ref.pointOutMem]
    exact Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice
      (Ref.isFieldElemPtr_splice (Ref.isFieldElemPtr_splice hq)))
  exact Ref.readPoint_eq_of _
    (Ref.readFieldElem_eq_of (h := lift hf0) hvX)
    (Ref.readFieldElem_eq_of (h := lift hf1) hvY)
    (Ref.readFieldElem_eq_of (h := lift hf2) hvT)
    (Ref.readFieldElem_eq_of (h := lift hf3) hvZ)

/-! ## `writeQuad`, read back and passed over

The `Quad` counterparts of the three above. `unflatten_readQuad_v03`/`_v14`/
`_v25` do the bit-level work; what is missing is the statement over
`writeQuad` itself. -/

/-- The three whole-vector stores miss every other block. -/
theorem Avx512.live?_writeQuad_ne {m : MemoryState} {p : Pointer} {q : Avx512.Quad}
    {b : BlockId} (h : p.id ≠ b) : (m.writeQuad p q).live? b = m.live? b := by
  simp only [MemoryState.writeQuad, live?_splice_ne (p := p.withOffset 128) h,
    live?_splice_ne (p := p.withOffset 64) h, live?_splice_ne h]

/-- **Noninterference.** A store of a QUAD at `r` leaves a QUAD at another
block alone. -/
theorem Avx512.readQuad_writeQuad_ne {m : MemoryState} {p r : Pointer} {q : Avx512.Quad}
    (hne : r.id ≠ p.id) (hp : Avx512.IsQuadPtr m p)
    (hp' : Avx512.IsQuadPtr (m.writeQuad r q) p) :
    Avx512.readQuad hp' = Avx512.readQuad hp :=
  Avx512.readQuad_of_live?_eq (Avx512.live?_writeQuad_ne hne) hp hp'

/-- **Readback.** The QUAD at `p` after the three whole-vector stores is the
one they wrote. -/
theorem Avx512.readQuad_writeQuad {m : MemoryState} {p : Pointer} {q : Avx512.Quad}
    (hp : Avx512.IsQuadPtr m p) (h : Avx512.IsQuadPtr (m.writeQuad p q) p) :
    Avx512.readQuad h = q := by
  obtain ⟨⟨blk, hblk, hlen⟩, hnw⟩ := hp
  simp only [LiveBlock.lengthInBits] at hlen
  have hl : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  -- the two gep'd field pointers, 512 and 1024 bits along
  have off64 : (p.withOffset 64).offsetInBits = p.offsetInBits + 512 := by
    rw [Ref.withOffset_offsetInBits (by simp; omega)]; simp
  have off128 : (p.withOffset 128).offsetInBits = p.offsetInBits + 1024 := by
    rw [Ref.withOffset_offsetInBits (by simp; omega)]; simp
  -- the block the three stores leave
  have h1 : (m.splice p (Avx512.vecBV q.v03)).live? p.id
      = some { length := blk.length,
               bytes := spliceBits blk.bytes p.offsetInBits (Avx512.vecBV q.v03) } :=
    splicedLive m p blk hl _
  have h2 : ((m.splice p (Avx512.vecBV q.v03)).splice (p.withOffset 64)
        (Avx512.vecBV q.v14)).live? p.id
      = some { length := blk.length,
               bytes := spliceBits (spliceBits blk.bytes p.offsetInBits (Avx512.vecBV q.v03))
                 (p.offsetInBits + 512) (Avx512.vecBV q.v14) } := by
    have e := splicedLive _ (p.withOffset 64) _ h1 (Avx512.vecBV q.v14)
    rwa [off64] at e
  have h3 : (m.writeQuad p q).live? p.id
      = some { length := blk.length,
               bytes := spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits
                 (Avx512.vecBV q.v03)) (p.offsetInBits + 512) (Avx512.vecBV q.v14))
                 (p.offsetInBits + 1024) (Avx512.vecBV q.v25) } := by
    have e := splicedLive _ (p.withOffset 128) _ h2 (Avx512.vecBV q.v25)
    rwa [off128] at e
  -- each 512-bit window reads back the vector stored into it
  have w25 : (spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits (Avx512.vecBV q.v03))
        (p.offsetInBits + 512) (Avx512.vecBV q.v14))
        (p.offsetInBits + 1024) (Avx512.vecBV q.v25)).extractLsb' (p.offsetInBits + 1024) 512
      = Avx512.vecBV q.v25 :=
    extractLsb'_spliceBits _ _ _ (by omega)
  have w14 : (spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits (Avx512.vecBV q.v03))
        (p.offsetInBits + 512) (Avx512.vecBV q.v14))
        (p.offsetInBits + 1024) (Avx512.vecBV q.v25)).extractLsb' (p.offsetInBits + 512) 512
      = Avx512.vecBV q.v14 := by
    rw [extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega)),
      extractLsb'_spliceBits _ _ _ (by omega)]
  have w03 : (spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits (Avx512.vecBV q.v03))
        (p.offsetInBits + 512) (Avx512.vecBV q.v14))
        (p.offsetInBits + 1024) (Avx512.vecBV q.v25)).extractLsb' p.offsetInBits 512
      = Avx512.vecBV q.v03 := by
    rw [extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega)),
      extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega)),
      extractLsb'_spliceBits _ _ _ (by omega)]
  -- a fully-defined vector is determined by its `PoisonOr.value` image
  have mapInj : ∀ {u v : Vector (BitVec 64) 8},
      u.map PoisonOr.value = v.map PoisonOr.value → u = v := by
    intro u v huv
    refine Vector.ext fun i hi => ?_
    have e : (u.map PoisonOr.value)[i] = (v.map PoisonOr.value)[i] := by rw [huv]
    simpa using e
  refine Avx512.Quad.ext ?_ ?_ ?_
  · have hu := Avx512.unflatten_readQuad_v03 h h3
    rw [w03, Avx512.unflatten_vecBV] at hu
    exact (mapInj hu).symm
  · have hu := Avx512.unflatten_readQuad_v14 h h3
    rw [w14, Avx512.unflatten_vecBV] at hu
    exact (mapInj hu).symm
  · have hu := Avx512.unflatten_readQuad_v25 h h3
    rw [w25, Avx512.unflatten_vecBV] at hu
    exact (mapInj hu).symm

/-! ## One encoding, read two ways

`ref` reads a 32-byte buffer as one `uint256`; AVX reads the same bytes as a
`wv_t`'s four lanes. Given that the two states hold the same bytes there, the
lanes are the word's four windows -- so the two sides name the same `y` and
read the same sign bit. -/

/-- The two states hold the same 32 bytes at `q` / `q'`. -/
abbrev SameBuf (m m' : MemoryState) (q q' : Pointer) : Prop :=
  ((fun blk => blk.bytes.extractLsb' q.offsetInBits 256) <$> m.live? q.id)
    = ((fun blk => blk.bytes.extractLsb' q'.offsetInBits 256) <$> m'.live? q'.id)

/-- The AVX lanes are the four 64-bit windows of the `ref` buffer's word. -/
theorem readWv_eq_extractLsb' {m m' : MemoryState} {q q' : Pointer}
    (hq : IsByteBufPtr m q) (hq' : Avx512.IsWvPtr m' q') (hbufs : SameBuf m m' q q') :
    Avx512.readWv hq'
      = Vector.ofFn (fun j : Fin 4 => (readBuf hq).extractLsb' (64 * j.val) 64) := by
  obtain ⟨blk, hblk, -⟩ := hq.left
  obtain ⟨blk', hblk', -⟩ := hq'.left
  have hl : m.live? q.id = some blk := by simp only [MemoryState.live?, hblk]
  have hl' : m'.live? q'.id = some blk' := by simp only [MemoryState.live?, hblk']
  rw [SameBuf, hl, hl'] at hbufs
  simp at hbufs
  have hW : readBuf hq = blk'.bytes.extractLsb' q'.offsetInBits 256 := by
    simp [readBuf, readBuf?, hl, hbufs]
  rw [hW]
  refine Vector.ext fun j hj => ?_
  simp [Avx512.readWv, Avx512.readWv?, hl']
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]

/-- ... so both sides name the same `y`. -/
theorem decodeBytes_eq_wvY {m m' : MemoryState} {q q' : Pointer}
    (hq : IsByteBufPtr m q) (hq' : Avx512.IsWvPtr m' q') (hbufs : SameBuf m m' q q') :
    Ref.decodeBytes (readBuf hq) = Avx512.wvY (Avx512.readWv hq') := by
  have hnat : Avx512.wvNat (Avx512.readWv hq') = (readBuf hq).toNat := by
    have hlt := (readBuf hq).isLt
    rw [readWv_eq_extractLsb' hq hq' hbufs]
    simp only [Avx512.wvNat, Vector.getElem_ofFn, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
    norm_num
    omega
  rw [Ref.decodeBytes, Avx512.wvY, hnat, BitVec.extractLsb'_toNat]
  norm_num

/-- ... and read the same sign bit: the buffer's top bit is the top bit of the
`wv_t`'s last lane. -/
theorem wvSign_eq_getElem_readBuf {m m' : MemoryState} {q q' : Pointer}
    (hq : IsByteBufPtr m q) (hq' : Avx512.IsWvPtr m' q') (hbufs : SameBuf m m' q q') :
    Avx512.wvSign (Avx512.readWv hq') = (readBuf hq)[255] := by
  rw [Avx512.wvSign, readWv_eq_extractLsb' hq hq' hbufs]
  simp [BitVec.getLsbD_extractLsb']

/-- The curve equation with the coordinates separated: `x²` alone on the left,
a function of `y` on the right. `d·y² + 1` is never zero (`denom_ne_zero`), so
the division is the honest one -- and the right-hand side is exactly the
quantity `Decodable` tests for squareness. -/
theorem sq_eq_of_onCurve {x y : ZMod _root_.p}
    (h : -x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2) :
    x ^ 2 = (y ^ 2 - 1) / (d * y ^ 2 + 1) := by
  rw [eq_div_iff (denom_ne_zero y)]
  linear_combination -h


/-- Two points agree when their four coordinates do. `Ed25519.Point` carries no
`@[ext]`, so the structure lemma is not generated for it. -/
theorem _root_.Ed25519.Point.ext' {P Q : Point} (hX : P.X = Q.X) (hY : P.Y = Q.Y)
    (hZ : P.Z = Q.Z) (hT : P.T = Q.T) : P = Q := by
  cases P; cases Q; simp_all


/-- A square root is determined up to sign: `ZMod p` is a domain (`prime_p`),
so `a² = b²` factors as `(a - b)(a + b) = 0`. -/
theorem eq_or_eq_neg_of_sq_eq_sq {a b : ZMod _root_.p} (h : a ^ 2 = b ^ 2) :
    a = b ∨ a = -b := by
  rcases mul_eq_zero.mp (show (a - b) * (a + b) = 0 by linear_combination h) with h' | h'
  · exact Or.inl (by linear_combination h')
  · exact Or.inr (by linear_combination h')


/-- Negating flips the parity of the canonical representative: `p` is odd, and
for `x ≠ 0` the representative of `-x` is `p - x.val`. This is what lets one
sign bit pin down which of the two square roots `x` is. -/
theorem val_neg_parity_ne {x : ZMod _root_.p} (hx : x ≠ 0) :
    (-x).val % 2 ≠ x.val % 2 := by
  haveI : NeZero _root_.p := ⟨by norm_num [_root_.p]⟩
  have hodd : _root_.p % 2 = 1 := by norm_num [_root_.p]
  have hlt : x.val < _root_.p := ZMod.val_lt x
  have hpos : 0 < x.val := ZMod.val_pos.mpr hx
  rw [ZMod.neg_val, if_neg hx]
  omega


/-- The decompression conditions, stated over the `y` and sign bit an encoding
names rather than over the encoding itself: what `Ref.IsDecoding` and
`Avx512.Decodes` both unfold to, so a fact proved here transfers to either. -/
abbrev DecodesAs (P : Point) (y₀ : ZMod _root_.p) (sgn : Bool) : Prop :=
  OnCurve P.x P.y ∧ P.Z = 1 ∧ P.Y = y₀ ∧ P.T / P.Z = P.x * P.y
    ∧ (P.X ≠ 0 → (P.X.val % 2 = 0 ↔ sgn = false))

/-- **Decompression is deterministic.** The curve equation pins `X²` from `Y`,
and the sign bit picks which of the two roots `X` is -- so two points that
decode one encoding are equal. This is the whole conformance argument for a
single point; the two sides differ only in how they name `y₀` and `sgn`. -/
theorem eq_of_decodesAs {P Q : Point} {y₀ : ZMod _root_.p} {sgn : Bool}
    (hP : DecodesAs P y₀ sgn) (hQ : DecodesAs Q y₀ sgn) : P = Q := by
  obtain ⟨hPc, hPz, hPy, hPt, hPx⟩ := hP
  obtain ⟨hQc, hQz, hQy, hQt, hQx⟩ := hQ
  have hY : P.Y = Q.Y := hPy.trans hQy.symm
  -- `Z = 1` on both sides, so the affine coordinates are the projective ones
  simp only [Point.x, Point.y, hPz, hQz, inv_one, mul_one, div_one, OnCurve]
    at hPc hQc hPt hQt
  -- the curve equation with `X` alone on the left: both sides solve the same one
  rw [hY] at hPc
  have hXsq := (sq_eq_of_onCurve hPc).trans (sq_eq_of_onCurve hQc).symm
  by_cases hx0 : Q.X = 0
  case pos =>
    -- `X` zero on one side is zero on the other, and then `T = X·Y = 0` on both
    have h0 := (pow_eq_zero_iff (by norm_num)).mp
      (hXsq.trans (show Q.X ^ 2 = 0 by rw [hx0]; ring))
    refine Point.ext' (h0.trans hx0.symm) hY (hPz.trans hQz.symm) ?_
    rw [hPt, hQt, h0, hx0, zero_mul, zero_mul]
  -- otherwise both sign clauses fire, and `X` is `X'` up to sign
  have hne : P.X ≠ 0 := fun h => hx0 ((pow_eq_zero_iff (by norm_num)).mp
    (show Q.X ^ 2 = 0 by rw [← hXsq, h]; ring))
  replace hPx := hPx hne
  replace hQx := hQx hx0
  obtain h | h := eq_or_eq_neg_of_sq_eq_sq hXsq
  · refine Point.ext' h hY (hPz.trans hQz.symm) ?_
    rw [hPt, hQt, h, hY]
  -- `X = -X'` would flip the parity of the representative, contradicting the
  -- sign bit the two sides share
  · exfalso
    have hflip := val_neg_parity_ne hne
    rw [h, neg_neg] at hflip
    rw [h] at hPx
    have hiff := hPx.trans hQx.symm
    omega


theorem fd_ed25519_point_frombytes_2x : fd_ed25519_point_frombytes_2x_equivalent := by
  unfold fd_ed25519_point_frombytes_2x_equivalent
  intro s a b aBuf bBuf hs ha hb haBuf hbBuf hbBufA hbA haBufA hbBufB haNull hbNull
  intro refResult'
  intro s' a' b' aBuf' bBuf' hs' ha' hb' haBuf' hbBuf' hbA'
  intro avxResult'

  intro haBufs hbBufs

  obtain ⟨s₂, refRes, hrefRes, hs₂⟩ := Ref.fd_ed25519_point_frombytes_2x_conforms a aBuf b bBuf s hs ha haBuf hb hbBuf haBufA hbBufB haNull hbNull
  refine ⟨([refRes]ₕ, s₂), ?_⟩

  obtain ⟨s'₂, avxRes, aQuad', bQuad', havxRes, hs'₂, hs'₂State⟩ := Avx512.fd_ed25519_point_frombytes_2x_conforms a' aBuf' b' bBuf' s' hs' ha' haBuf' hb' hbBuf'
  refine ⟨([avxRes]ₕ, s'₂), ?_⟩

  refine ⟨by simp only [refResult', hrefRes], by simp only [avxResult', havxRes], ?_⟩

  intro ⟨resEq, resOk⟩
  simp at resEq resOk

  by_cases hsqₐ : IsSquare ((Ref.decodeBytes (readBuf haBuf) ^ 2 - 1) / (d * Ref.decodeBytes (readBuf haBuf) ^ 2 + 1))
  case neg =>
    simp [hsqₐ] at hs₂
    simp [hs₂.left] at resOk
  by_cases hsq'ₐ : Avx512.Decodable (Avx512.readWv haBuf')
  case neg =>
    simp [hsq'ₐ, ← resEq, resOk] at hs'₂State
  simp [hsqₐ] at hs₂
  simp [hsq'ₐ] at hs'₂State
  obtain ⟨aX, aY, aZ, aT, hdecA, -, hfailB, hokB⟩ := hs₂
  refine ⟨aX, aY, aZ, aT, ?_⟩

  -- `bBuf` is read at the memory `a`'s four coordinate stores left; those miss
  -- its block, so the second squareness test is the one over the entry state.
  have hreadB : readBuf (m := Ref.pointOutMem s.mem a aX aY aZ aT)
      (isByteBufPtr_splice (isByteBufPtr_splice
        (isByteBufPtr_splice (isByteBufPtr_splice hbBuf))))
      = readBuf hbBuf :=
    readBuf_of_live?_eq (Ref.live?_pointOutMem_ne (Ne.symm hbBufA))
  rw [hreadB] at hfailB hokB

  by_cases hsq : IsSquare ((Ref.decodeBytes (readBuf hbBuf) ^ 2 - 1) / (d * Ref.decodeBytes (readBuf hbBuf) ^ 2 + 1))
  case neg =>
    simp [hsq] at hfailB
    simp [hfailB.left] at resOk
  simp [hsq] at hokB
  by_cases hsq' : Avx512.Decodable (Avx512.readWv hbBuf')
  case neg =>
    simp [hsq', ← resEq, resOk] at hs'₂State
  simp [hsq'] at hs'₂State

  obtain ⟨bX, bY, bZ, bT, hs₂, hrefDecodes, -⟩ := hokB.right
  refine ⟨bX, bY, bZ, bT, ?_⟩

  -- `a`'s point survives `b`'s four stores, and then reads back as what its own
  -- four wrote; `b`'s is the readback of the outer store on its own.
  have hreadPointA :
      Ref.readPoint (Ref.isPointPtr_pointOutMem' (r := b)
          (Ref.isPointPtr_pointOutMem' (r := a) ha aX aY aZ aT) bX bY bZ bT)
        = { X := Ref.decodeFieldElem fun i => (aX i).toNat,
            Y := Ref.decodeFieldElem fun i => (aY i).toNat,
            Z := Ref.decodeFieldElem fun i => (aZ i).toNat,
            T := Ref.decodeFieldElem fun i => (aT i).toNat } :=
    (Ref.readPoint_pointOutMem_ne hbA
        (Ref.isPointPtr_pointOutMem ha aX aY aZ aT)
        (Ref.isPointPtr_pointOutMem' (r := b)
          (Ref.isPointPtr_pointOutMem' (r := a) ha aX aY aZ aT) bX bY bZ bT)).trans
      (Ref.readPoint_pointOutMem ha aX aY aZ aT)
  have hreadPointB :
      Ref.readPoint (Ref.isPointPtr_pointOutMem
          (Ref.isPointPtr_pointOutMem' (r := a) hb aX aY aZ aT) bX bY bZ bT)
        = { X := Ref.decodeFieldElem fun i => (bX i).toNat,
            Y := Ref.decodeFieldElem fun i => (bY i).toNat,
            Z := Ref.decodeFieldElem fun i => (bZ i).toNat,
            T := Ref.decodeFieldElem fun i => (bT i).toNat } :=
    Ref.readPoint_pointOutMem
      (Ref.isPointPtr_pointOutMem' (r := a) hb aX aY aZ aT) bX bY bZ bT

  -- ... and the same on the AVX side: `a'`'s QUAD survives `b'`'s three
  -- stores, `b'`'s is the readback of the outer store on its own.
  have hreadQuadA :
      Avx512.readQuad (Avx512.isQuadPtr_writeQuad (r := b')
          (Avx512.isQuadPtr_writeQuad (r := a') ha' aQuad') bQuad')
        = aQuad' :=
    (Avx512.readQuad_writeQuad_ne hbA'
        (Avx512.isQuadPtr_writeQuad (r := a') ha' aQuad')
        (Avx512.isQuadPtr_writeQuad (r := b')
          (Avx512.isQuadPtr_writeQuad (r := a') ha' aQuad') bQuad')).trans
      (Avx512.readQuad_writeQuad ha' (Avx512.isQuadPtr_writeQuad (r := a') ha' aQuad'))
  have hreadQuadB :
      Avx512.readQuad (Avx512.isQuadPtr_writeQuad (r := b')
          (Avx512.isQuadPtr_writeQuad (r := a') hb' aQuad') bQuad')
        = bQuad' :=
    Avx512.readQuad_writeQuad
      (Avx512.isQuadPtr_writeQuad (r := a') hb' aQuad')
      (Avx512.isQuadPtr_writeQuad (r := b')
        (Avx512.isQuadPtr_writeQuad (r := a') hb' aQuad') bQuad')

  intro refMem refAfterState

  refine ⟨aQuad', bQuad', ?_⟩
  intro avxMem avxAfterState

  simp
  refine ⟨?a, ?state', ?state, ?b⟩

  case a =>
    simp only [hreadQuadA]
    -- `a`'s point is untouched by `b`'s four stores, so the goal reads it at the
    -- memory `hdecA` describes -- otherwise every later unification has to check
    -- two `readPoint`s at different four-fold splices for defeq.
    rw [Ref.readPoint_pointOutMem_ne hbA
        (Ref.isPointPtr_pointOutMem ha aX aY aZ aT)
        (Ref.isPointPtr_pointOutMem' (r := b)
          (Ref.isPointPtr_pointOutMem' (r := a) ha aX aY aZ aT) bX bY bZ bT)]
    refine eq_of_decodesAs hdecA ?_
    -- the AVX decoding, in the `ref` side's names for `y` and the sign bit
    rw [decodeBytes_eq_wvY haBuf haBuf' haBufs,
      ← wvSign_eq_getElem_readBuf haBuf haBuf' haBufs]
    exact hs'₂State.right.left

  case b =>
    -- `b` is written last, so its point is already at the memory `hrefDecodes`
    -- describes: no transport needed
    simp only [hreadQuadB]
    refine eq_of_decodesAs hrefDecodes ?_
    rw [hreadB, decodeBytes_eq_wvY hbBuf hbBuf' hbBufs,
      ← wvSign_eq_getElem_readBuf hbBuf hbBuf' hbBufs]
    exact hs'₂State.right.right

  case state' =>
    simp [avxAfterState, avxMem, hs'₂]
  case state =>
    simp [refAfterState, refMem, hs₂]

end Firedancer
