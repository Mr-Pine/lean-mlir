/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Common.Proof.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_curve25519_into_precomputed
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_with_opts
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Avx512.Proof.Point.fd_ed25519_point_add_final_mul_projective
import SSA.Projects.Firedancer.Proof.WriteChain

/-!
# `fd_ed25519_double_scalar_mul_base` conformance (AVX-512)

The blocks are ref's (`Ref/Proof/Point/fd_ed25519_double_scalar_mul_base.lean`): `^bb0` fills the
slides, `ai[0] = a` precomputed and `a2 = 2a`; `^bb2(k)` fills `ai[1..7]`; `^bb1` zeroes `r`;
`^bb3(i)`–`^bb5` skip leading zero digits; `^bb6`/`^bb7` enter the ladder `^bb8(j)`–`^bb18`;
`^bb19` returns. Here every point is a `u44` QUAD, `partial_dbl` doubles fully and
`add_final_mul`/`_projective` copy, so `r` is always a whole point.
-/

namespace Firedancer.Avx512

-- v4.34: the literal blocks a walk enters are indexed by `Γout` unfolded
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] fd_ed25519_double_scalar_mul_base
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace DoubleScalarMulBase
open Common.DoubleScalarMulBase

attribute [local simp ↓] SSA.simpValuationApply

/-- `^bb0`'s allocas and the base-point table. -/
structure Locals where
  tbl : Pointer
  n1slide : Pointer
  n2slide : Pointer
  ai : Pointer
  a2 : Pointer
  t : Pointer

/-- `^bb0`'s values the tail blocks read. `%k` is `Γout` variable `19 - k`, `%arg0` is 23. -/
structure EntryEnv (V : fd_ed25519_double_scalar_mul_base.Γout.Valuation) (r : Pointer)
    (L : Locals) : Prop where
  c0 : V (⟨19, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 0#32
  c1 : V (⟨18, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 1#32
  c4 : V (⟨15, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 1#64
  c5 : V (⟨14, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value (BitVec.ofInt 64 (-1))
  c6 : V (⟨13, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 0#64
  c7 : V (⟨12, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 8#64
  c8 : V (⟨11, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 255#32
  c9 : V (⟨10, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 16))
    = .value 0#16
  c10 : V (⟨9, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value (BitVec.ofInt 32 (-1))
  c11 : V (⟨8, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 16))
    = .value 1#16
  tbl : V (⟨7, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr) = .value L.tbl
  n1slide : V (⟨6, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr)
    = .value L.n1slide
  n2slide : V (⟨5, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr)
    = .value L.n2slide
  ai : V (⟨4, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr) = .value L.ai
  a2 : V (⟨3, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr) = .value L.a2
  t : V (⟨2, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr) = .value L.t
  n1slide_r : L.n1slide.id ≠ r.id
  n2slide_r : L.n2slide.id ≠ r.id
  ai_r : L.ai.id ≠ r.id
  a2_r : L.a2.id ≠ r.id
  t_r : L.t.id ≠ r.id
  n1slide_t : L.n1slide.id ≠ L.t.id
  n2slide_t : L.n2slide.id ≠ L.t.id
  ai_t : L.ai.id ≠ L.t.id
  a2_t : L.a2.id ≠ L.t.id
  n1slide_ai : L.n1slide.id ≠ L.ai.id
  n2slide_ai : L.n2slide.id ≠ L.ai.id
  a2_ai : L.a2.id ≠ L.ai.id
  r : V (⟨23, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr) = .value r

local notation "v64 " k => (PoisonOr.value (BitVec.ofNat 64 k) : LLVM.IntW 64)
local notation "v32 " k => (PoisonOr.value (BitVec.ofNat 32 k) : LLVM.IntW 32)
local notation "vd " d => (PoisonOr.value d : LLVM.IntW 16)

/-! ## Memory -/

/-- `r`'s block is `s`'s after one `writeQuad` into `r`. -/
def Written (s : GlobalState) (r : Pointer) (u : GlobalState) : Prop :=
  ∃ q : Quad, u.mem.live? r.id = (s.mem.writeQuad r q).live? r.id

/-! ## Points -/

abbrev U44 : Quad → Prop := Ge.QuadU44

/-- A table entry's bounds: `u44`, and `2d·T` within `2p`'s limbs for `sub_with_opts`. -/
abbrev Ent : Quad → Prop := fun q => Ge.QuadU44 q ∧ q.NegBounds 3

/-- `p` holds the QUAD of `P`, within `B`. -/
structure PointAt (m : MemoryState) (p : Pointer) (P : Ed25519.Point) (B : Quad → Prop) :
    Prop where
  ptr : IsQuadPtr m p
  val : (readQuad ptr).toPoint = P
  bnd : B (readQuad ptr)

theorem PointAt.of_readQuad?_eq {m m' : MemoryState} {p : Pointer} {P : Ed25519.Point}
    {B : Quad → Prop} (e : readQuad? p m' = readQuad? p m) (hptr : IsQuadPtr m' p)
    (hp : PointAt m p P B) : PointAt m' p P B :=
  have hq := Ge.readQuad_congr e hp.ptr hptr
  ⟨hptr, hq ▸ hp.val, hq ▸ hp.bnd⟩

theorem PointAt.of_live?_eq {m m' : MemoryState} {p : Pointer} {P : Ed25519.Point}
    {B : Quad → Prop} (h : m'.live? p.id = m.live? p.id) (hp : PointAt m p P B) :
    PointAt m' p P B :=
  hp.of_readQuad?_eq (by simp only [readQuad?, h]) (Ge.isQuadPtr_of_live?_eq h hp.ptr)

theorem PointAt.of_equiv {w s : GlobalState} {m : MemoryState} {p : Pointer} {P : Ed25519.Point}
    {B : Quad → Prop} (he : w ≈ ({ s with mem := m } : GlobalState)) (hp : PointAt m p P B) :
    PointAt w.mem p P B :=
  hp.of_live?_eq (live?_of_equiv_mem' he p.id)

theorem PointAt.mono {m : MemoryState} {p : Pointer} {P : Ed25519.Point} {B B' : Quad → Prop}
    (hp : PointAt m p P B) (hB : ∀ q, B q → B' q) : PointAt m p P B' :=
  ⟨hp.ptr, hp.val, hB _ hp.bnd⟩

theorem PointAt.u44 {m : MemoryState} {p : Pointer} {P : Ed25519.Point} (hp : PointAt m p P Ent) :
    PointAt m p P U44 :=
  hp.mono fun _ h => h.1

/-- A `writeQuad` of `q` into a QUAD pointer leaves `q` there. -/
theorem PointAt.writeQuad {m : MemoryState} {p : Pointer} {q : Quad} {B : Quad → Prop}
    (hp : IsQuadPtr m p) (hB : B q) : PointAt (m.writeQuad p q) p q.toPoint B :=
  have hq := Ge.readQuad_writeQuad hp (PointDbln.isQuadPtr_writeQuad hp q)
  ⟨PointDbln.isQuadPtr_writeQuad hp q, congrArg Quad.toPoint hq, by rw [hq]; exact hB⟩

/-- The 256 digits, `a`'s point. -/
structure Vals where
  w₁ : BitVec 4096
  w₂ : BitVec 4096
  A : Ed25519.Point

/-- `ai + 192k`, entry `k` of a table of QUADs. -/
abbrev aiPtr (ai : Pointer) (k : ℕ) : Pointer := entryPtr 192 ai k

/-- `ai[k]` as `into_precomputed` leaves it: `a`, then `a2 + ai[k - 1]`, precomputed. -/
def aiVal (A : Ed25519.Point) : ℕ → Ed25519.PrecomputedPoint
  | 0 => A.toPrecomputed
  | k + 1 => ((A.dbln 1#32).addPrecomputed (aiVal A k)).toPrecomputed

/-- `ai[0 .. n)` hold `aiVal A`. -/
def Table (m : MemoryState) (ai : Pointer) (A : Ed25519.Point) (n : ℕ) : Prop :=
  ∀ k < n, ∃ P, PointAt m (aiPtr ai k) P Ent ∧ Ed25519.PrecomputedPoint.ofSlots P = aiVal A k

theorem Table.of_live?_eq {m m' : MemoryState} {ai : Pointer} {A : Ed25519.Point} {n : ℕ}
    (h : m'.live? ai.id = m.live? ai.id) (ht : Table m ai A n) : Table m' ai A n :=
  fun k hk => (ht k hk).elim fun P ⟨hp, hv⟩ => ⟨P, hp.of_live?_eq h, hv⟩

theorem Table.of_equiv {w u : GlobalState} {m : MemoryState} {ai : Pointer} {A : Ed25519.Point}
    {n : ℕ} (he : w ≈ ({ u with mem := m } : GlobalState)) (ht : Table m ai A n) :
    Table w.mem ai A n :=
  ht.of_live?_eq (live?_of_equiv_mem' he ai.id)

/-- Entry `k < 8` of a table whose block fits is a QUAD pointer. -/
theorem isQuadPtr_aiPtr {m : MemoryState} {ai : Pointer}
    (h : Fits m ai (8 * (3 * 8 * 64)) ∧ ai.offset.toNat + 8 * (3 * 8 * 8) ≤ 2 ^ 64) {k : ℕ}
    (hk : k < 8) : IsQuadPtr m (aiPtr ai k) := by
  obtain ⟨⟨blk, hblk, hlen⟩, hoff⟩ := h
  have ho : (aiPtr ai k).offset.toNat = ai.offset.toNat + 192 * k :=
    entryPtr_offset_toNat (K := 8) (n := 192) hoff hk
  refine ⟨⟨blk, hblk, ?_⟩, by omega⟩
  simp only [Pointer.offsetInBits, ho] at hlen ⊢
  omega

theorem aiPtr_offsetInBits {ai : Pointer} (hoff : ai.offset.toNat + 8 * (3 * 8 * 8) ≤ 2 ^ 64)
    {k : ℕ} (hk : k < 8) : (aiPtr ai k).offsetInBits = ai.offsetInBits + 1536 * k := by
  simp only [Pointer.offsetInBits, entryPtr_offset_toNat (K := 8) (n := 192) hoff hk]
  omega

/-- `Table` below `k` past a `writeQuad` into entry `k`. -/
theorem Table.writeQuad {m : MemoryState} {ai : Pointer} {A : Ed25519.Point} {k : ℕ} {v : Quad}
    (hoff : ai.offset.toNat + 8 * (3 * 8 * 8) ≤ 2 ^ 64) (hk : k < 8) (ht : Table m ai A k) :
    Table (m.writeQuad (aiPtr ai k) v) ai A k := fun j hj =>
  (ht j hj).elim fun P ⟨hp, hv⟩ =>
    ⟨P, hp.of_readQuad?_eq (Ge.readQuad?_writeQuad_of_le
        (by rw [entryPtr_offset_toNat (K := 8) (n := 192) hoff hk]; omega)
        (by rw [aiPtr_offsetInBits hoff (by omega), aiPtr_offsetInBits hoff hk]
            have : 1536 * j + 1536 ≤ 1536 * k := by omega
            omega))
      ⟨fits_splice (fits_splice (fits_splice hp.ptr.1)), hp.ptr.2⟩, hv⟩

/-- The base-point table as the ladder reads it: below the caller's blocks, apart from `r`, and
`tbl[0 .. 128)` entries holding `Bt` on entry. -/
structure BaseTable (s : GlobalState) (r : Pointer) (L : Locals)
    (Bt : ℕ → Ed25519.PrecomputedPoint) : Prop where
  below : L.tbl.id.id < s.alloc.nextFreeBlock
  ne_r : L.tbl.id ≠ r.id
  pts : ∀ k < 128, ∃ P, PointAt s.mem (aiPtr L.tbl k) P Ent ∧
    Ed25519.PrecomputedPoint.ofSlots P = Bt k

/-! ## Values -/

open Ed25519 in
/-- `r` and `t` after `^bb8`–`^bb11` from `r = R` and digit `d`: `t` is `2R`; a nonzero `d` copies
that into `r` and adds `ai[|d| >> 1]` to `t`, negated for `d < 0`. -/
def addDigit (A R : Point) (d : BitVec 16) : Point × Point :=
  if 0#16 <ₛ d then
    (R.dbl, R.dbl.addPrecomputed (aiVal A (BitVec.setWidth 64 d >>> 1).toNat))
  else if d <ₛ 0#16 then
    (R.dbl, R.dbl.addPrecomputed (aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat).neg)
  else (R, R.dbl)

theorem addDigit_snd (A R : Ed25519.Point) (d : BitVec 16) :
    (addDigit A R d).2 = addSigned R.dbl (aiVal A) d := by
  unfold addDigit addSigned; split_ifs <;> rfl

open Ed25519 in
/-- `t` after `^bb8`–`^bb11`: `2X + d·A`, for `R` representing `X`. -/
theorem addDigit_represents {A R : Point} {X : Edwards.Point curve} (hA : A.WellFormed)
    (hR : R.Represents X) {d : BitVec 16} (hd : d = 0 ∨ d.toInt % 2 = 1) (hb : |d.toInt| ≤ 15) :
    ∃ h : (addDigit A R d).2.WellFormed,
      (addDigit A R d).2.toAffine h = 2 • X + d.toInt • A.toAffine hA := by
  have hR' := hR.wellFormed_fixT
  have e : R.dbl = R.fixT.dbl := Point.dbl_congr rfl rfl rfl
  obtain ⟨h, hv⟩ := addSigned_value (Point.wellFormed_dbl hR')
    (oddMultiples_of_succ hA (E := aiVal A) rfl (fun _ => rfl) 8) hd (by omega)
  rw [addDigit_snd, e]
  exact ⟨h, by rw [hv, Point.toAffine_dbl hR', hR.toAffine_fixT, two_nsmul]⟩

open Ed25519 in
/-- `r` and `t` after `^bb12`–`^bb15` from `r = R`, `t = T` and digit `d`: a nonzero `d` copies
`T` into `r` and adds `B (|d| >> 1)` to `t`, negated for `d < 0`. -/
def addDigitB (B : ℕ → PrecomputedPoint) (R T : Point) (d : BitVec 16) : Point × Point :=
  if 0#16 <ₛ d then (T, T.addPrecomputed (B (BitVec.setWidth 64 d >>> 1).toNat))
  else if d <ₛ 0#16 then (T, T.addPrecomputed (B (BitVec.setWidth 64 (-d) >>> 1).toNat).neg)
  else (R, T)

theorem addDigitB_snd (B : ℕ → Ed25519.PrecomputedPoint) (R T : Ed25519.Point) (d : BitVec 16) :
    (addDigitB B R T d).2 = addSigned T B d := by
  unfold addDigitB addSigned; split_ifs <;> rfl

theorem addDigit_pos {A R : Ed25519.Point} {d : BitVec 16} (h : (0#16 <ₛ d) = true) :
    addDigit A R d = (R.dbl, R.dbl.addPrecomputed (aiVal A (BitVec.setWidth 64 d >>> 1).toNat)) := by
  rw [addDigit, if_pos h]

theorem addDigit_neg {A R : Ed25519.Point} {d : BitVec 16} (h0 : ¬(0#16 <ₛ d) = true)
    (h : (d <ₛ 0#16) = true) :
    addDigit A R d = (R.dbl, R.dbl.addPrecomputed (aiVal A (BitVec.setWidth 64 (-d) >>> 1).toNat).neg) := by
  rw [addDigit, if_neg h0, if_pos h]

theorem addDigit_zero {A R : Ed25519.Point} {d : BitVec 16} (h0 : ¬(0#16 <ₛ d) = true)
    (h : ¬(d <ₛ 0#16) = true) : addDigit A R d = (R, R.dbl) := by
  rw [addDigit, if_neg h0, if_neg h]

theorem addDigitB_pos {B : ℕ → Ed25519.PrecomputedPoint} {R T : Ed25519.Point} {d : BitVec 16}
    (h : (0#16 <ₛ d) = true) :
    addDigitB B R T d = (T, T.addPrecomputed (B (BitVec.setWidth 64 d >>> 1).toNat)) := by
  rw [addDigitB, if_pos h]

theorem addDigitB_neg {B : ℕ → Ed25519.PrecomputedPoint} {R T : Ed25519.Point} {d : BitVec 16}
    (h0 : ¬(0#16 <ₛ d) = true) (h : (d <ₛ 0#16) = true) :
    addDigitB B R T d = (T, T.addPrecomputed (B (BitVec.setWidth 64 (-d) >>> 1).toNat).neg) := by
  rw [addDigitB, if_neg h0, if_pos h]

theorem addDigitB_zero {B : ℕ → Ed25519.PrecomputedPoint} {R T : Ed25519.Point} {d : BitVec 16}
    (h0 : ¬(0#16 <ₛ d) = true) (h : ¬(d <ₛ 0#16) = true) : addDigitB B R T d = (R, T) := by
  rw [addDigitB, if_neg h0, if_neg h]

/-! ## The invariant -/

/-- The state invariant: `r` and `t` QUAD pointers, the digits and `a2` as `^bb0` left them, `t`
and `ai` above the caller's blocks, caller blocks but `r`'s as on entry, `r`'s `Written`. -/
structure Frame (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals) (u : GlobalState) :
    Prop where
  wf : u.WF
  rptr : IsQuadPtr u.mem r
  tptr : IsQuadPtr u.mem L.t
  n1slide : SlidesAt u.mem L.n1slide W.w₁
  n2slide : SlidesAt u.mem L.n2slide W.w₂
  a2 : PointAt u.mem L.a2 (W.A.dbln 1#32) U44
  fresh : s.alloc.nextFreeBlock ≤ L.t.id.id ∧ s.alloc.nextFreeBlock ≤ L.ai.id.id
  aifits : Fits u.mem L.ai (8 * (3 * 8 * 64)) ∧ L.ai.offset.toNat + 8 * (3 * 8 * 8) ≤ 2 ^ 64
  caller : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ r.id → u.mem.live? b = s.mem.live? b
  written : Written s r u

/-- What the return leaves. -/
def Done (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals) (Xf : Edwards.Point Ed25519.curve)
    (rs : HVector toType [SLLVM.Ty.ptr]) (u : GlobalState) : Prop :=
  rs = [.value r]ₕ ∧ Frame s r L W u ∧ ∃ R, PointAt u.mem r R U44 ∧ R.Represents Xf

/-- Block `t`'s run in `u`: `Done` at a return, `P` at the successor. -/
abbrev StepThen (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals)
    (Xf : Edwards.Point Ed25519.curve)
    (V : fd_ed25519_double_scalar_mul_base.Γout.Valuation)
    (P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop)
    (t : SuccArgs fd_ed25519_double_scalar_mul_base.sigs) (u : GlobalState) : Prop :=
  ∃ p u', StateT.run ((fd_ed25519_double_scalar_mul_base.blocks.get t.idx t.hidx).2.denote
      (Ctxt.Valuation.ofHVector t.args.reverse ++ V)) u = .value (p, u')
    ∧ (∀ rs, p.2 = .inl rs → Done s r L W Xf rs u')
    ∧ (∀ t', p.2 = .inr t' → P t' u')

/-- `P` at `t` from every state with the frame, the full table, and `RT` at `r` and `t`. -/
abbrev AtLadder (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals)
    (P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop)
    (RT : Ed25519.Point × Ed25519.Point) (t : SuccArgs fd_ed25519_double_scalar_mul_base.sigs) :
    Prop :=
  ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → PointAt u'.mem r RT.1 U44 →
    PointAt u'.mem L.t RT.2 U44 → P t u'

/-- From `t` in `u`, the run returns with `Done`. -/
abbrev Runs (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals)
    (Xf : Edwards.Point Ed25519.curve)
    (V : fd_ed25519_double_scalar_mul_base.Γout.Valuation)
    (t : SuccArgs fd_ed25519_double_scalar_mul_base.sigs) (u : GlobalState) : Prop :=
  fd_ed25519_double_scalar_mul_base.blocks.Runs V (Done s r L W Xf) t u

section Frames
variable {s u u' : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
  {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation}

theorem live?_writeQuad_of_equiv {p : Pointer} {q : Quad}
    (he : ({ u with mem := u.mem.writeQuad p q } : GlobalState) ≈ u') (b : BlockId)
    (hb : p.id ≠ b) : u'.mem.live? b = u.mem.live? b :=
  (live?_of_equiv_mem' he.symm b).trans (Ge.live?_writeQuad_ne hb)

/-- `Frame` past a `writeQuad` into `r`. -/
theorem Frame.storeR (hu : Frame s r L W u) (hV : EntryEnv V r L) {q : Quad}
    (he : ({ u with mem := u.mem.writeQuad r q } : GlobalState) ≈ u') : Frame s r L W u' :=
  have hl := live?_writeQuad_of_equiv he
  hu.written.elim fun q₀ hw => {
    wf := (Ge.wf_writeQuad hu.wf).of_equiv he
    rptr := Ge.isQuadPtr_of_live?_eq (live?_of_equiv_mem' he.symm r.id) (PointDbln.isQuadPtr_writeQuad hu.rptr q)
    tptr := Ge.isQuadPtr_of_live?_eq (hl _ (Ne.symm hV.t_r)) hu.tptr
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_r))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_r))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_r))
    fresh := hu.fresh
    aifits := ⟨fits_of_live?_eq (hl _ (Ne.symm hV.ai_r)) hu.aifits.1, hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (Ne.symm hbr)).trans (hu.caller b hb hbr)
    written := ⟨q, (live?_of_equiv_mem' he.symm r.id).trans ((Ge.live?_writeQuad_congr q hw).trans
      (Ge.live?_writeQuad_writeQuad q₀ q hu.rptr.2))⟩ }

/-- `Frame` past a call that changed only `t`'s block. -/
theorem Frame.writeT (hu : Frame s r L W u) (hV : EntryEnv V r L) (hwf : u'.WF)
    (ht : IsQuadPtr u'.mem L.t) (hl : ∀ b : BlockId, L.t.id ≠ b → u'.mem.live? b = u.mem.live? b) :
    Frame s r L W u' :=
  have hfresh : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → L.t.id ≠ b := fun b hb h => by
    have := congrArg BlockId.id h; have := hu.fresh.1; omega
  hu.written.elim fun q₀ hw => {
    wf := hwf
    rptr := Ge.isQuadPtr_of_live?_eq (hl _ hV.t_r) hu.rptr
    tptr := ht
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_t))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_t))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_t))
    fresh := hu.fresh
    aifits := ⟨fits_of_live?_eq (hl _ (Ne.symm hV.ai_t)) hu.aifits.1, hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (hfresh b hb)).trans (hu.caller b hb hbr)
    written := ⟨q₀, (hl _ hV.t_r).trans hw⟩ }

/-- `Frame` past a `writeQuad` into `t`. -/
theorem Frame.storeT (hu : Frame s r L W u) (hV : EntryEnv V r L) {q : Quad}
    (he : ({ u with mem := u.mem.writeQuad L.t q } : GlobalState) ≈ u') : Frame s r L W u' :=
  hu.writeT hV ((Ge.wf_writeQuad hu.wf).of_equiv he)
    (Ge.isQuadPtr_of_live?_eq (live?_of_equiv_mem' he.symm _) (PointDbln.isQuadPtr_writeQuad hu.tptr q))
    (live?_writeQuad_of_equiv he)

/-- `Frame` past a `writeQuad` into `ai`'s block. -/
theorem Frame.storeAi (hu : Frame s r L W u) (hV : EntryEnv V r L) {p : Pointer} (hp : p.id = L.ai.id)
    {q : Quad} (he : ({ u with mem := u.mem.writeQuad p q } : GlobalState) ≈ u') :
    Frame s r L W u' :=
  have hl : ∀ b : BlockId, L.ai.id ≠ b → u'.mem.live? b = u.mem.live? b := fun b hb =>
    live?_writeQuad_of_equiv he b (hp ▸ hb)
  have hfresh : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → L.ai.id ≠ b := fun b hb h => by
    have := congrArg BlockId.id h; have := hu.fresh.2; omega
  hu.written.elim fun q₀ hw => {
    wf := (Ge.wf_writeQuad hu.wf).of_equiv he
    rptr := Ge.isQuadPtr_of_live?_eq (hl _ hV.ai_r) hu.rptr
    tptr := Ge.isQuadPtr_of_live?_eq (hl _ hV.ai_t) hu.tptr
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_ai))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_ai))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_ai))
    fresh := hu.fresh
    aifits := ⟨fits_of_live?_eq (live?_of_equiv_mem' he.symm _)
      (fits_splice (fits_splice (fits_splice hu.aifits.1))), hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (hfresh b hb)).trans (hu.caller b hb hbr)
    written := ⟨q₀, (hl _ hV.ai_r).trans hw⟩ }

end Frames

/-! ## The callees -/

section Callees
variable {s u : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
  {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation}

/-- `add_final_mul(r, t)`: `r` becomes `t`'s point. -/
theorem copy_rt (hV : EntryEnv V r L) {T : Ed25519.Point} (hu : Frame s r L W u)
    (hT : PointAt u.mem L.t T U44) :
    ∃ u₁, StateT.run (runFunction (fd_ed25519_point_add_final_mul.denote
        (Ctxt.Valuation.ofHVector [.value L.t, .value r]ₕ))) u = .value ([.value r]ₕ, u₁)
      ∧ Frame s r L W u₁ ∧ (∀ b : BlockId, r.id ≠ b → u₁.mem.live? b = u.mem.live? b)
      ∧ PointAt u₁.mem r T U44 :=
  (fd_ed25519_point_add_final_mul_conforms r L.t u hu.wf (Ne.symm hV.t_r) hu.rptr hT.ptr).elim
    fun u₁ h => ⟨u₁, h.1, hu.storeR hV h.2, live?_writeQuad_of_equiv h.2,
      PointAt.of_equiv h.2.symm (by
        have hw := PointAt.writeQuad (B := U44) hu.rptr hT.bnd
        rwa [hT.val] at hw)⟩

/-- `add_final_mul_projective(r, t)`: `r` becomes `t`'s point. -/
theorem copyProj_rt (hV : EntryEnv V r L) {T : Ed25519.Point} (hu : Frame s r L W u)
    (hT : PointAt u.mem L.t T U44) :
    ∃ u₁, StateT.run (runFunction (fd_ed25519_point_add_final_mul_projective.denote
        (Ctxt.Valuation.ofHVector [.value L.t, .value r]ₕ))) u = .value ([.value r]ₕ, u₁)
      ∧ Frame s r L W u₁ ∧ (∀ b : BlockId, r.id ≠ b → u₁.mem.live? b = u.mem.live? b)
      ∧ PointAt u₁.mem r T U44 :=
  (fd_ed25519_point_add_final_mul_projective_conforms r L.t u hu.wf (Ne.symm hV.t_r) hu.rptr
    hT.ptr).elim
    fun u₁ h => ⟨u₁, h.1, hu.storeR hV h.2, live?_writeQuad_of_equiv h.2,
      PointAt.of_equiv h.2.symm (by
        have hw := PointAt.writeQuad (B := U44) hu.rptr hT.bnd
        rwa [hT.val] at hw)⟩

/-- `partial_dbl(t, r)`: `t` becomes `2R`. -/
theorem dbl_t (hV : EntryEnv V r L) {R : Ed25519.Point} (hu : Frame s r L W u)
    (hR : PointAt u.mem r R U44) :
    ∃ u₁, StateT.run (runFunction (fd_ed25519_partial_dbl.denote
        (Ctxt.Valuation.ofHVector [.value r, .value L.t]ₕ))) u = .value ([.value L.t]ₕ, u₁)
      ∧ Frame s r L W u₁ ∧ (∀ b : BlockId, L.t.id ≠ b → u₁.mem.live? b = u.mem.live? b)
      ∧ PointAt u₁.mem L.t R.dbl U44 :=
  (fd_ed25519_partial_dbl_conforms L.t r u hu.wf hu.tptr hR.ptr hR.bnd.1 hR.bnd.2.1
    hR.bnd.2.2).elim fun u₁ h => h.2.elim fun q h₁ =>
    ⟨u₁, h.1, hu.storeT hV h₁.1, live?_writeQuad_of_equiv h₁.1, PointAt.of_equiv h₁.1.symm (by
      have hw := PointAt.writeQuad (B := U44) hu.tptr h₁.2.2
      rwa [h₁.2.1, hR.val] at hw)⟩

/-- `add_with_opts(t, a, b, 1)`: `t` becomes `a`'s point plus `b`'s entry. -/
theorem addOpts_t (hV : EntryEnv V r L) {R P : Ed25519.Point} {a b : Pointer}
    (hu : Frame s r L W u) (hR : PointAt u.mem a R U44) (hb : PointAt u.mem b P Ent) :
    ∃ u₂, StateT.run (runFunction (fd_ed25519_point_add_with_opts.denote (Ctxt.Valuation.ofHVector
        [.value 1#32, .value b, .value a, .value L.t]ₕ))) u = .value ([.value L.t]ₕ, u₂)
      ∧ Frame s r L W u₂ ∧ (∀ c : BlockId, L.t.id ≠ c → u₂.mem.live? c = u.mem.live? c)
      ∧ PointAt u₂.mem L.t (R.addPrecomputed (Ed25519.PrecomputedPoint.ofSlots P)) U44 :=
  (fd_ed25519_point_add_with_opts_conforms L.t a b 1#32 u hu.wf hu.tptr hR.ptr hb.ptr rfl
    hR.bnd.1 hR.bnd.2.1 hR.bnd.2.2 hb.bnd.1.1 hb.bnd.1.2.1 hb.bnd.1.2.2).elim
    fun u₂ h => h.2.elim fun q h₁ =>
    ⟨u₂, h.1, hu.storeT hV h₁.1, live?_writeQuad_of_equiv h₁.1, PointAt.of_equiv h₁.1.symm (by
      have hw := PointAt.writeQuad (B := U44) hu.tptr h₁.2.2
      rwa [h₁.2.1, hR.val, hb.val] at hw)⟩

/-- `sub_with_opts(t, a, b, 1)`: `addOpts_t` with `b`'s entry negated. -/
theorem subOpts_t (hV : EntryEnv V r L) {R P : Ed25519.Point} {a b : Pointer}
    (hu : Frame s r L W u) (hR : PointAt u.mem a R U44) (hb : PointAt u.mem b P Ent) :
    ∃ u₂, StateT.run (runFunction (fd_ed25519_point_sub_with_opts.denote (Ctxt.Valuation.ofHVector
        [.value 1#32, .value b, .value a, .value L.t]ₕ))) u = .value ([.value L.t]ₕ, u₂)
      ∧ Frame s r L W u₂ ∧ (∀ c : BlockId, L.t.id ≠ c → u₂.mem.live? c = u.mem.live? c)
      ∧ PointAt u₂.mem L.t (R.addPrecomputed (Ed25519.PrecomputedPoint.ofSlots P).neg) U44 :=
  (fd_ed25519_point_sub_with_opts_conforms L.t a b 1#32 u hu.wf hu.tptr hR.ptr hb.ptr rfl
    hR.bnd.1 hR.bnd.2.1 hR.bnd.2.2 hb.bnd.1.1 hb.bnd.1.2.1 hb.bnd.1.2.2 hb.bnd.2).elim
    fun u₂ h => h.2.elim fun q h₁ =>
    ⟨u₂, h.1, hu.storeT hV h₁.1, live?_writeQuad_of_equiv h₁.1, PointAt.of_equiv h₁.1.symm (by
      have hw := PointAt.writeQuad (B := U44) hu.tptr h₁.2.2
      rwa [h₁.2.1, hR.val, hb.val] at hw)⟩

end Callees

/-! ## The blocks -/

section Steps
variable {s : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
  {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} {Xf : Edwards.Point Ed25519.curve}

/-- `^bb1`: `set_zero(r)`, then `br ^bb3(255)`. `P` at the target, `r` representing `0` there. -/
theorem step_bb1 (hV : EntryEnv V r L) {u : GlobalState} (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k3 : ∀ u' R, Frame s r L W u' → Table u'.mem L.ai W.A 8 → PointAt u'.mem r R U44 →
      R.Represents 0 → P ⟨2, rfl, [v32 255]ₕ⟩ u') :
    StepThen s r L W Xf V P ⟨0, rfl, .nil⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  -- `set_zero(r)`
  refine (fd_ed25519_point_set_zero_conforms r u hu.wf hu.rptr).elim fun q h => ?_
  refine h.2.2.2.elim fun u₁ h₁ => ?_
  -- the spec's `Valuation.singleton`, as the `ofHVector` `peel_call` matches by reference
  have hrun₁ : StateT.run (runFunction (fd_ed25519_point_set_zero.denote
      (Ctxt.Valuation.ofHVector [PoisonOr.value r]ₕ))) u = .value ([.value r]ₕ, u₁) := h₁.1
  peel_call hrun₁ with hV.r
  simp_return
  simp [hV.c8]
  have he : ({ u with mem := u.mem.writeQuad r q } : GlobalState) ≈ u₁ :=
    GlobalState.Equiv.trans (show ({ u with mem := u.mem.writeQuad r q } : GlobalState)
      ≈ { u with mem := u.mem.splice r q.BV } from
      ⟨rfl, rfl, fun b => (Ge.live?_splice_BV hu.rptr.2 q b).symm⟩) h₁.2
  have hu₁ := hu.storeR hV he
  have htb₁ := htb.of_live?_eq (live?_writeQuad_of_equiv he _ (Ne.symm hV.ai_r))
  have hR₁ := PointAt.of_equiv he.symm (PointAt.writeQuad (B := U44) hu.rptr h.1)
  have hZ : q.toPoint.Represents 0 := ⟨h.2.2.1, h.2.1.1.trans (by rw [← toAffine_zero]; rfl),
      h.2.1.2.trans (by rw [← toAffine_zero]; rfl)⟩
  exact k3 _ _ hu₁ htb₁ hR₁ hZ

/-- `^bb2`: `add_with_opts(t, a2, ai[k-1], 1); add_final_mul(ai[k], t); into_precomputed(ai[k])`;
`k + 1 = 8` exits to `^bb1`, else `^bb2(k + 1)`, with `ai[k]` filled. -/
theorem step_bb2 (hV : EntryEnv V r L) {u : GlobalState}
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 7) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A k)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k1 : k = 7 → ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → P ⟨0, rfl, .nil⟩ u')
    (k2 : k < 7 → ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A (k + 1) →
      P ⟨1, rfl, [v64 (k + 1)]ₕ⟩ u') :
    StepThen s r L W Xf V P ⟨1, rfl, [v64 k]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  have hoff := hu.aifits.2
  have hk8 : k < 8 := by omega
  refine (htb (k - 1) (by omega)).elim fun Q hQ => ?_
  -- `ai[k - 1]`
  denote_step_reduce v 2 [LLVM.const?] fold
  rw [hV.c5, add_neg_one64 hk1 (by omega)] at hv1
  rw [hV.ai, hV.c5, add_neg_one64 hk1 (by omega), gep_entryPtr, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show k - 1 < 2 ^ 64 by omega)] at hv2
  -- `add_with_opts(t, a2, ai[k - 1], 1)`
  refine (addOpts_t hV hu hu.a2 hQ.1).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.t, hV.a2, hv2, hV.c1
  have hu₁ : Frame s r L W u₁ := h₁.2.1
  have hT₁ := h₁.2.2.2
  rw [hQ.2] at hT₁
  have htb₁ : Table u₁.mem L.ai W.A k := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_t))
  have hai₁ : IsQuadPtr u₁.mem (aiPtr L.ai k) := isQuadPtr_aiPtr hu₁.aifits hk8
  -- `add_final_mul(ai[k], t)`
  denote_step_reduce v 4 [LLVM.const?] fold
  rw [hV.ai, gep_entryPtr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at hv4
  refine (fd_ed25519_point_add_final_mul_conforms (aiPtr L.ai k) L.t u₁ hu₁.wf hV.ai_t hai₁
    hT₁.ptr).elim fun u₂ hc₂ => ?_
  peel_call hc₂.1 with hv4, hV.t
  have hu₂ : Frame s r L W u₂ := hu₁.storeAi hV (entryPtr_id 192 L.ai k) hc₂.2
  have htb₂ : Table u₂.mem L.ai W.A k := (htb₁.writeQuad hoff hk8).of_equiv hc₂.2.symm
  have hK₂ : PointAt u₂.mem (aiPtr L.ai k)
      ((W.A.dbln 1#32).addPrecomputed (aiVal W.A (k - 1))) U44 :=
    PointAt.of_equiv hc₂.2.symm (by
      have hw := PointAt.writeQuad (B := U44) hai₁ hT₁.bnd
      rwa [hT₁.val] at hw)
  -- `into_precomputed(ai[k])`
  refine (fd_curve25519_into_precomputed_conforms (aiPtr L.ai k) u₂ hu₂.wf hK₂.ptr
    (IntoPre.u62_of_u44 hK₂.bnd.1) (IntoPre.u62_of_u44 hK₂.bnd.2.1) (IntoPre.u62_of_u44 hK₂.bnd.2.2)).elim
    fun q h => h.1.elim fun u₃ h₃ => ?_
  -- the spec's `Valuation.singleton`, as the `ofHVector` `peel_call` matches by reference
  have hrun₃ : StateT.run (runFunction (fd_curve25519_into_precomputed.denote
      (Ctxt.Valuation.ofHVector [PoisonOr.value (aiPtr L.ai k)]ₕ))) u₂ = .value ([]ₕ, u₃) := h₃.1
  peel_call hrun₃
  have hu₃ : Frame s r L W u₃ := hu₂.storeAi hV (entryPtr_id 192 L.ai k) h₃.2
  have htb₃ : Table u₃.mem L.ai W.A (k + 1) := fun j hj => by
    by_cases hjk : j < k
    · exact (htb₂.writeQuad hoff hk8).of_equiv h₃.2.symm j hjk
    obtain rfl : j = k := by omega
    refine ⟨_, PointAt.of_equiv h₃.2.symm (PointAt.writeQuad hK₂.ptr
      ⟨⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩), ?_⟩
    rw [h.2.1, hK₂.val]
    obtain ⟨k', rfl⟩ : ∃ k', j = k' + 1 := ⟨j - 1, by omega⟩
    rfl
  -- `k + 1`, `k + 1 == 8`
  denote_step_reduce v 7 [LLVM.const?] fold
  rw [hV.c4, add_one64 (show k + 1 < 2 ^ 63 by omega)] at hv6 hv7
  rw [hV.c7, Common.Wnaf.icmp_eq_ofNat (show k + 1 < 2 ^ 64 by omega) (show 8 < 2 ^ 64 by omega)]
    at hv7
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv7]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  by_cases hk7 : k + 1 = 8
  · rw [if_pos (Common.Wnaf.ofBool_eq_one.mpr hk7)]
    exact k1 (by omega) u₃ hu₃ (hk7 ▸ htb₃)
  · rw [if_neg (mt Common.Wnaf.ofBool_eq_one.mp hk7)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv6]
    exact k2 (by omega) u₃ hu₃ htb₃

end Steps

section Steps
variable {s : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
  {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} {Xf : Edwards.Point Ed25519.curve}

section Loop1

/-- `^bb3`: `n1slide[i] == 0`: `^bb4`, else `^bb6`. `P` at either target, given the branch
taken. -/
theorem step_bb3 (hV : EntryEnv V r L) {u : GlobalState}
    (i : Nat) (hi : i ≤ 255) (hu : Frame s r L W u)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kz : Common.Wnaf.slot W.w₁ i = 0#16 → P ⟨3, rfl, [v32 i, v64 i]ₕ⟩ u)
    (knz : Common.Wnaf.slot W.w₁ i ≠ 0#16 → P ⟨5, rfl, [v32 i]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨2, rfl, [v32 i]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 1 [LLVM.zext, LLVM.zext?]
  rw [setWidth_ofNat (by omega)] at hv1
  denote_step_reduce v 2 [LLVM.const?] fold
  simp only [simp_spine, hV.n1slide, hv1, Common.Wnaf.gep_slot] at hv2
  peel_load_slides hu.n1slide, (show i < 256 by omega), hv2
  denote_step_reduce v 4 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv4
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv4]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  split <;> rename_i hz
  · simp only [Target.denote_mk, HVector.map, simp_spine, hv1]
    exact kz (Common.Wnaf.ofBool_beq_one.mp hz)
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact knz (mt Common.Wnaf.ofBool_beq_one.mpr hz)

/-- `^bb4`: `n2slide[i] == 0`: `^bb5`, else `^bb6`. `P` at either target, given the branch
taken. -/
theorem step_bb4 (hV : EntryEnv V r L) {u : GlobalState}
    (i : Nat) (hi : i ≤ 255) (hu : Frame s r L W u)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kz : Common.Wnaf.slot W.w₂ i = 0#16 → P ⟨4, rfl, [v32 i]ₕ⟩ u)
    (knz : Common.Wnaf.slot W.w₂ i ≠ 0#16 → P ⟨5, rfl, [v32 i]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨3, rfl, [v32 i, v64 i]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 2 [LLVM.const?] fold
  simp only [simp_spine, hV.n2slide, Common.Wnaf.gep_slot] at hv2
  peel_load_slides hu.n2slide, (show i < 256 by omega), hv2
  denote_step_reduce v 4 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv4
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv4]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  split <;> rename_i hz
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact kz (Common.Wnaf.ofBool_beq_one.mp hz)
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact knz (mt Common.Wnaf.ofBool_beq_one.mpr hz)

/-- `^bb5`: `i == 0`: `^bb19`, else `^bb3(i - 1)`. `P` at either target, given the branch taken. -/
theorem step_bb5 (hV : EntryEnv V r L) {u : GlobalState} (i : Nat) (hi : i ≤ 255)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k19 : i = 0 → P ⟨18, rfl, .nil⟩ u) (k3 : 1 ≤ i → P ⟨2, rfl, [v32 (i - 1)]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨4, rfl, [v32 i]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 2 [LLVM.const?] fold
  rw [hV.c10] at hv1
  simp only [hV.c0, Common.Wnaf.icmp_eq_ofNat (show i < 2 ^ 32 by omega) (show 0 < 2 ^ 32 by omega)]
    at hv2
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv2]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  by_cases hi0 : i = 0
  · rw [if_pos (Common.Wnaf.ofBool_eq_one.mpr hi0)]
    exact k19 hi0
  · rw [if_neg (mt Common.Wnaf.ofBool_eq_one.mp hi0)]
    rw [add_neg_one32 (i := i) (by omega) (by omega)] at hv1
    simp only [Target.denote_mk, HVector.map, simp_spine, hv1]
    exact k3 (by omega)

/-- `^bb3` through `^bb4` and `^bb5`: to `^bb6` at a nonzero digit, else to `^bb19` at `i = 0` or
back to `^bb3(i - 1)`, walking on by the matching `stop`. -/
theorem walk_bb3 (hV : EntryEnv V r L) {u : GlobalState}
    (i : Nat) (hi : i ≤ 255) (hu : Frame s r L W u)
    (stop6 : Common.Wnaf.slot W.w₁ i ≠ 0#16 ∨ Common.Wnaf.slot W.w₂ i ≠ 0#16 →
      Runs s r L W Xf V ⟨5, rfl, [v32 i]ₕ⟩ u)
    (stop19 : Common.Wnaf.slot W.w₁ i = 0#16 → Common.Wnaf.slot W.w₂ i = 0#16 → i = 0 →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u)
    (stop3 : Common.Wnaf.slot W.w₁ i = 0#16 → Common.Wnaf.slot W.w₂ i = 0#16 → 1 ≤ i →
      Runs s r L W Xf V ⟨2, rfl, [v32 (i - 1)]ₕ⟩ u) :
    Runs s r L W Xf V ⟨2, rfl, [v32 i]ₕ⟩ u :=
  .step (step_bb3 (P := Runs s r L W Xf V) hV i hi hu
    (fun h₁ => .step (step_bb4 hV i hi hu
      (fun h₂ => .step (step_bb5 hV i hi (stop19 h₁ h₂) (stop3 h₁ h₂)))
      (fun h₂ => stop6 (.inr h₂))))
    (fun h₁ => stop6 (.inl h₁)))

/-- `^bb3(i)` down to `^bb6(i')` at the highest `i' ≤ i` with a nonzero digit, or to `^bb19` if
every digit up to `i` is zero; by induction on `i` over `walk_bb3`. -/
theorem walk_bb3_all (hV : EntryEnv V r L) {u : GlobalState} (hu : Frame s r L W u) :
    ∀ (i : Nat), i ≤ 255 →
    (∀ i' ≤ i, (Common.Wnaf.slot W.w₁ i' ≠ 0#16 ∨ Common.Wnaf.slot W.w₂ i' ≠ 0#16) →
      (∀ k, i' < k → k ≤ i → Common.Wnaf.slot W.w₁ k = 0#16 ∧ Common.Wnaf.slot W.w₂ k = 0#16) →
      Runs s r L W Xf V ⟨5, rfl, [v32 i']ₕ⟩ u) →
    ((∀ k ≤ i, Common.Wnaf.slot W.w₁ k = 0#16 ∧ Common.Wnaf.slot W.w₂ k = 0#16) →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u) →
    Runs s r L W Xf V ⟨2, rfl, [v32 i]ₕ⟩ u
  | 0, hi, stop6, stop19 =>
    walk_bb3 hV 0 hi hu (fun h => stop6 0 le_rfl h fun _ _ _ => by omega)
      (fun h₁ h₂ _ => stop19 fun k hk => by obtain rfl : k = 0 := (by omega); exact ⟨h₁, h₂⟩)
      (fun _ _ h => absurd h (by omega))
  | i + 1, hi, stop6, stop19 =>
    walk_bb3 hV (i + 1) hi hu (fun h => stop6 (i + 1) le_rfl h fun _ _ _ => by omega)
      (fun _ _ h => absurd h (by omega))
      (fun h₁ h₂ _ => walk_bb3_all hV hu i (by omega)
        (fun i' hi' hne hz => stop6 i' (by omega) hne fun k hk hki => by
          by_cases hk1 : k = i + 1
          · subst hk1; exact ⟨h₁, h₂⟩
          · exact hz k hk (by omega))
        (fun hz => stop19 fun k hk => by
          by_cases hk1 : k = i + 1
          · subst hk1; exact ⟨h₁, h₂⟩
          · exact hz k (by omega)))

end Loop1

/-- `^bb6`: `i >s -1`: `^bb7`, else `^bb19`. `P` at either target. -/
theorem step_bb6 (hV : EntryEnv V r L) {u : GlobalState} (i : Nat) (hi : i ≤ 255)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k7 : P ⟨6, rfl, [v32 i]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨5, rfl, [v32 i]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 1 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hV.c10]
  simp [slt_neg_one32 hi, hv1, BlockCom.denote_term, Target.denote]
  exact k7

/-- `^bb7`: `br ^bb8(zext i)`. `P` at the target. -/
theorem step_bb7 (_hV : EntryEnv V r L) {u : GlobalState} (i : Nat) (hi : i ≤ 255)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k8 : P ⟨7, rfl, [v64 i]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨6, rfl, [v32 i]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 1 [LLVM.zext, LLVM.zext?]
  simp_return
  simp only [hv1, setWidth_ofNat (show i < 2 ^ 32 by omega)]
  exact k8

section N1SlidePart

/-- `^bb8`: `partial_dbl(t, r)`; `n1slide[j] >s 0`: `^bb9`, else `^bb10`. `P` at either target,
given the branch taken and the state there. -/
theorem step_bb8 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (R : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kpos : (0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true →
      AtLadder s r L W P (R, R.dbl) ⟨8, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩)
    (knpos : ¬(0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true →
      AtLadder s r L W P (R, R.dbl) ⟨9, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩) :
    StepThen s r L W Xf V P ⟨7, rfl, [v64 j]ₕ⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  -- `partial_dbl(t, r)`
  refine (dbl_t hV hu hR).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.t, hV.r
  have hu₁ : Frame s r L W u₁ := h₁.2.1
  have hR₁ := hR.of_live?_eq (h₁.2.2.1 _ hV.t_r)
  have htb₁ := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_t))
  -- `n1slide[j] >s 0`
  denote_step_reduce v 2 [LLVM.const?] fold
  simp only [simp_spine, hV.n1slide, Common.Wnaf.gep_slot] at hv2
  peel_load_slides hu₁.n1slide, (show j < 256 by omega), hv2
  denote_step_reduce v 4 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv4
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv4]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  split <;> rename_i hb
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact kpos (ofBool_sgt_zero.mp hb) u₁ hu₁ htb₁ hR₁ h₁.2.2.2
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact knpos (mt ofBool_sgt_zero.mpr hb) u₁ hu₁ htb₁ hR₁ h₁.2.2.2

/-- `^bb9`: `add_final_mul(r, t); add_with_opts(t, r, ai[d >> 1], 1)`, then `^bb12` with
`addDigit`'s values. -/
theorem step_bb9 (hV : EntryEnv V r L) (hW : Digits W.w₁ 15#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : (0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true)
    (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t R.dbl U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigit W.A R (Common.Wnaf.slot W.w₁ j)) ⟨11, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨8, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩ u := by
  have hk := idx_pos (hW j (by omega)).1 (hW j (by omega)).2 hb
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₁ j = d at hb hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (copy_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `ai[d >> 1]`
  denote_step_reduce v 5 [LLVM.const?] fold
  simp [hV.c11, hV.ai, LLVM.lshr, LLVM.lshr?, LLVM.zext, LLVM.zext?] at hv5
  replace hv5 := hv5.trans (gep_entryPtr 192 L.ai _)
  have htb₁ := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))
  refine (htb₁ _ hk).elim fun P hP => ?_
  -- `add_with_opts(t, r, ai[d >> 1], 1)`
  refine (addOpts_t hV h₁.2.1 h₁.2.2.2 hP.1).elim fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv5
  simp_return
  exact k _ h₂.2.1 (htb₁.of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigit_pos hb]; exact h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r))
    (by rw [addDigit_pos hb, ← hP.2]; exact h₂.2.2.2)

/-- `^bb10`: `d <s 0`: `^bb11`, else `^bb12` with `addDigit`'s values. -/
theorem step_bb10 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true)
    (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r R U44) (hT : PointAt u.mem L.t R.dbl U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kneg : (Common.Wnaf.slot W.w₁ j <ₛ 0#16) = true →
      AtLadder s r L W P (R, R.dbl) ⟨10, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩)
    (kzero : AtLadder s r L W P (addDigit W.A R (Common.Wnaf.slot W.w₁ j)) ⟨11, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨9, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  generalize Common.Wnaf.slot W.w₁ j = d at hb kneg kzero ⊢
  denote_step_reduce v 2 [LLVM.icmp, LLVM.icmp?, LLVM.icmp', hV.c9]
  by_cases h : d.slt 0#16 <;> simp [h, hv2, BlockCom.denote_term, Target.denote]
  · exact kneg h u hu htb hR hT
  · exact kzero u hu htb (by rw [addDigit_zero hb h]; exact hR)
      (by rw [addDigit_zero hb h]; exact hT)

/-- `^bb11`: `add_final_mul(r, t); sub_with_opts(t, r, ai[-d >> 1], 1)`, then `^bb12` with
`addDigit`'s values. -/
theorem step_bb11 (hV : EntryEnv V r L) (hW : Digits W.w₁ 15#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true)
    (hneg : (Common.Wnaf.slot W.w₁ j <ₛ 0#16) = true)
    (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t R.dbl U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigit W.A R (Common.Wnaf.slot W.w₁ j)) ⟨11, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨10, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩ u := by
  have hk := idx_neg (hW j (by omega)).1 (hW j (by omega)).2 hb
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₁ j = d at hb hneg hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (copy_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `ai[-d >> 1]`
  denote_step_reduce v 6 [LLVM.const?] fold
  simp [hV.c9, hV.c11, hV.ai, LLVM.sub, LLVM.sub?, LLVM.lshr, LLVM.lshr?, LLVM.zext,
    LLVM.zext?] at hv6
  replace hv6 := hv6.trans (gep_entryPtr 192 L.ai _)
  have htb₁ := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))
  refine (htb₁ _ hk).elim fun P hP => ?_
  -- `sub_with_opts(t, r, ai[-d >> 1], 1)`
  refine (subOpts_t hV h₁.2.1 h₁.2.2.2 hP.1).elim fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv6
  simp_return
  exact k _ h₂.2.1 (htb₁.of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigit_neg hb hneg]; exact h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r))
    (by rw [addDigit_neg hb hneg, ← hP.2]; exact h₂.2.2.2)

end N1SlidePart

/-- `^bb8` through `^bb9`, or `^bb10` and `^bb11`, to `^bb12` with `addDigit`'s values, walking on
by `k`. -/
theorem walk_bb8 (hV : EntryEnv V r L) (hW : Digits W.w₁ 15#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (R : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R U44)
    (stop12 : AtLadder s r L W (Runs s r L W Xf V) (addDigit W.A R (Common.Wnaf.slot W.w₁ j))
      ⟨11, rfl, [v64 j]ₕ⟩) :
    Runs s r L W Xf V ⟨7, rfl, [v64 j]ₕ⟩ u :=
  .step (step_bb8 (P := Runs s r L W Xf V) hV j hj R hu htb hR
    (fun hb _ hu' htb' _ hT' => .step (step_bb9 hV hW j hj hb R hu' htb' hT' stop12))
    (fun hb _ hu' htb' hR' hT' => .step (step_bb10 hV j hb R hu' htb' hR' hT'
      (fun hneg _ hu'' htb'' _ hT'' =>
        .step (step_bb11 hV hW j hj hb hneg R hu'' htb'' hT'' stop12))
      stop12)))

section N2SlidePart

/-- `^bb12`: `n2slide[j] >s 0`: `^bb13`, else `^bb14`. `P` at either target, given the branch
taken. -/
theorem step_bb12 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hu : Frame s r L W u)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kpos : (0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true →
      P ⟨12, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u)
    (knpos : ¬(0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true →
      P ⟨13, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨11, rfl, [v64 j]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 1 [LLVM.const?] fold
  simp only [simp_spine, hV.n2slide, Common.Wnaf.gep_slot] at hv1
  peel_load_slides hu.n2slide, (show j < 256 by omega), hv1
  denote_step_reduce v 3 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv3
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv3]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  split <;> rename_i hb
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact kpos (ofBool_sgt_zero.mp hb)
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact knpos (mt ofBool_sgt_zero.mpr hb)

/-- A base-point table entry, in a state that kept the caller's blocks but `r`'s. -/
theorem BaseTable.at {Bt : ℕ → Ed25519.PrecomputedPoint} (hBT : BaseTable s r L Bt)
    {u u₁ : GlobalState} (hu : Frame s r L W u)
    (hl : ∀ b : BlockId, r.id ≠ b → u₁.mem.live? b = u.mem.live? b) {k : ℕ} (hk : k < 128) :
    ∃ P, PointAt u₁.mem (aiPtr L.tbl k) P Ent ∧ Ed25519.PrecomputedPoint.ofSlots P = Bt k :=
  (hBT.pts k hk).elim fun Q hQ =>
    ⟨Q, PointAt.of_live?_eq (m := u.mem) (by rw [entryPtr_id]; exact hl _ (Ne.symm hBT.ne_r))
      (PointAt.of_live?_eq (m := s.mem) (by rw [entryPtr_id]; exact hu.caller _ hBT.below hBT.ne_r)
        hQ.1), hQ.2⟩

/-- `^bb13`: `add_final_mul(r, t); add_with_opts(t, r, tbl[d >> 1], 1)`, then `^bb16` with
`addDigitB`'s values. -/
theorem step_bb13 {Bt : ℕ → Ed25519.PrecomputedPoint} (hV : EntryEnv V r L)
    (hBT : BaseTable s r L Bt) (hW₂ : Digits W.w₂ 255#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : (0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true)
    (R T : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t T U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigitB Bt R T (Common.Wnaf.slot W.w₂ j)) ⟨15, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨12, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u := by
  have hk := idx_pos_tbl (hW₂ j (by omega)).1 (hW₂ j (by omega)).2 hb
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₂ j = d at hb hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (copy_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `tbl[d >> 1]`
  denote_step_reduce v 5 [LLVM.const?] fold
  simp [hV.c11, hV.tbl, LLVM.lshr, LLVM.lshr?, LLVM.zext, LLVM.zext?] at hv5
  replace hv5 := hv5.trans (gep_entryPtr 192 L.tbl _)
  refine (hBT.at hu h₁.2.2.1 hk).elim fun Q hQ => ?_
  -- `add_with_opts(t, r, tbl[d >> 1], 1)`
  refine (addOpts_t hV h₁.2.1 h₁.2.2.2 hQ.1).elim fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv5
  simp_return
  exact k _ h₂.2.1
    ((htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))).of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigitB_pos hb]; exact h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r))
    (by rw [addDigitB_pos hb, ← hQ.2]; exact h₂.2.2.2)

/-- `^bb14`: `d <s 0`: `^bb15`, else `^bb16` with `addDigitB`'s values. -/
theorem step_bb14 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true)
    (R T : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r R U44) (hT : PointAt u.mem L.t T U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kneg : (Common.Wnaf.slot W.w₂ j <ₛ 0#16) = true →
      P ⟨14, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u)
    {Bt : ℕ → Ed25519.PrecomputedPoint}
    (kzero : AtLadder s r L W P (addDigitB Bt R T (Common.Wnaf.slot W.w₂ j))
      ⟨15, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨13, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  generalize Common.Wnaf.slot W.w₂ j = d at hb kneg kzero ⊢
  denote_step_reduce v 2 [LLVM.const?] fold
  simp only [simp_spine, hV.c9] at hv2
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv2]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  split <;> rename_i hneg
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact kneg (ofBool_slt_zero.mp hneg)
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    have h0 := addDigitB_zero (B := Bt) (R := R) (T := T) hb (mt ofBool_slt_zero.mpr hneg)
    exact kzero u hu htb (by rw [h0]; exact hR) (by rw [h0]; exact hT)

/-- `^bb15`: `add_final_mul(r, t); sub_with_opts(t, r, tbl[-d >> 1], 1)`, then `^bb16` with
`addDigitB`'s values. -/
theorem step_bb15 {Bt : ℕ → Ed25519.PrecomputedPoint} (hV : EntryEnv V r L)
    (hBT : BaseTable s r L Bt) (hW₂ : Digits W.w₂ 255#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true)
    (hneg : (Common.Wnaf.slot W.w₂ j <ₛ 0#16) = true)
    (R T : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t T U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigitB Bt R T (Common.Wnaf.slot W.w₂ j)) ⟨15, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨14, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u := by
  have hk := idx_neg_tbl (hW₂ j (by omega)).1 (hW₂ j (by omega)).2 hneg
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₂ j = d at hb hneg hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (copy_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `tbl[-d >> 1]`
  denote_step_reduce v 6 [LLVM.const?] fold
  simp [hV.c9, hV.c11, hV.tbl, LLVM.sub, LLVM.sub?, LLVM.lshr, LLVM.lshr?, LLVM.zext,
    LLVM.zext?] at hv6
  replace hv6 := hv6.trans (gep_entryPtr 192 L.tbl _)
  refine (hBT.at hu h₁.2.2.1 hk).elim fun Q hQ => ?_
  -- `sub_with_opts(t, r, tbl[-d >> 1], 1)`
  refine (subOpts_t hV h₁.2.1 h₁.2.2.2 hQ.1).elim fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv6
  simp_return
  exact k _ h₂.2.1
    ((htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))).of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigitB_neg hb hneg]; exact h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r))
    (by rw [addDigitB_neg hb hneg, ← hQ.2]; exact h₂.2.2.2)

end N2SlidePart

/-- `^bb12` through `^bb13`, or `^bb14` and `^bb15`, to `^bb16` with `addDigitB`'s values, walking
on by `k`. -/
theorem walk_bb12 {Bt : ℕ → Ed25519.PrecomputedPoint} (hV : EntryEnv V r L)
    (hBT : BaseTable s r L Bt) (hW₂ : Digits W.w₂ 255#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (R T : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R U44)
    (hT : PointAt u.mem L.t T U44)
    (stop16 : AtLadder s r L W (Runs s r L W Xf V) (addDigitB Bt R T (Common.Wnaf.slot W.w₂ j))
      ⟨15, rfl, [v64 j]ₕ⟩) :
    Runs s r L W Xf V ⟨11, rfl, [v64 j]ₕ⟩ u :=
  .step (step_bb12 (P := Runs s r L W Xf V) hV j hj hu
    (fun hb => .step (step_bb13 hV hBT hW₂ j hj hb R T hu htb hT stop16))
    (fun hb => .step (step_bb14 hV j hb R T hu htb hR hT
      (fun hneg => .step (step_bb15 hV hBT hW₂ j hj hb hneg R T hu htb hT stop16))
      stop16)))

/-- `^bb16`: `j == 0`: `^bb17`, else `^bb18`. `P` at either target, given the branch taken. -/
theorem step_bb16 (hV : EntryEnv V r L) {u : GlobalState} (j : Nat) (hj : j ≤ 255)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kzero : j = 0 → P ⟨16, rfl, .nil⟩ u) (knz : j ≠ 0 → P ⟨17, rfl, [v64 j]ₕ⟩ u) :
    StepThen s r L W Xf V P ⟨15, rfl, [v64 j]ₕ⟩ u := by
  simp only [StepThen]
  repeat denote_reduce_get
  denote_step_reduce v 1 [LLVM.const?] fold
  simp only [hV.c6, Common.Wnaf.icmp_eq_ofNat (show j < 2 ^ 64 by omega) (show 0 < 2 ^ 64 by omega)]
    at hv1
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv1]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  by_cases hj0 : j = 0
  · rw [if_pos (Common.Wnaf.ofBool_eq_one.mpr hj0)]
    exact kzero hj0
  · rw [if_neg (mt Common.Wnaf.ofBool_eq_one.mp hj0)]
    simp only [Target.denote_mk, HVector.map, simp_spine]
    exact knz hj0

/-- `^bb17`: `add_final_mul(r, t)`, then `^bb19` with `r = T`. -/
theorem step_bb17 (hV : EntryEnv V r L) {u : GlobalState} (T : Ed25519.Point)
    (hu : Frame s r L W u) (hT : PointAt u.mem L.t T U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : ∀ u', Frame s r L W u' → PointAt u'.mem r T U44 → P ⟨18, rfl, .nil⟩ u') :
    StepThen s r L W Xf V P ⟨16, rfl, .nil⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  refine (copy_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  simp_return
  exact k _ h₁.2.1 h₁.2.2.2

/-- `^bb18`: `add_final_mul_projective(r, t)`; `j >s 0`: `^bb8(j - 1)`, else `^bb19`. From
`1 ≤ j` only the first, with `r = T`. -/
theorem step_bb18 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 255) (T : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hT : PointAt u.mem L.t T U44)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → PointAt u'.mem r T U44 →
      P ⟨7, rfl, [v64 (j - 1)]ₕ⟩ u') :
    StepThen s r L W Xf V P ⟨17, rfl, [v64 j]ₕ⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  -- `add_final_mul_projective(r, t)`
  refine (copyProj_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  have htb₁ := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))
  -- `j - 1`, `j >s 0`
  denote_step_reduce v 3 [LLVM.const?] fold
  rw [hV.c5, add_neg_one64 hj1 (by omega)] at hv2
  simp only [hV.c6, icmp_sgt_zero64 hj1 (show j < 2 ^ 63 by omega)] at hv3
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv3]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  rw [if_pos (by decide)]
  simp only [Target.denote_mk, HVector.map, simp_spine, hv2]
  exact k u₁ h₁.2.1 htb₁ h₁.2.2.2

/-- `^bb16` through `^bb17` to `^bb19`, or through `^bb18` back to `^bb8(j - 1)`, walking on by
`stop19` or `stop8`. -/
theorem walk_bb16 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (T : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hT : PointAt u.mem L.t T U44)
    (stop19 : j = 0 → ∀ u', Frame s r L W u' → PointAt u'.mem r T U44 →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u')
    (stop8 : 1 ≤ j → ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 →
      PointAt u'.mem r T U44 → Runs s r L W Xf V ⟨7, rfl, [v64 (j - 1)]ₕ⟩ u') :
    Runs s r L W Xf V ⟨15, rfl, [v64 j]ₕ⟩ u :=
  .step (step_bb16 (P := Runs s r L W Xf V) hV j hj
    (fun hj0 => .step (step_bb17 hV T hu hT (stop19 hj0)))
    (fun hj0 => .step (step_bb18 hV j (by omega) hj T hu htb hT (stop8 (by omega)))))

/-- One ladder iteration: from `^bb8(j)` with `r` representing `X`, to `^bb19` or `^bb8(j - 1)` with
`r` representing `ladderStep`. -/
theorem walk_iter {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point} (hV : EntryEnv V r L)
    (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255) (hBT : BaseTable s r L Bt)
    (hA : W.A.WellFormed) (hG : G.WellFormed) (hB : BaseVals Bt G hG)
    {u : GlobalState} (j : Nat) (hj : j ≤ 255) (R : Ed25519.Point) {X : Edwards.Point Ed25519.curve}
    (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R U44)
    (hX : R.Represents X)
    (stop19 : j = 0 → ∀ u' R', Frame s r L W u' → PointAt u'.mem r R' U44 →
      R'.Represents (ladderStep (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j) →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u')
    (stop8 : 1 ≤ j → ∀ u' R', Frame s r L W u' → Table u'.mem L.ai W.A 8 →
      PointAt u'.mem r R' U44 →
      R'.Represents (ladderStep (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j) →
      Runs s r L W Xf V ⟨7, rfl, [v64 (j - 1)]ₕ⟩ u') :
    Runs s r L W Xf V ⟨7, rfl, [v64 j]ₕ⟩ u := by
  have hd₁ := hD₁ j (by omega)
  have hd₂ := hD₂ j (by omega)
  obtain ⟨hT₁, hv₁⟩ := addDigit_represents hA hX hd₁.1 hd₁.2
  obtain ⟨hT₂, hv₂⟩ := addSigned_value hT₁ (BaseVals.oddMultiples hB) hd₂.1 (lt_of_le_of_lt hd₂.2 (by norm_num))
  have hX₂ : (addDigitB Bt (addDigit W.A R (Common.Wnaf.slot W.w₁ j)).1
      (addDigit W.A R (Common.Wnaf.slot W.w₁ j)).2 (Common.Wnaf.slot W.w₂ j)).2.Represents
      (ladderStep (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j) := by
    rw [addDigitB_snd, ladderStep, ← hv₁, ← hv₂]
    exact Ed25519.Point.represents_toAffine hT₂
  exact walk_bb8 hV hD₁.digits15 j hj R hu htb hR fun _ hu₁ htb₁ hR₁ hT₁' =>
    walk_bb12 hV hBT hD₂.digits255 j hj _ _ hu₁ htb₁ hR₁ hT₁' fun _ hu₂ htb₂ _ hT₂' =>
    walk_bb16 hV j hj _ hu₂ htb₂ hT₂'
      (fun hj0 u₃ hu₃ hR₃ => stop19 hj0 u₃ _ hu₃ hR₃ hX₂)
      (fun hj1 u₃ hu₃ htb₃ hR₃ => stop8 hj1 u₃ _ hu₃ htb₃ hR₃ hX₂)

/-- `^bb8(j)` through every remaining ladder iteration to `^bb19`, `r` representing the ladder's
value `Xf`; by induction on `j` over `walk_iter`. -/
theorem walk_bb8_all {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point}
    (hV : EntryEnv V r L) (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255)
    (hBT : BaseTable s r L Bt) (hA : W.A.WellFormed) (hG : G.WellFormed)
    (hB : BaseVals Bt G hG)
    (stop19 : ∀ u' R', Frame s r L W u' → PointAt u'.mem r R' U44 → R'.Represents Xf →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u') :
    ∀ (j : Nat), j ≤ 255 → ∀ (u : GlobalState) (R : Ed25519.Point)
      (X : Edwards.Point Ed25519.curve),
      ladder (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j = Xf → Frame s r L W u →
      Table u.mem L.ai W.A 8 → PointAt u.mem r R U44 → R.Represents X →
      Runs s r L W Xf V ⟨7, rfl, [v64 j]ₕ⟩ u
  | 0, hj, _, R, X, hXf, hu, htb, hR, hX =>
    walk_iter hV hD₁ hD₂ hBT hA hG hB 0 hj R hu htb hR hX
      (fun _ u' R' hu' hR' hX' => stop19 u' R' hu' hR' (by rwa [← hXf, ladder_zero]))
      (fun hj1 => absurd hj1 (by omega))
  | j + 1, hj, _, R, X, hXf, hu, htb, hR, hX =>
    walk_iter hV hD₁ hD₂ hBT hA hG hB (j + 1) hj R hu htb hR hX
      (fun hj0 => absurd hj0 (by omega))
      (fun _ u' R' hu' htb' hR' hX' =>
        walk_bb8_all hV hD₁ hD₂ hBT hA hG hB stop19 j (by omega) u' R' _
          (by rw [← hXf, ladder_succ]) hu' htb' hR' hX')

/-- `^bb3(255)` through the leading-zero skip, `^bb6`, `^bb7` and the ladder to `^bb19`, `r`
representing the ladder's value. -/
theorem walk_loops {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point}
    (hV : EntryEnv V r L) (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255)
    (hBT : BaseTable s r L Bt) (hA : W.A.WellFormed) (hG : G.WellFormed)
    (hB : BaseVals Bt G hG) (hXf : ladder (W.A.toAffine hA) (G.toAffine hG) 0 W.w₁ W.w₂ 255 = Xf)
    (stop19 : ∀ u' R', Frame s r L W u' → PointAt u'.mem r R' U44 → R'.Represents Xf →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u')
    {u : GlobalState} (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r R U44) (h0 : R.Represents 0) :
    Runs s r L W Xf V ⟨2, rfl, [v32 255]ₕ⟩ u :=
  walk_bb3_all hV hu 255 le_rfl
    (fun i' hi' _ hz => .step (step_bb6 (P := Runs s r L W Xf V) hV i' hi'
      (.step (step_bb7 hV i' hi'
        (walk_bb8_all hV hD₁ hD₂ hBT hA hG hB stop19 i' hi' u R 0
          ((ladder_skip (by omega) hz).trans hXf) hu htb hR h0)))))
    (fun hz => stop19 u R hu hR (by rw [← hXf, ladder_all_zero hz]; exact h0))

/-- `^bb19`: Lifetime ends, `return r`. -/
theorem step_bb19 (hV : EntryEnv V r L) {u : GlobalState} (R : Ed25519.Point)
    (hu : Frame s r L W u) (hR : PointAt u.mem r R U44) (hX : R.Represents Xf)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    : StepThen s r L W Xf V P ⟨18, rfl, .nil⟩ u := by
  simp only [StepThen, Done]
  denote_reduce_get
  iterate 5 peel_lifetime
  simp_return
  simp only [hV.r, true_and]
  exact ⟨hu, R, hR, hX⟩

/-- `^bb2(k)` through the rest of the table loop to `^bb1`, the table full, running on by `stop1`;
by induction on `8 - k`. -/
theorem walk_bb2_all (hV : EntryEnv V r L)
    (stop1 : ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → Runs s r L W Xf V ⟨0, rfl, .nil⟩ u')
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 7) {u : GlobalState}
    (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A k) :
    Runs s r L W Xf V ⟨1, rfl, [v64 k]ₕ⟩ u :=
  .step (step_bb2 (P := Runs s r L W Xf V) hV k hk1 hk hu htb
    (fun _ u' hu' htb' => stop1 u' hu' htb')
    (fun _ _ hu' htb' => walk_bb2_all hV stop1 (k + 1) (by omega) (by omega) hu' htb'))
termination_by 8 - k

/-- From `^bb2(k)` to the return: the table loop, `^bb1`, both loops and `^bb19`. -/
theorem walk_bb2 {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point}
    (hV : EntryEnv V r L) (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255)
    (hBT : BaseTable s r L Bt) (hA : W.A.WellFormed) (hG : G.WellFormed)
    (hB : BaseVals Bt G hG) (hXf : ladder (W.A.toAffine hA) (G.toAffine hG) 0 W.w₁ W.w₂ 255 = Xf)
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 7) {u : GlobalState}
    (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A k) :
    Runs s r L W Xf V ⟨1, rfl, [v64 k]ₕ⟩ u :=
  walk_bb2_all hV
    (fun _ hu' htb' => .step (step_bb1 (P := Runs s r L W Xf V) hV hu' htb'
      fun _ R hu₁ htb₁ hR₁ h0 =>
      walk_loops hV hD₁ hD₂ hBT hA hG hB hXf
        (fun _ R' hu₂ hR₂ hX₂ => .step (step_bb19 hV R' hu₂ hR₂ hX₂)) R hu₁ htb₁ hR₁ h0))
    k hk1 hk hu htb

end Steps

/-! ## Entering and leaving -/

/-- `^bb0`'s `alloca` widths in bits: `n1slide`, `n2slide`, `ai`, `a2`, `t`. -/
def allocW : Nat → Nat
  | 0 => 256 * 16
  | 1 => 256 * 16
  | 2 => 8 * (3 * 8 * 64)
  | _ => 3 * 8 * 64

/-- The `k`-th `alloca` of `^bb0`. -/
abbrev slot (s : GlobalState) (k : Nat) : Pointer := s.chainPtr allocW k

/-- `^bb0`: `wnaf(n1slide, n1, 4); wnaf(n2slide, n2, 8); set(ai[0], a); dbln(a2, a, 1);
into_precomputed(ai[0])`, then `br ^bb2(1)`. -/
theorem entry_run (r n1 a n2 : Pointer) (s : GlobalState) (hs : s.WF)
    (hr : IsQuadPtr s.mem r) (ha : IsQuadPtr s.mem a)
    (hn1 : IsByteBufPtr s.mem n1) (hn2 : IsByteBufPtr s.mem n2)
    (hua : U44 (readQuad ha)) {g : Pointer} (hg : GlobalPtr s "fd_ed25519_base_point_wnaf_table" g) :
    ∃ (L : Locals) (Vout : fd_ed25519_double_scalar_mul_base.Γout.Valuation) (u : GlobalState),
      StateT.run (fd_ed25519_double_scalar_mul_base.entry.denote
          (Ctxt.Valuation.ofHVector [.value n2, .value a, .value n1, .value r]ₕ)) s
        = .value ((Vout, .inr ⟨1, rfl, [v64 1]ₕ⟩), u)
      ∧ L.tbl = g ∧ EntryEnv Vout r L ∧ ∃ W : Vals, W.A = (readQuad ha).toPoint ∧ Frame s r L W u
        ∧ Table u.mem L.ai W.A 1
        ∧ DigitVals W.w₁ 15 ∧ DigitVals W.w₂ 255
        ∧ Common.digitSum W.w₁ 256 = ((readBuf hn1).toNat % 2 ^ 255 : ℕ)
        ∧ Common.digitSum W.w₂ 256 = ((readBuf hn2).toNat % 2 ^ 255 : ℕ) := by
  denote_step_reduce v 11 [LLVM.const?]
  peel_addressof hg
  -- `%13 … %17`: `n1slide`, `n2slide`, `ai`, `a2`, `t`
  peel_alloca_chain s, allocW, 5
  fold_cells s, allocW, slot, 5
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11
  have hwL : (s.allocaChain allocW 5).WF := GlobalState.WF.allocaChain hs 5
  have fb : FrameBelow s.alloc.nextFreeBlock s (s.allocaChain allocW 5) :=
    FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) 5
  have hslot : ∀ {j k : Nat}, j ≠ k → (slot s j).id ≠ (slot s k).id := fun hjk h => by
    have := congrArg BlockId.id h
    simp only [GlobalState.chainPtr_id] at this
    omega
  have hslot_below : ∀ {k : Nat} {b : BlockId}, b.id < s.alloc.nextFreeBlock →
      (slot s k).id ≠ b := fun hb h => by
    have := congrArg BlockId.id h
    simp only [GlobalState.chainPtr_id] at this
    omega

  -- `wnaf(n1slide, n1, 4)`
  peel_lifetime
  have hn1b := lt_nextFreeBlock_of_fits hs hn1.1
  have hn1L : IsByteBufPtr (s.allocaChain allocW 5).mem n1 :=
    ⟨fits_of_live?_eq (fb n1.id hn1b) hn1.1, hn1.2⟩
  refine (wnaf_run (slot s 0) n1 4#32 15 (s.allocaChain allocW 5) hwL
    ⟨GlobalState.fits_chainPtr (by omega), by simp⟩ hn1L (.inl ⟨rfl, rfl⟩)).elim
    fun u₁ h₁ => h₁.elim fun hrun₁ he₁ => ?_
  peel_call hrun₁

  -- `wnaf(n2slide, n2, 8)`
  obtain ⟨w₁, he₁, hd₁, hsum₁⟩ := he₁
  have hS₁ := (hsum₁ (hslot_below hn1b)).trans
    (congrArg (fun x : BitVec 256 => ((x.toNat % 2 ^ 255 : ℕ) : ℤ))
      (readBuf_of_live?_eq (fb n1.id hn1b) (hp := hn1) (hp' := hn1L)))
  have hl₁ : ∀ b : BlockId, (slot s 0).id ≠ b →
      u₁.mem.live? b = (s.allocaChain allocW 5).mem.live? b := fun b hb =>
    (live?_of_equiv_mem' he₁.symm b).trans (live?_splice_ne (p := slot s 0) hb)
  peel_lifetime
  have hn2b := lt_nextFreeBlock_of_fits hs hn2.1
  have hn2L : IsByteBufPtr u₁.mem n2 :=
    ⟨fits_of_live?_eq ((hl₁ _ (hslot_below hn2b)).trans (fb n2.id hn2b)) hn2.1, hn2.2⟩
  refine (wnaf_run (slot s 1) n2 8#32 255 u₁ (GlobalState.WF.of_equiv hwL.splice he₁)
    ⟨fits_of_live?_eq (hl₁ _ (hslot (by omega))) (GlobalState.fits_chainPtr (by omega)), by simp⟩
    hn2L (.inr ⟨rfl, rfl⟩)).elim fun u₂ h₂ => h₂.elim fun hrun₂ he₂ => ?_
  peel_call hrun₂

  iterate 3 peel_lifetime

  -- `set(ai[0], a)`
  obtain ⟨w₂, he₂, hd₂, hsum₂⟩ := he₂
  have hS₂ := (hsum₂ (hslot_below hn2b)).trans
    (congrArg (fun x : BitVec 256 => ((x.toNat % 2 ^ 255 : ℕ) : ℤ))
      (readBuf_of_live?_eq ((hl₁ _ (hslot_below hn2b)).trans (fb n2.id hn2b)) (hp := hn2) (hp' := hn2L)))
  have hl₂ : ∀ b : BlockId, (slot s 1).id ≠ b → u₂.mem.live? b = u₁.mem.live? b := fun b hb =>
    (live?_of_equiv_mem' he₂.symm b).trans (live?_splice_ne (p := slot s 1) hb)
  have hna : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.1
  have hla₂ : u₂.mem.live? a.id = s.mem.live? a.id :=
    (hl₂ _ (hslot_below hna)).trans ((hl₁ _ (hslot_below hna)).trans (fb a.id hna))
  have ha₂ : IsQuadPtr u₂.mem a := Ge.isQuadPtr_of_live?_eq hla₂ ha
  have hai₂ : IsQuadPtr u₂.mem (slot s 2) :=
    ⟨fits_of_live?_eq ((hl₂ _ (hslot (by omega))).trans (hl₁ _ (hslot (by omega))))
      (Fits.mono (GlobalState.fits_chainPtr (w := allocW) (s := s) (k := 5) (show 2 < 5 by omega))
        (by simp [allocW])), by simp⟩
  have hw₂ : u₂.WF := GlobalState.WF.of_equiv (GlobalState.WF.of_equiv hwL.splice he₁).splice he₂
  refine (fd_ed25519_point_set_conforms (slot s 2) a u₂ hw₂ (hslot_below hna) hai₂ ha₂).elim
    fun u₃ h₃ => ?_
  peel_call h₃.1

  -- `dbln(a2, a, 1)`
  have hl₃ := live?_writeQuad_of_equiv h₃.2
  have hla₃ : u₃.mem.live? a.id = s.mem.live? a.id := (hl₃ _ (hslot_below hna)).trans hla₂
  have ha₃ : IsQuadPtr u₃.mem a := Ge.isQuadPtr_of_live?_eq hla₃ ha
  have hqa₃ : readQuad ha₃ = readQuad ha := readQuad_of_live?_eq hla₃ ha ha₃
  have ha2₃ : IsQuadPtr u₃.mem (slot s 3) :=
    ⟨fits_of_live?_eq ((hl₃ _ (hslot (by omega))).trans ((hl₂ _ (hslot (by omega))).trans
        (hl₁ _ (hslot (by omega))))) (GlobalState.fits_chainPtr (show 3 < 5 by omega)), by simp⟩
  have hw₃ : u₃.WF := (Ge.wf_writeQuad hw₂).of_equiv h₃.2
  refine (fd_ed25519_point_dbln_conforms (slot s 3) a 1#32 u₃ hw₃ ha2₃ ha₃ (by rw [hqa₃]; exact hua)
    (by decide)).elim fun q₄ h₄ => h₄.1.elim fun u₄ he₄ => ?_
  peel_call he₄.1

  -- `into_precomputed(ai[0])`
  have hl₄ := live?_writeQuad_of_equiv he₄.2
  have hw₄ : u₄.WF := (Ge.wf_writeQuad hw₃).of_equiv he₄.2
  have hl₄₂ : u₄.mem.live? (slot s 2).id
      = (u₂.mem.writeQuad (slot s 2) (readQuad ha₂)).live? (slot s 2).id :=
    (hl₄ _ (hslot (by omega))).trans (live?_of_equiv_mem' h₃.2.symm _)
  have hai₄ : IsQuadPtr u₄.mem (slot s 2) :=
    Ge.isQuadPtr_of_live?_eq hl₄₂ (PointDbln.isQuadPtr_writeQuad hai₂ _)
  have hq₄ : readQuad hai₄ = readQuad ha :=
    (readQuad_of_live?_eq hl₄₂ (PointDbln.isQuadPtr_writeQuad hai₂ _) hai₄).trans
      ((Ge.readQuad_writeQuad hai₂ _).trans (readQuad_of_live?_eq hla₂ ha ha₂))
  refine (fd_curve25519_into_precomputed_conforms (slot s 2) u₄ hw₄ hai₄
    (by rw [hq₄]; exact IntoPre.u62_of_u44 hua.1) (by rw [hq₄]; exact IntoPre.u62_of_u44 hua.2.1)
    (by rw [hq₄]; exact IntoPre.u62_of_u44 hua.2.2)).elim fun q₅ h₅ => h₅.1.elim fun u₅ he₅ => ?_
  -- the spec's `Valuation.singleton`, as the `ofHVector` `peel_call` matches by reference
  have hrun₅ : StateT.run (runFunction (fd_curve25519_into_precomputed.denote
      (Ctxt.Valuation.ofHVector [PoisonOr.value (slot s 2)]ₕ))) u₄ = .value ([]ₕ, u₅) := he₅.1
  peel_call hrun₅

  simp_return
  refine ⟨⟨g, (slot s 0), (slot s 1), (slot s 2), (slot s 3), (slot s 4)⟩, rfl, ?_⟩
  constructor

  case left =>
    constructor <;> simp
    all_goals first
      | exact hslot_below (lt_nextFreeBlock_of_fits hs hr.1)
      | exact hslot (by omega)

  case right =>
    have hl₅ := live?_writeQuad_of_equiv he₅.2
    have hbelow : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → u₅.mem.live? b = s.mem.live? b :=
      fun b hb => (hl₅ b (hslot_below hb)).trans ((hl₄ b (hslot_below hb)).trans
        ((hl₃ b (hslot_below hb)).trans ((hl₂ b (hslot_below hb)).trans
          ((hl₁ b (hslot_below hb)).trans (fb b hb)))))
    have hrb : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.1
    have hs₁ : SlidesAt u₅.mem (slot s 0) w₁ :=
      (SlidesAt.splice (m := (s.allocaChain allocW 5).mem)
        ⟨GlobalState.fits_chainPtr (by omega), by simp⟩ w₁).of_live?_eq
        (((hl₅ _ (hslot (by omega))).trans ((hl₄ _ (hslot (by omega))).trans
          ((hl₃ _ (hslot (by omega))).trans (hl₂ _ (hslot (by omega)))))).trans
          (live?_of_equiv_mem' he₁.symm _))
    have hs₂ : SlidesAt u₅.mem (slot s 1) w₂ :=
      (SlidesAt.splice (m := u₁.mem)
        ⟨fits_of_live?_eq (hl₁ _ (hslot (by omega))) (GlobalState.fits_chainPtr (by omega)),
          by simp⟩ w₂).of_live?_eq
        (((hl₅ _ (hslot (by omega))).trans ((hl₄ _ (hslot (by omega))).trans
          (hl₃ _ (hslot (by omega))))).trans (live?_of_equiv_mem' he₂.symm _))
    -- `a2 = dbln 1 a`
    have hA2 : PointAt u₅.mem (slot s 3) ((readQuad ha).toPoint.dbln 1#32) U44 :=
      (PointAt.of_equiv he₄.2.symm (by
        have hw := PointAt.writeQuad (B := U44) ha2₃ h₄.2.2
        rwa [h₄.2.1, hqa₃] at hw)).of_live?_eq (hl₅ _ (hslot (by omega)))
    -- `ai[0]`: `a`'s point precomputed
    have htb : Table u₅.mem (slot s 2) (readQuad ha).toPoint 1 := fun k hk => by
      obtain rfl : k = 0 := by omega
      refine ⟨_, ?_, show _ = (readQuad ha).toPoint.toPrecomputed by rw [h₅.2.1, hq₄]⟩
      rw [aiPtr, entryPtr_zero]
      exact PointAt.of_equiv he₅.2.symm (PointAt.writeQuad hai₄
        ⟨⟨h₅.2.2.1, h₅.2.2.2.1, h₅.2.2.2.2.1⟩, h₅.2.2.2.2.2⟩)
    refine ⟨⟨w₁, w₂, (readQuad ha).toPoint⟩, rfl, (show Frame _ _ _ _ _ from
      { wf := (Ge.wf_writeQuad hw₄).of_equiv he₅.2
        rptr := Ge.isQuadPtr_of_live?_eq (hbelow _ hrb) hr
        tptr := ⟨fits_of_live?_eq ((hl₅ _ (hslot (by omega))).trans
          ((hl₄ _ (hslot (by omega))).trans ((hl₃ _ (hslot (by omega))).trans
            ((hl₂ _ (hslot (by omega))).trans (hl₁ _ (hslot (by omega)))))))
          (GlobalState.fits_chainPtr (show 4 < 5 by omega)), by simp⟩
        n1slide := hs₁
        n2slide := hs₂
        a2 := hA2
        fresh := ⟨by simp, by simp⟩
        aifits := ⟨fits_of_live?_eq (live?_of_equiv_mem' he₅.2.symm _)
          (fits_splice (fits_splice (fits_splice (fits_of_live?_eq hl₄₂
            (fits_splice (fits_splice (fits_splice
              (fits_of_live?_eq ((hl₂ _ (hslot (by omega))).trans (hl₁ _ (hslot (by omega))))
                (GlobalState.fits_chainPtr (show 2 < 5 by omega)))))))))), by simp⟩
        caller := fun b hb _ => hbelow b hb
        written := ⟨readQuad hr, (hbelow _ hrb).trans (Ge.live?_writeQuad_readQuad hr).symm⟩ }),
      htb, hd₁, hd₂, hS₁, hS₂⟩

end DoubleScalarMulBase

open DoubleScalarMulBase Common.DoubleScalarMulBase in
theorem fd_ed25519_double_scalar_mul_base_conforms (r n1 a n2 : Pointer) (s : GlobalState)
    (hs : s.WF) : fd_ed25519_double_scalar_mul_base_spec r n1 a n2 s := by
  simp only [fd_ed25519_double_scalar_mul_base_spec, Cfg.denote]
  intro hr ha hn1 hn2 hAa h03 h14 h25 Bt hTbl hB
  refine run_runFunction' _ ?_
  obtain ⟨g, hg, hgr, hpts⟩ := hTbl
  obtain ⟨L, Vout, u₀, hentry, rfl, hV, W, hWA, hu₀, htb₀, hD₁, hD₂, hS₁, hS₂⟩ :=
    entry_run r n1 a n2 s hs hr ha hn1 hn2 ⟨h03, h14, h25⟩ hg
  have hA : W.A.WellFormed := hWA ▸ hAa
  have hBT : BaseTable s r L Bt :=
    { below := (hpts 0 (by decide)).elim fun h _ => lt_nextFreeBlock_of_fits hs (p := aiPtr L.tbl 0) h.1
      ne_r := hgr
      pts := fun k hk => (hpts k hk).elim fun h ⟨hb, hn, hv⟩ => ⟨_, ⟨h, rfl, hb, hn⟩, hv⟩ }
  obtain ⟨rs, u, hrun, rfl, hF, R, hRu, hRX⟩ :=
    walk_bb2 hV hD₁ hD₂ hBT hA Ed25519.wellFormed_basePoint hB rfl 1 le_rfl (by omega) hu₀ htb₀
  -- `r` holds `(n₁ mod 2^255)·a + (n₂ mod 2^255)·G`
  rw [ladder_digitSum, hS₁, hS₂] at hRX
  obtain ⟨q, hlr⟩ := hF.written
  have hq : readQuad hRu.ptr = q :=
    (readQuad_of_live?_eq hlr (PointDbln.isQuadPtr_writeQuad hr q) hRu.ptr).trans
      (Ge.readQuad_writeQuad hr _)
  refine ⟨u, ?run, q, ?equiv, ?val, ?bnd⟩
  case bnd => exact hq ▸ hRu.bnd
  case val =>
    rw [← hq, hRu.val, ← Ed25519.Point.toAffine_congr hWA hA hAa, ← natCast_zsmul, ← natCast_zsmul]
    exact hRX
  case run =>
    rw [EffectM.run_bind, hentry, PoisonOr.value_bind]
    exact hrun
  case equiv =>
    exact (popFrame_equiv_block hs (lt_nextFreeBlock_of_fits hs hr.1) hF.caller
      (fun b hbr => Ge.live?_writeQuad_ne (Ne.symm hbr)) hlr).symm

end Firedancer.Avx512
