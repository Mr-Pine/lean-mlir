/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_double_scalar_mul_base
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_set
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_curve25519_into_precomputed
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_sub_with_opts
import SSA.Projects.Firedancer.Proof.WriteChain
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_double_scalar_mul_base.Ladder

/-!
# `fd_ed25519_double_scalar_mul_base` conformance (ref)

`^bb0` fills `n1slide`/`n2slide`, sets `ai[0] = a` precomputed and `a2 = 2a`;
`^bb2(k)` fills `ai[1..7]`; `^bb1` zeroes `r`; `^bb3(i)`–`^bb5` skip leading
zero digits; `^bb6`/`^bb7` enter the ladder `^bb8(j)`–`^bb18`; `^bb19` returns.

Each `step_bbK` is block `K` with its successors as continuations (`StepThen`); the `walk_*`
lemmas chain them into `Runs`, looping by induction, from `^bb2(1)` to the return.
-/

namespace Firedancer.Ref

-- v4.34: the literal blocks a walk enters are indexed by `Γout` unfolded
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] fd_ed25519_double_scalar_mul_base
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace DoubleScalarMulBase
open Common.DoubleScalarMulBase

-- Valuation lookups at literal variables (`Var.last` included) in one step, whatever the
-- context's spelling; a dsimproc, so it also rewrites under dependent fields.
attribute [local simp ↓] SSA.simpValuationApply

/-- `^bb0`'s allocas and the base-point table. -/
structure Locals where
  tbl : Pointer
  n1slide : Pointer
  n2slide : Pointer
  ai : Pointer
  a2 : Pointer
  t : Pointer

/-- `^bb0`'s values the tail blocks read. `%k` is `Γout` variable `20 - k`,
`%arg0` is 24. -/
structure EntryEnv (V : fd_ed25519_double_scalar_mul_base.Γout.Valuation) (r : Pointer)
    (L : Locals) : Prop where
  c0 : V (⟨20, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 0#32
  c1 : V (⟨19, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 1#32
  c4 : V (⟨16, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 1#64
  c5 : V (⟨15, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value (BitVec.ofInt 64 (-1))
  c6 : V (⟨14, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 0#64
  c7 : V (⟨13, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 64))
    = .value 8#64
  c8 : V (⟨12, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value 255#32
  c9 : V (⟨11, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 16))
    = .value 0#16
  c10 : V (⟨10, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 32))
    = .value (BitVec.ofInt 32 (-1))
  c11 : V (⟨9, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 16))
    = .value 1#16
  c12 : V (⟨8, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var (SLLVM.Ty.bitvec 16))
    = .value (BitVec.ofInt 16 (-1))
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
  r : V (⟨24, by rfl⟩ : fd_ed25519_double_scalar_mul_base.Γout.Var SLLVM.Ty.ptr) = .value r

/-! ## The invariant -/

local notation "v64 " k => (PoisonOr.value (BitVec.ofNat 64 k) : LLVM.IntW 64)
local notation "v32 " k => (PoisonOr.value (BitVec.ofNat 32 k) : LLVM.IntW 32)
local notation "vd " d => (PoisonOr.value d : LLVM.IntW 16)

/-- `r`'s block is `s`'s after a four-coordinate store at `r`. -/
def Written (s : GlobalState) (r : Pointer) (u : GlobalState) : Prop :=
  ∃ oX oY oZ oT : BitVec (5 * 64),
    u.mem.live? r.id = ((((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT).live? r.id

/-! ### Values -/

/-- A point's `Y, T, Z` coordinates sit `320, 640, 960` bits past `X`. -/
theorem coordBits {m : MemoryState} {p : Pointer} (h : IsPointPtr m p) :
    (p.withOffset 40).offsetInBits = p.offsetInBits + 320
      ∧ (p.withOffset 80).offsetInBits = p.offsetInBits + 640
      ∧ (p.withOffset 120).offsetInBits = p.offsetInBits + 960 := by
  have := h.2
  exact ⟨by simpa using withOffset_offsetInBits (off := 40) (by simp; omega),
    by simpa using withOffset_offsetInBits (off := 80) (by simp; omega),
    by simpa using withOffset_offsetInBits (off := 120) (by simp; omega)⟩

/-- The tight limb bound, per coordinate. -/
abbrev tight : Fin 4 → ℕ := fun _ => 0x8000000000000

/-- The loose limb bound, per coordinate. -/
abbrev loose : Fin 4 → ℕ := fun _ => 0x18000000000000

/-- `r`'s bounds in the ladder: `X, Y, T` tight, `Z` loose (`isCoordPtr` order). -/
abbrev rBnd : Fin 4 → ℕ :=
  ![0x8000000000000, 0x8000000000000, 0x8000000000000, 0x18000000000000]

theorem tight_le_rBnd : ∀ i, tight i ≤ rBnd i := by decide

/-- `p` holds `P`, coordinate `i` within `B i`. -/
structure PointAt (m : MemoryState) (p : Pointer) (P : Ed25519.Point) (B : Fin 4 → ℕ) : Prop where
  ptr : IsPointPtr m p
  val : readPoint ptr = P
  bnd : ∀ i, LimbBounds (isCoordPtr ptr i) (B i)

theorem PointAt.of_live?_eq {m m' : MemoryState} {p : Pointer} {P : Ed25519.Point}
    {B : Fin 4 → ℕ} (h : m'.live? p.id = m.live? p.id) (hp : PointAt m p P B) :
    PointAt m' p P B :=
  have ptr := isPointPtr_of_live?_eq h hp.ptr
  ⟨ptr, (readPoint_of_live?_eq h hp.ptr ptr).trans hp.val,
    fun i => carryBnd (q := p.withOffset (i * (5 * 8))) h (hp.bnd i)⟩

theorem PointAt.of_equiv {w s : GlobalState} {m : MemoryState} {p : Pointer} {P : Ed25519.Point}
    {B : Fin 4 → ℕ} (he : w ≈ ({ s with mem := m } : GlobalState)) (hp : PointAt m p P B) :
    PointAt w.mem p P B :=
  hp.of_live?_eq (live?_of_equiv_mem he p.id)

theorem PointAt.mono {m : MemoryState} {p : Pointer} {P : Ed25519.Point} {B B' : Fin 4 → ℕ}
    (hp : PointAt m p P B) (hB : ∀ i, B i ≤ B' i) : PointAt m p P B' :=
  ⟨hp.ptr, hp.val, fun i j => (hp.bnd i j).trans (hB i)⟩

/-- The values `^bb0` fixes: the digits and `a`'s point. -/
structure Vals where
  w₁ : BitVec 4096
  w₂ : BitVec 4096
  A : Ed25519.Point

/-- `ai + 160k`, entry `k` of the table. -/
abbrev aiPtr (ai : Pointer) (k : ℕ) : Pointer := entryPtr 160 ai k

/-- `ai[0 .. n)` hold `aiVal A`, loose. -/
def Table (m : MemoryState) (ai : Pointer) (A : Ed25519.Point) (n : ℕ) : Prop :=
  ∀ k < n, ∃ P, PointAt m (aiPtr ai k) P loose ∧ Ed25519.PrecomputedPoint.ofSlots P = aiVal A k

theorem Table.of_live?_eq {m m' : MemoryState} {ai : Pointer} {A : Ed25519.Point} {n : ℕ}
    (h : m'.live? ai.id = m.live? ai.id) (ht : Table m ai A n) : Table m' ai A n :=
  fun k hk => (ht k hk).elim fun P ⟨hp, hv⟩ => ⟨P, hp.of_live?_eq h, hv⟩

theorem Table.of_equiv {w u : GlobalState} {m : MemoryState} {ai : Pointer} {A : Ed25519.Point}
    {n : ℕ} (he : w ≈ ({ u with mem := m } : GlobalState)) (ht : Table m ai A n) :
    Table w.mem ai A n :=
  ht.of_live?_eq (live?_of_equiv_mem he ai.id)

/-- Entry `k < 8`'s byte offset in a table that does not wrap. -/
theorem aiPtr_offset_toNat {ai : Pointer} (hoff : ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64)
    {k : ℕ} (hk : k < 8) : (aiPtr ai k).offset.toNat = ai.offset.toNat + 160 * k :=
  entryPtr_offset_toNat (K := 8) hoff hk

/-- Entry `k < 8` of a table whose block fits is a point pointer. -/
theorem isPointPtr_aiPtr {m : MemoryState} {ai : Pointer}
    (h : Fits m ai (8 * (4 * 5 * 64)) ∧ ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64) {k : ℕ}
    (hk : k < 8) : IsPointPtr m (aiPtr ai k) := by
  obtain ⟨⟨blk, hblk, hlen⟩, hoff⟩ := h
  have ho := aiPtr_offset_toNat hoff hk
  refine ⟨⟨blk, hblk, ?_⟩, by omega⟩
  simp only [Pointer.offsetInBits, ho] at hlen ⊢
  omega

/-- A store at entry `k`, up to `120` bytes in, starts past entries below `k`. -/
theorem aiPtr_withOffset_ge {ai : Pointer} (hoff : ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64)
    {k : ℕ} (hk : k < 8) {off : BitVec 64} (ho : off.toNat ≤ 120) :
    ai.offsetInBits + 1280 * k ≤ ((aiPtr ai k).withOffset off).offsetInBits := by
  have hk' := aiPtr_offset_toNat hoff hk
  rw [withOffset_offsetInBits (by omega)]
  simp only [Pointer.offsetInBits, hk']
  omega

theorem aiPtr_ge {ai : Pointer} (hoff : ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64) {k : ℕ}
    (hk : k < 8) : ai.offsetInBits + 1280 * k ≤ (aiPtr ai k).offsetInBits := by
  simp only [Pointer.offsetInBits, aiPtr_offset_toNat hoff hk]
  omega

/-- `PointAt` carried to a memory that reads the same limbs at `p`. -/
theorem PointAt.of_readLimb?_eq {m m' : MemoryState} {p : Pointer} {P : Ed25519.Point}
    {B : Fin 4 → ℕ} (hp : PointAt m p P B) (hptr : IsPointPtr m' p)
    (hl : ∀ (c : Fin 4) (i : Fin 5), readLimb? (p.withOffset (c * (5 * 8))) i m'
      = readLimb? (p.withOffset (c * (5 * 8))) i m) :
    PointAt m' p P B := by
  refine ⟨hptr, ?_, fun c => limbBounds_of_readLimb?_eq (hl c) (hp.bnd c)⟩
  have e : ∀ c : Fin 4, readCoordinate? p c m' = readCoordinate? p c m := fun c => by
    simp only [readCoordinate?, readFieldElem?, hl c]
  rw [← hp.val]
  simp only [readPoint, readPoint?, e]

/-- A limb of entry `j` passes over a store starting at or past entry `k > j`. -/
theorem readLimb?_entry_splice {m : MemoryState} {ai q : Pointer} {j k w : ℕ} {x : BitVec w}
    (hoff : ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64) (hj : j < k) (hk : k ≤ 8)
    (hq : ai.offsetInBits + 1280 * k ≤ q.offsetInBits) (c : Fin 4) (i : Fin 5) :
    readLimb? ((aiPtr ai j).withOffset (c * (5 * 8))) i (m.splice q x)
      = readLimb? ((aiPtr ai j).withOffset (c * (5 * 8))) i m := by
  have hi : i.toNat < 5 := i.isLt
  have hj' := aiPtr_offset_toNat hoff (show j < 8 by omega)
  refine readLimb?_splice_of_disjoint i (.inr (.inr ?_))
  have hc : ((c : BitVec 64) * (5 * 8)).toNat = 40 * c.val := by
    fin_cases c <;> rfl
  rw [withOffset_offsetInBits (by rw [hc]; have := c.isLt; omega)]
  simp only [Pointer.offsetInBits, hj', hc] at hq ⊢
  have := c.isLt
  omega

/-- `Table` below `k` past a store starting at or past entry `k`. -/
theorem Table.splice {m : MemoryState} {ai q : Pointer} {A : Ed25519.Point} {k w : ℕ}
    {x : BitVec w} (hoff : ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64) (hk : k ≤ 8)
    (hq : ai.offsetInBits + 1280 * k ≤ q.offsetInBits) (ht : Table m ai A k) :
    Table (m.splice q x) ai A k := fun j hj =>
  (ht j hj).elim fun P ⟨hp, hv⟩ =>
    ⟨P, hp.of_readLimb?_eq (isPointPtr_splice hp.ptr) (readLimb?_entry_splice hoff hj hk hq), hv⟩

/-- The base-point table as the ladder reads it: below the caller's blocks, apart from `r`, and
`tbl[0 .. 128)` loose points holding `Bt` on entry. -/
structure BaseTable (s : GlobalState) (r : Pointer) (L : Locals)
    (Bt : ℕ → Ed25519.PrecomputedPoint) : Prop where
  below : L.tbl.id.id < s.alloc.nextFreeBlock
  ne_r : L.tbl.id ≠ r.id
  pts : ∀ k < 128, ∃ P, PointAt s.mem (aiPtr L.tbl k) P loose ∧
    Ed25519.PrecomputedPoint.ofSlots P = Bt k

/-! ### Frame and blocks -/

/-- The state invariant: the module's constants apart from what the ladder writes, `r` and `t`
points, the digits and `a2` as `^bb0` left them, `t` and `ai` above the caller's blocks, caller
blocks but `r`'s as on entry, `r`'s `Written`. -/
structure Frame (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals) (u : GlobalState) :
    Prop where
  refwf : u.RefWF [r, L.t, L.ai]
  rptr : IsPointPtr u.mem r
  tptr : IsPointPtr u.mem L.t
  n1slide : SlidesAt u.mem L.n1slide W.w₁
  n2slide : SlidesAt u.mem L.n2slide W.w₂
  a2 : PointAt u.mem L.a2 (W.A.dbln 1#32) tight
  fresh : s.alloc.nextFreeBlock ≤ L.t.id.id ∧ s.alloc.nextFreeBlock ≤ L.ai.id.id
  aifits : Fits u.mem L.ai (8 * (4 * 5 * 64)) ∧ L.ai.offset.toNat + 8 * (4 * 5 * 8) ≤ 2 ^ 64
  caller : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ r.id → u.mem.live? b = s.mem.live? b
  written : Written s r u

/-- What the return leaves. -/
def Done (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals) (Xf : Edwards.Point Ed25519.curve)
    (rs : HVector toType [SLLVM.Ty.ptr]) (u : GlobalState) : Prop :=
  rs = [.value r]ₕ ∧ Frame s r L W u ∧ ∃ R, PointAt u.mem r R tight ∧ R.Represents Xf

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
  ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → PointAt u'.mem r RT.1 rBnd →
    PointAt u'.mem L.t RT.2 loose → P t u'

/-- From `t` in `u`, the run returns with `Done`. -/
abbrev Runs (s : GlobalState) (r : Pointer) (L : Locals) (W : Vals)
    (Xf : Edwards.Point Ed25519.curve)
    (V : fd_ed25519_double_scalar_mul_base.Γout.Valuation)
    (t : SuccArgs fd_ed25519_double_scalar_mul_base.sigs) (u : GlobalState) : Prop :=
  fd_ed25519_double_scalar_mul_base.blocks.Runs V (Done s r L W Xf) t u

/-! ## The blocks -/

/-- Stores at `o + {0, 320, 960, 640}` followed by stores at the same offsets are the latter
alone. -/
theorem spliceBits_absorb4 {n : Nat} (bytes : BitVec n) (o : Nat)
    (x₁ y₁ z₁ v₁ x y z v : BitVec 320) :
    spliceBits (spliceBits (spliceBits (spliceBits (spliceBits (spliceBits (spliceBits
      (spliceBits bytes o x₁) (o + 320) y₁) (o + 960) z₁) (o + 640) v₁) o x) (o + 320) y)
      (o + 960) z) (o + 640) v
    = spliceBits (spliceBits (spliceBits (spliceBits bytes o x) (o + 320) y) (o + 960) z)
      (o + 640) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  split_ifs <;> rfl

/-- `r`'s block after two four-coordinate stores is the block after the second alone. -/
theorem live?_absorb4 {m : MemoryState} {r : Pointer}
    (h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320)
    (h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640)
    (h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960)
    (x₁ y₁ z₁ v₁ x y z v : BitVec (5 * 64)) :
    ((((((((m.splice r x₁).splice (r.withOffset 40) y₁).splice (r.withOffset 120) z₁).splice
      (r.withOffset 80) v₁).splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z).splice (r.withOffset 80) v).live? r.id
    = ((((m.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).splice
      (r.withOffset 80) v).live? r.id := by
  simp only [Dbln.live?_splice_of_id (p := r.withOffset 80) (b := r.id) rfl,
    Dbln.live?_splice_of_id (p := r.withOffset 120) (b := r.id) rfl,
    Dbln.live?_splice_of_id (p := r.withOffset 40) (b := r.id) rfl,
    Dbln.live?_splice_of_id (p := r) (b := r.id) rfl, Option.map_map]
  congr 1
  funext blk
  simp only [Function.comp_apply, h40, h80, h120]
  rw [spliceBits_absorb4]

/-- A four-coordinate store at `r` leaves every other block. -/
theorem live?_store4 {u u' : GlobalState} {r : Pointer} {x y z v : BitVec (5 * 64)}
    (he : ({ u with mem := (((u.mem.splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z).splice (r.withOffset 80) v } : GlobalState) ≈ u')
    (b : BlockId) (hb : r.id ≠ b) : u'.mem.live? b = u.mem.live? b :=
  (live?_of_equiv_mem he.symm b).trans ((live?_splice_ne (p := r.withOffset 80) hb).trans
    ((live?_splice_ne (p := r.withOffset 120) hb).trans
      ((live?_splice_ne (p := r.withOffset 40) hb).trans (live?_splice_ne (p := r) hb))))

/-- `Frame` past a four-coordinate store at `r` (as `set_zero` and `add_final_mul` leave). -/
theorem Frame.store4 {s u u' : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
    {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} (hu : Frame s r L W u)
    (hV : EntryEnv V r L) {x y z v : BitVec (5 * 64)}
    (he : ({ u with mem := (((u.mem.splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z).splice (r.withOffset 80) v } : GlobalState) ≈ u') :
    Frame s r L W u' := by
  have hr := hu.rptr
  obtain ⟨h40, h80, h120⟩ := coordBits hr
  have hl := live?_store4 he
  obtain ⟨a₀, b₀, c₀, d₀, hw⟩ := hu.written
  exact {
    refwf := hu.refwf.untouched ((wf_splice4 hu.refwf.wf).of_equiv he) he.globals.symm
      fun b hb => hl b (Ne.symm (hb r (by simp)))
    rptr := isPointPtr_of_equiv he.symm
      (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr))))
    tptr := isPointPtr_of_live?_eq (hl _ (Ne.symm hV.t_r)) hu.tptr
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_r))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_r))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_r))
    fresh := hu.fresh
    aifits := ⟨fits_of_live?_eq (hl _ (Ne.symm hV.ai_r)) hu.aifits.1, hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (Ne.symm hbr)).trans (hu.caller b hb hbr)
    written := ⟨x, y, z, v, (live?_of_equiv_mem he.symm r.id).trans
      ((live?_splice_congr (p := r.withOffset 80) (live?_splice_congr (p := r.withOffset 120)
        (live?_splice_congr (p := r.withOffset 40) (live?_splice_congr (p := r) hw)))).trans
        (live?_absorb4 h40 h80 h120 _ _ _ _ x y z v))⟩ }

/-- Stores at `o + {0, 320, 960, 640}` followed by stores at `o + {0, 320, 960}` are the latter
over the first's `o + 640` store. -/
theorem spliceBits_absorb3 {n : Nat} (bytes : BitVec n) (o : Nat)
    (x₁ y₁ z₁ v₁ x y z : BitVec 320) :
    spliceBits (spliceBits (spliceBits (spliceBits (spliceBits (spliceBits (spliceBits
      bytes o x₁) (o + 320) y₁) (o + 960) z₁) (o + 640) v₁) o x) (o + 320) y) (o + 960) z
    = spliceBits (spliceBits (spliceBits (spliceBits bytes o x) (o + 320) y) (o + 960) z)
      (o + 640) v₁ := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  by_cases hv : o + 640 ≤ i ∧ i < o + 640 + 320 ∧ i < n
  · rw [if_pos hv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv]
  · rw [if_neg hv]
    split_ifs <;> rfl

/-- `r`'s block after a four-coordinate store and then an `X, Y, Z` store. -/
theorem live?_absorb3 {m : MemoryState} {r : Pointer}
    (h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320)
    (h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640)
    (h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960)
    (x₁ y₁ z₁ v₁ x y z : BitVec (5 * 64)) :
    (((((((m.splice r x₁).splice (r.withOffset 40) y₁).splice (r.withOffset 120) z₁).splice
      (r.withOffset 80) v₁).splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z).live? r.id
    = ((((m.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).splice
      (r.withOffset 80) v₁).live? r.id := by
  simp only [Dbln.live?_splice_of_id (p := r.withOffset 80) (b := r.id) rfl,
    Dbln.live?_splice_of_id (p := r.withOffset 120) (b := r.id) rfl,
    Dbln.live?_splice_of_id (p := r.withOffset 40) (b := r.id) rfl,
    Dbln.live?_splice_of_id (p := r) (b := r.id) rfl, Option.map_map]
  congr 1
  funext blk
  simp only [Function.comp_apply, h40, h80, h120]
  rw [spliceBits_absorb3]

/-- An `X, Y, Z` store at `r` leaves every other block. -/
theorem live?_store3 {u u' : GlobalState} {r : Pointer} {x y z : BitVec (5 * 64)}
    (he : ({ u with mem := (((u.mem.splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z) } : GlobalState) ≈ u')
    (b : BlockId) (hb : r.id ≠ b) : u'.mem.live? b = u.mem.live? b :=
  (live?_of_equiv_mem he.symm b).trans ((live?_splice_ne (p := r.withOffset 120) hb).trans
    ((live?_splice_ne (p := r.withOffset 40) hb).trans (live?_splice_ne (p := r) hb)))

/-- `Frame` past an `X, Y, Z` store at `r` (as `add_final_mul_projective` leaves). -/
theorem Frame.store3 {s u u' : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
    {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} (hu : Frame s r L W u)
    (hV : EntryEnv V r L) {x y z : BitVec (5 * 64)}
    (he : ({ u with mem := (((u.mem.splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z) } : GlobalState) ≈ u') :
    Frame s r L W u' := by
  have hr := hu.rptr
  obtain ⟨h40, h80, h120⟩ := coordBits hr
  have hl := live?_store3 he
  obtain ⟨a₀, b₀, c₀, d₀, hw⟩ := hu.written
  exact {
    refwf := hu.refwf.untouched ((wf_splice3 hu.refwf.wf).of_equiv he) he.globals.symm
      fun b hb => hl b (Ne.symm (hb r (by simp)))
    rptr := isPointPtr_of_equiv he.symm
      (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
    tptr := isPointPtr_of_live?_eq (hl _ (Ne.symm hV.t_r)) hu.tptr
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_r))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_r))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_r))
    fresh := hu.fresh
    aifits := ⟨fits_of_live?_eq (hl _ (Ne.symm hV.ai_r)) hu.aifits.1, hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (Ne.symm hbr)).trans (hu.caller b hb hbr)
    written := ⟨x, y, z, d₀, (live?_of_equiv_mem he.symm r.id).trans
      ((live?_splice_congr (p := r.withOffset 120) (live?_splice_congr (p := r.withOffset 40)
        (live?_splice_congr (p := r) hw))).trans
        (live?_absorb3 h40 h80 h120 _ _ _ _ x y z))⟩ }

/-- `Frame` past a call that changed only `t`'s block. -/
theorem Frame.writeT {s u u' : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
    {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} (hu : Frame s r L W u)
    (hV : EntryEnv V r L) (hwf : u'.WF) (hg : u'.globals = u.globals)
    (ht : IsPointPtr u'.mem L.t) (hl : ∀ b : BlockId, L.t.id ≠ b → u'.mem.live? b = u.mem.live? b) :
    Frame s r L W u' := by
  have hfresh : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → L.t.id ≠ b := fun b hb h => by
    have := congrArg BlockId.id h; have := hu.fresh.1; omega
  obtain ⟨a₀, b₀, c₀, d₀, hw⟩ := hu.written
  exact {
    refwf := hu.refwf.untouched hwf hg fun b hb => hl b (Ne.symm (hb L.t (by simp)))
    rptr := isPointPtr_of_live?_eq (hl _ hV.t_r) hu.rptr
    tptr := ht
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_t))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_t))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_t))
    fresh := hu.fresh
    aifits := ⟨fits_of_live?_eq (hl _ (Ne.symm hV.ai_t)) hu.aifits.1, hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (hfresh b hb)).trans (hu.caller b hb hbr)
    written := ⟨a₀, b₀, c₀, d₀, (hl _ hV.t_r).trans hw⟩ }

/-- `Frame` past a call that changed only `ai`'s block, the block still fitting. -/
theorem Frame.writeAi {s u u' : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
    {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} (hu : Frame s r L W u)
    (hV : EntryEnv V r L) (hwf : u'.WF) (hg : u'.globals = u.globals)
    (hfits : Fits u'.mem L.ai (8 * (4 * 5 * 64)))
    (hl : ∀ b : BlockId, L.ai.id ≠ b → u'.mem.live? b = u.mem.live? b) :
    Frame s r L W u' := by
  have hfresh : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → L.ai.id ≠ b := fun b hb h => by
    have := congrArg BlockId.id h; have := hu.fresh.2; omega
  obtain ⟨a₀, b₀, c₀, d₀, hw⟩ := hu.written
  exact {
    refwf := hu.refwf.untouched hwf hg fun b hb => hl b (Ne.symm (hb L.ai (by simp)))
    rptr := isPointPtr_of_live?_eq (hl _ hV.ai_r) hu.rptr
    tptr := isPointPtr_of_live?_eq (hl _ hV.ai_t) hu.tptr
    n1slide := hu.n1slide.of_live?_eq (hl _ (Ne.symm hV.n1slide_ai))
    n2slide := hu.n2slide.of_live?_eq (hl _ (Ne.symm hV.n2slide_ai))
    a2 := hu.a2.of_live?_eq (hl _ (Ne.symm hV.a2_ai))
    fresh := hu.fresh
    aifits := ⟨hfits, hu.aifits.2⟩
    caller := fun b hb hbr => (hl b (hfresh b hb)).trans (hu.caller b hb hbr)
    written := ⟨a₀, b₀, c₀, d₀, (hl _ hV.ai_r).trans hw⟩ }

/-- `Frame` past a four-coordinate store at `t`. -/
theorem Frame.storeT {s u u' : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
    {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} (hu : Frame s r L W u)
    (hV : EntryEnv V r L) {x y z v : BitVec (5 * 64)}
    (he : ({ u with mem := (((u.mem.splice L.t x).splice (L.t.withOffset 40) y).splice
      (L.t.withOffset 120) z).splice (L.t.withOffset 80) v } : GlobalState) ≈ u') :
    Frame s r L W u' :=
  hu.writeT hV ((wf_splice4 hu.refwf.wf).of_equiv he) he.globals.symm
    (isPointPtr_of_equiv he.symm
      (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hu.tptr)))))
    (live?_store4 he)

/-- The `Z := 1` flag of `add_with_opts`/`sub_with_opts`, `zext (d == c)`, is nonzero exactly at
`d = c`. -/
theorem zext_icmp_eq_zero (d c : BitVec 16) :
    BitVec.setWidth 32 (BitVec.ofBool (LLVM.icmp' LLVM.IntPred.eq d c)) = 0 ↔ d ≠ c := by
  by_cases h : d = c
  · simp [h, LLVM.icmp']
  · have hb : (d == c) = false := by simpa using h
    simp [LLVM.icmp', hb, h]

/-- The entry `add_with_opts`/`sub_with_opts` adds at flag `zext (d == c)`: `Z := 1` exactly at
`d = c`. -/
theorem flag_if (d c : BitVec 16) (Q : Ed25519.PrecomputedPoint) :
    (if BitVec.setWidth 32 (BitVec.ofBool (LLVM.icmp' LLVM.IntPred.eq d c)) = 0 then Q
      else { Q with Z := 1 }) = (if d = c then { Q with Z := 1 } else Q) := by
  by_cases h : d = c
  · rw [if_neg ((zext_icmp_eq_zero d c).not.mpr (not_not.mpr h)), if_pos h]
  · rw [if_pos ((zext_icmp_eq_zero d c).mpr h), if_neg h]

section Steps
variable {s : GlobalState} {r : Pointer} {L : Locals} {W : Vals}
  {V : fd_ed25519_double_scalar_mul_base.Γout.Valuation} {Xf : Edwards.Point Ed25519.curve}

/-- `add_final_mul(r, t)`: `r` becomes `T` multiplied out, tight; only `r`'s block moves. -/
theorem finalMul_rt (hV : EntryEnv V r L) {u : GlobalState} {T : Ed25519.Point}
    (hu : Frame s r L W u) (hT : PointAt u.mem L.t T loose) :
    ∃ u₁, StateT.run (runFunction (fd_ed25519_point_add_final_mul.denote
        (Ctxt.Valuation.ofHVector [.value L.t, .value r]ₕ))) u = .value ([.value r]ₕ, u₁)
      ∧ Frame s r L W u₁ ∧ (∀ b : BlockId, r.id ≠ b → u₁.mem.live? b = u.mem.live? b)
      ∧ PointAt u₁.mem r T.finalMul tight :=
  (fd_ed25519_point_add_final_mul_conforms r L.t u hu.refwf.wf (Ne.symm hV.t_r) hu.rptr hT.ptr
    (Dbln.coordBounds hT.ptr 0 L.t (coordPtr_zero _) (hT.bnd 0))
    (Dbln.coordBounds hT.ptr 1 _ rfl (hT.bnd 1)) (Dbln.coordBounds hT.ptr 3 _ rfl (hT.bnd 3))
    (Dbln.coordBounds hT.ptr 2 _ rfl (hT.bnd 2))).elim
    fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h₁ => h₁.1.elim fun u₁ hc =>
    ⟨u₁, hc.1, hu.store4 hV hc.2, live?_store4 hc.2,
      PointAt.of_equiv hc.2.symm ⟨_, h₁.2.1.trans (congrArg Ed25519.Point.finalMul hT.val), h₁.2.2⟩⟩

/-- `add_with_opts(t, a, b, f, 1, 1)`: `t` becomes `a`'s `R` plus `b`'s entry, `Z := 1` unless
`f = 0`, loose; only `t`'s block moves. -/
theorem addOpts_t (hV : EntryEnv V r L) {u : GlobalState} {R P : Ed25519.Point} {a b : Pointer}
    (f : BitVec 32) (hu : Frame s r L W u) (hR : PointAt u.mem a R tight)
    (hb : PointAt u.mem b P loose) :
    ∃ u₂, StateT.run (runFunction (fd_ed25519_point_add_with_opts.denote (Ctxt.Valuation.ofHVector
        [.value 1#32, .value 1#32, .value f, .value b, .value a, .value L.t]ₕ))) u
        = .value ([.value L.t]ₕ, u₂)
      ∧ Frame s r L W u₂ ∧ (∀ c : BlockId, L.t.id ≠ c → u₂.mem.live? c = u.mem.live? c)
      ∧ PointAt u₂.mem L.t (R.addPrecomputedPartial
        (if f = 0 then Ed25519.PrecomputedPoint.ofSlots P
          else { Ed25519.PrecomputedPoint.ofSlots P with Z := 1 })) loose :=
  (fd_ed25519_point_add_with_opts_conforms L.t a b f 1#32 1#32 u hu.tptr hR.ptr hb.ptr rfl rfl
    (hu.refwf.mono (by simp)) (hR.bnd 0) (hR.bnd 1) (hR.bnd 2).loose (hR.bnd 3) hb.bnd).elim
    fun u₂ h₂ => h₂.2.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h₃ =>
    ⟨u₂, h₂.1, hu.storeT hV h₃.1, live?_store4 h₃.1,
      PointAt.of_equiv h₃.1.symm ⟨_, h₃.2.1.trans (by rw [hR.val, hb.val]), h₃.2.2⟩⟩

/-- `sub_with_opts(t, a, b, f, 1, 1)`: `addOpts_t` with `b`'s entry negated. -/
theorem subOpts_t (hV : EntryEnv V r L) {u : GlobalState} {R P : Ed25519.Point} {a b : Pointer}
    (f : BitVec 32) (hu : Frame s r L W u) (hR : PointAt u.mem a R tight)
    (hb : PointAt u.mem b P loose) :
    ∃ u₂, StateT.run (runFunction (fd_ed25519_point_sub_with_opts.denote (Ctxt.Valuation.ofHVector
        [.value 1#32, .value 1#32, .value f, .value b, .value a, .value L.t]ₕ))) u
        = .value ([.value L.t]ₕ, u₂)
      ∧ Frame s r L W u₂ ∧ (∀ c : BlockId, L.t.id ≠ c → u₂.mem.live? c = u.mem.live? c)
      ∧ PointAt u₂.mem L.t (R.addPrecomputedPartial
        (if f = 0 then Ed25519.PrecomputedPoint.ofSlots P
          else { Ed25519.PrecomputedPoint.ofSlots P with Z := 1 }).neg) loose :=
  (fd_ed25519_point_sub_with_opts_conforms L.t a b f 1#32 1#32 u hu.tptr hR.ptr hb.ptr rfl rfl
    (hu.refwf.mono (by simp)) (hR.bnd 0) (hR.bnd 1) (hR.bnd 2).loose (hR.bnd 3) hb.bnd).elim
    fun u₂ h₂ => h₂.2.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h₃ =>
    ⟨u₂, h₂.1, hu.storeT hV h₃.1, live?_store4 h₃.1,
      PointAt.of_equiv h₃.1.symm ⟨_, h₃.2.1.trans (by rw [hR.val, hb.val]), h₃.2.2⟩⟩

/-- `^bb1`: `set_zero(r)`, then `br ^bb3(255)`. `P` at the target, `r` zero there. -/
theorem step_bb1 (hV : EntryEnv V r L) {u : GlobalState} (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k3 : ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → PointAt u'.mem r .zero tight →
      P ⟨2, rfl, [v32 255]ₕ⟩ u') :
    StepThen s r L W Xf V P ⟨0, rfl, .nil⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  -- `set_zero(r)`
  refine (fd_ed25519_point_set_zero_conforms r u hu.rptr (hu.refwf.mono (by simp))).elim
    fun u₁ h₁ => h₁.elim fun hrun₁ he₁ => ?_
  -- the spec's `Valuation.singleton`, as the `ofHVector` `peel_call` matches by reference
  have hrun₁' : StateT.run (runFunction (fd_ed25519_point_set_zero.denote
      (Ctxt.Valuation.ofHVector [PoisonOr.value r]ₕ))) u = .value ([.value r]ₕ, u₁) := hrun₁
  peel_call hrun₁' with hV.r

  simp_return
  simp [hV.c8]
  obtain ⟨X, Y, Z, T, he, hval, hbnd⟩ := he₁
  exact k3 _ (hu.store4 hV he) (htb.of_live?_eq (live?_store4 he _ (Ne.symm hV.ai_r)))
    (PointAt.of_equiv he.symm ⟨_, hval, hbnd⟩)

/-- `^bb2`: `add_with_opts(t, a2, ai[k-1], k == 1, 1, 1); add_final_mul(ai[k], t);
into_precomputed(ai[k])`; `k + 1 = 8` exits to `^bb1`, else `^bb2(k + 1)`, with `ai[k]` filled. -/
theorem step_bb2 (hV : EntryEnv V r L) {u : GlobalState}
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 7) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A k)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k1 : k = 7 → ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 → P ⟨0, rfl, .nil⟩ u')
    (k2 : k < 7 → ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A (k + 1) →
      P ⟨1, rfl, [v64 (k + 1)]ₕ⟩ u') :
    StepThen s r L W Xf V P ⟨1, rfl, [v64 k]ₕ⟩ u := by
  simp only [StepThen]
  -- v4.34: the block and its valuation's index are separate `Blocks.get`s; reduce both
  repeat denote_reduce_get
  have hoff := hu.aifits.2
  obtain ⟨Q, hQ, hQv⟩ := htb (k - 1) (by omega)
  -- `ai[k - 1]`, `k == 1`
  denote_step_reduce v 4 [LLVM.const?] fold
  rw [hV.c5, add_neg_one64 hk1 (by omega)] at hv1
  rw [hV.ai, hV.c5, add_neg_one64 hk1 (by omega), gep_entryPtr, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show k - 1 < 2 ^ 64 by omega)] at hv2
  rw [hV.c4, Common.Wnaf.icmp_eq_ofNat (show k < 2 ^ 64 by omega) (show 1 < 2 ^ 64 by omega)]
    at hv3 hv4
  simp only [LLVM.zext, LLVM.zext?, PoisonOr.value_bind] at hv4
  -- `add_with_opts(t, a2, ai[k - 1], k == 1, 1, 1)`
  refine (addOpts_t hV (BitVec.setWidth 32 (BitVec.ofBool (decide (k = 1)))) hu hu.a2 hQ).elim
    fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.t, hV.a2, hv2, hv4, hV.c1
  have hl₁ := h₁.2.2.1
  have hu₁ : Frame s r L W u₁ := h₁.2.1
  have hT₁ : PointAt u₁.mem L.t ((W.A.dbln 1#32).addPrecomputedPartial
      (if k - 1 = 0 then { aiVal W.A (k - 1) with Z := 1 } else aiVal W.A (k - 1))) loose := by
    have h := h₁.2.2.2
    rw [hQv] at h
    by_cases h1 : k = 1
    · rw [if_neg (by simp [h1])] at h; rwa [if_pos (by omega)]
    · rw [if_pos (by simp [h1])] at h; rwa [if_neg (by omega)]
  have htb₁ : Table u₁.mem L.ai W.A k := htb.of_live?_eq (hl₁ _ (Ne.symm hV.ai_t))
  have hai₁ : IsPointPtr u₁.mem (aiPtr L.ai k) := isPointPtr_aiPtr hu₁.aifits (by omega)
  -- `add_final_mul(ai[k], t)`
  denote_step_reduce v 6 [LLVM.const?] fold
  rw [hV.ai, gep_entryPtr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at hv6
  refine (fd_ed25519_point_add_final_mul_conforms (aiPtr L.ai k) L.t u₁ hu₁.refwf.wf hV.ai_t hai₁
    hT₁.ptr (Dbln.coordBounds hT₁.ptr 0 L.t (coordPtr_zero _) (hT₁.bnd 0))
    (Dbln.coordBounds hT₁.ptr 1 _ rfl (hT₁.bnd 1)) (Dbln.coordBounds hT₁.ptr 3 _ rfl (hT₁.bnd 3))
    (Dbln.coordBounds hT₁.ptr 2 _ rfl (hT₁.bnd 2))).elim
    fun x h => h.elim fun y h => h.elim fun z h => h.elim fun v h₃ =>
    h₃.1.elim fun u₂ hc₂ => ?_
  peel_call hc₂.1 with hv6, hV.t
  have hK₂ : PointAt u₂.mem (aiPtr L.ai k) ((W.A.dbln 1#32).addPrecomputedPartial
      (if k - 1 = 0 then { aiVal W.A (k - 1) with Z := 1 } else aiVal W.A (k - 1))).finalMul
      tight :=
    PointAt.of_equiv hc₂.2.symm ⟨_, h₃.2.1.trans (congrArg _ hT₁.val), h₃.2.2⟩
  have hu₂ : Frame s r L W u₂ :=
    hu₁.writeAi hV ((wf_splice4 hu₁.refwf.wf).of_equiv hc₂.2) hc₂.2.globals.symm
      (fits_of_live?_eq (live?_of_equiv_mem hc₂.2.symm _)
        (fits_splice (fits_splice (fits_splice (fits_splice hu₁.aifits.1)))))
      fun b hb => live?_store4 hc₂.2 b (by rw [entryPtr_id]; exact hb)
  have hk8 : k < 8 := by omega
  have ge40 := aiPtr_withOffset_ge hoff hk8 (off := 40) (by decide)
  have ge80 := aiPtr_withOffset_ge hoff hk8 (off := 80) (by decide)
  have ge120 := aiPtr_withOffset_ge hoff hk8 (off := 120) (by decide)
  have htb₂ : Table u₂.mem L.ai W.A k :=
    (Table.splice hoff (by omega) ge80 (Table.splice hoff (by omega) ge120
      (Table.splice hoff (by omega) ge40 (Table.splice hoff (by omega) (aiPtr_ge hoff hk8)
        htb₁)))).of_equiv hc₂.2.symm
  -- `into_precomputed(ai[k])`
  have hrefwf₂ : u₂.RefWF [aiPtr L.ai k] :=
    hu₂.refwf.of_ids fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp; exact ⟨L.ai, by simp, entryPtr_id _ _ _⟩
  refine (fd_curve25519_into_precomputed_conforms (aiPtr L.ai k) u₂ hK₂.ptr hrefwf₂
    (biasBounds_congr (coordPtr_zero _) (hK₂.bnd 0).bias)
    (limbBounds_congr_bound (coordPtr_one _) (hK₂.bnd 1))
    (limbBounds_congr_bound (coordPtr_two _) (hK₂.bnd 2)).loose).elim
    fun u₃ h₄ => h₄.elim fun hrun₄ he₄ => ?_
  -- the spec's `Valuation.singleton`, as the `ofHVector` `peel_call` matches by reference
  have hrun₄' : StateT.run (runFunction (fd_curve25519_into_precomputed.denote
      (Ctxt.Valuation.ofHVector [PoisonOr.value (aiPtr L.ai k)]ₕ))) u₂ = .value ([]ₕ, u₃) := hrun₄
  peel_call hrun₄'
  refine he₄.elim fun eX h => h.elim fun eY h => h.elim fun eT h₅ => ?_
  have hu₃ : Frame s r L W u₃ :=
    hu₂.writeAi hV ((wf_splice3 hu₂.refwf.wf).of_equiv h₅.1) h₅.1.globals.symm
      (fits_of_live?_eq (live?_of_equiv_mem h₅.1.symm _)
        (fits_splice (fits_splice (fits_splice hu₂.aifits.1))))
      fun b hb =>
        have hb' : (aiPtr L.ai k).id ≠ b := by rw [entryPtr_id]; exact hb
        (live?_of_equiv_mem h₅.1.symm b).trans
          ((live?_splice_ne (p := (aiPtr L.ai k).withOffset 80) hb').trans
            ((live?_splice_ne (p := (aiPtr L.ai k).withOffset 40) hb').trans
              (live?_splice_ne (p := aiPtr L.ai k) hb')))
  have hai := hK₂.ptr
  have h40 := (coordBits hai).1
  have h80 := (coordBits hai).2.1
  have h120 := (coordBits hai).2.2
  have htb₃ : Table u₃.mem L.ai W.A (k + 1) := fun j hj => by
    by_cases hjk : j < k
    · exact (Table.splice hoff (by omega) ge80 (Table.splice hoff (by omega) ge40
        (Table.splice hoff (by omega) (aiPtr_ge hoff hk8) htb₂))).of_equiv h₅.1.symm j hjk
    obtain rfl : j = k := by omega
    refine ⟨_, PointAt.of_equiv h₅.1.symm
      ⟨isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hai)), rfl, fun i => ?_⟩,
      h₅.2.1.trans ((congrArg _ hK₂.val).trans ?_)⟩
    · fin_cases i
      · exact limbBounds_congr_bound (coordPtr_zero _).symm h₅.2.2.1
      · exact limbBounds_congr_bound (coordPtr_one _).symm h₅.2.2.2.1
      · exact (limbBounds_congr_bound (coordPtr_two _).symm h₅.2.2.2.2).loose
      · refine limbBounds_of_readLimb? _ (bounds_of_limbs (p := (aiPtr L.ai j).withOffset 120)
          (fun i => ?_) (limbBounds_readLimb? _ (hK₂.bnd 3).loose))
        have hi : i.toNat < 5 := i.isLt
        rw [readLimb?_splice_of_disjoint i (Or.inr (Or.inl (by simp only [h80, h120]; omega))),
          readLimb?_splice_of_disjoint i (Or.inr (Or.inl (by simp only [h40, h120]; omega))),
          readLimb?_splice_of_disjoint i (Or.inr (Or.inl (by simp only [h120]; omega)))]
    · exact (aiVal_succ W.A (j - 1)).symm.trans (congrArg (aiVal W.A) (Nat.sub_add_cancel hk1))
  -- `k + 1`, `k + 1 == 8`
  denote_step_reduce v 9 [LLVM.const?] fold
  rw [hV.c4, add_one64 (show k + 1 < 2 ^ 63 by omega)] at hv8 hv9
  rw [hV.c7, Common.Wnaf.icmp_eq_ofNat (show k + 1 < 2 ^ 64 by omega) (show 8 < 2 ^ 64 by omega)]
    at hv9
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv9]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  by_cases hk7 : k + 1 = 8
  · rw [if_pos (Common.Wnaf.ofBool_eq_one.mpr hk7)]
    exact k1 (by omega) u₃ hu₃ (hk7 ▸ htb₃)
  · rw [if_neg (mt Common.Wnaf.ofBool_eq_one.mp hk7)]
    simp only [Target.denote_mk, HVector.map, simp_spine, hv8]
    exact k2 (by omega) u₃ hu₃ htb₃

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
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R rBnd)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kpos : (0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true →
      AtLadder s r L W P (R, R.partialDbl) ⟨8, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩)
    (knpos : ¬(0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true →
      AtLadder s r L W P (R, R.partialDbl) ⟨9, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩) :
    StepThen s r L W Xf V P ⟨7, rfl, [v64 j]ₕ⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  -- `partial_dbl(t, r)`
  refine (fd_ed25519_partial_dbl_conforms L.t r u hu.refwf.wf hu.tptr hR.ptr
    (biasBounds?_of_limbBounds (Dbln.coordBounds hR.ptr 0 r (coordPtr_zero _) (hR.bnd 0)))
    (Dbln.coordBounds hR.ptr 1 _ rfl (hR.bnd 1)) (Dbln.coordBounds hR.ptr 3 _ rfl (hR.bnd 3))).elim
    fun oT h => h.elim fun oZ h => h.elim fun oY h => h.elim fun oX h₁ =>
    h₁.1.elim fun u₁ hc₁ => ?_
  peel_call hc₁.1 with hV.t, hV.r
  have he₁ := hc₁.2
  have hl₁ : ∀ b : BlockId, L.t.id ≠ b → u₁.mem.live? b = u.mem.live? b := fun b hb =>
    (live?_of_equiv_mem he₁.symm b).trans ((live?_splice_ne (p := L.t) hb).trans
      ((live?_splice_ne (p := L.t.withOffset 40) hb).trans
        ((live?_splice_ne (p := L.t.withOffset 120) hb).trans
          (live?_splice_ne (p := L.t.withOffset 80) hb))))
  have hpt₁ : IsPointPtr ((((u.mem.splice (L.t.withOffset 80) oT).splice (L.t.withOffset 120)
      oZ).splice (L.t.withOffset 40) oY).splice L.t oX) L.t :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hu.tptr)))
  have hu₁ : Frame s r L W u₁ :=
    hu.writeT hV ((wf_splice4 hu.refwf.wf).of_equiv he₁) he₁.globals.symm
      (isPointPtr_of_equiv he₁.symm hpt₁) hl₁
  have hT₁ : PointAt u₁.mem L.t R.partialDbl loose :=
    PointAt.of_equiv he₁.symm ⟨hpt₁, h₁.2.1.trans (congrArg Ed25519.Point.partialDbl hR.val),
      fun i => by
        fin_cases i
        · exact h₁.2.2.1
        · exact h₁.2.2.2.1
        · exact h₁.2.2.2.2.1.loose
        · exact h₁.2.2.2.2.2.loose⟩
  have hR₁ := hR.of_live?_eq (hl₁ _ hV.t_r)
  have htb₁ := htb.of_live?_eq (hl₁ _ (Ne.symm hV.ai_t))
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
    exact kpos (ofBool_sgt_zero.mp hb) u₁ hu₁ htb₁ hR₁ hT₁
  · simp only [Target.denote_mk, HVector.map, simp_spine]
    exact knpos (mt ofBool_sgt_zero.mpr hb) u₁ hu₁ htb₁ hR₁ hT₁

/-- `^bb9`: `add_final_mul(r, t); add_with_opts(t, r, ai[d >> 1], d == 1, 1, 1)`, then `^bb12`
with `addDigit`'s values. -/
theorem step_bb9 (hV : EntryEnv V r L) (hW : Digits W.w₁ 15#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : (0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true)
    (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t R.partialDbl loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigit W.A R (Common.Wnaf.slot W.w₁ j)) ⟨11, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨8, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩ u := by
  have hk := idx_pos (hW j (by omega)).1 (hW j (by omega)).2 hb
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₁ j = d at hb hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (finalMul_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `ai[d >> 1]`, `d == 1`
  denote_step_reduce v 7 [LLVM.const?] fold
  simp [hV.c11, hV.ai, LLVM.lshr, LLVM.lshr?, LLVM.zext, LLVM.zext?, LLVM.icmp, LLVM.icmp?]
    at hv5 hv7
  replace hv5 := hv5.trans (gep_entryPtr 160 L.ai _)
  have htb₁ := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))
  refine (htb₁ _ hk).elim fun P hP => ?_
  -- `add_with_opts(t, r, ai[d >> 1], d == 1, 1, 1)`
  refine (addOpts_t hV (BitVec.setWidth 32 (BitVec.ofBool (LLVM.icmp' LLVM.IntPred.eq d 1#16)))
    h₁.2.1 h₁.2.2.2 hP.1).elim fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv5, hv7
  simp_return
  exact k _ h₂.2.1 (htb₁.of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigit_pos hb]
        exact (h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r)).mono tight_le_rBnd)
    (by rw [addDigit_pos hb, ← hP.2, ← flag_if]; exact h₂.2.2.2)

/-- `^bb10`: `d <s 0`: `^bb11`, else `^bb12` with `addDigit`'s values. -/
theorem step_bb10 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true)
    (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r R rBnd) (hT : PointAt u.mem L.t R.partialDbl loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (kneg : (Common.Wnaf.slot W.w₁ j <ₛ 0#16) = true →
      AtLadder s r L W P (R, R.partialDbl) ⟨10, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩)
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

/-- `^bb11`: `add_final_mul(r, t); sub_with_opts(t, r, ai[-d >> 1], d == -1, 1, 1)`,
then `^bb12` with `addDigit`'s values. -/
theorem step_bb11 (hV : EntryEnv V r L) (hW : Digits W.w₁ 15#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₁ j) = true)
    (hneg : (Common.Wnaf.slot W.w₁ j <ₛ 0#16) = true)
    (R : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t R.partialDbl loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigit W.A R (Common.Wnaf.slot W.w₁ j)) ⟨11, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨10, rfl, [v64 j, vd (Common.Wnaf.slot W.w₁ j)]ₕ⟩ u := by
  have hk := idx_neg (hW j (by omega)).1 (hW j (by omega)).2 hb
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₁ j = d at hb hneg hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (finalMul_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `ai[-d >> 1]`, `d == -1`
  denote_step_reduce v 8 [LLVM.const?] fold
  simp [hV.c9, hV.c11, hV.c12, hV.ai, LLVM.sub, LLVM.sub?, LLVM.lshr, LLVM.lshr?, LLVM.zext,
    LLVM.zext?, LLVM.icmp, LLVM.icmp?] at hv6 hv8
  replace hv6 := hv6.trans (gep_entryPtr 160 L.ai _)
  have htb₁ := htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))
  refine (htb₁ _ hk).elim fun P hP => ?_
  -- `sub_with_opts(t, r, ai[-d >> 1], d == -1, 1, 1)`
  refine (subOpts_t hV
    (BitVec.setWidth 32 (BitVec.ofBool (LLVM.icmp' LLVM.IntPred.eq d 65535#16)))
    h₁.2.1 h₁.2.2.2 hP.1).elim fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv6, hv8
  simp_return
  exact k _ h₂.2.1 (htb₁.of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigit_neg hb hneg]
        exact (h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r)).mono tight_le_rBnd)
    (by rw [addDigit_neg hb hneg, ← hP.2, ← flag_if]; exact h₂.2.2.2)

end N1SlidePart

/-- `^bb8` through `^bb9`, or `^bb10` and `^bb11`, to `^bb12` with `addDigit`'s values, walking on
by `k`. -/
theorem walk_bb8 (hV : EntryEnv V r L) (hW : Digits W.w₁ 15#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (R : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R rBnd)
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

/-- `^bb13`: `add_final_mul(r, t); add_with_opts(t, r, tbl[d >> 1], 1, 1, 1)`, then `^bb16` with
`addDigitB`'s values. -/
theorem step_bb13 {Bt : ℕ → Ed25519.PrecomputedPoint} (hV : EntryEnv V r L)
    (hBT : BaseTable s r L Bt) (hW₂ : Digits W.w₂ 255#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : (0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true)
    (R T : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t T loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigitB Bt R T (Common.Wnaf.slot W.w₂ j)) ⟨15, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨12, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u := by
  have hk := idx_pos_tbl (hW₂ j (by omega)).1 (hW₂ j (by omega)).2 hb
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₂ j = d at hb hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (finalMul_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `tbl[d >> 1]`
  denote_step_reduce v 5 [LLVM.const?] fold
  simp [hV.c11, hV.tbl, LLVM.lshr, LLVM.lshr?, LLVM.zext, LLVM.zext?] at hv5
  replace hv5 := hv5.trans (gep_entryPtr 160 L.tbl _)
  refine (hBT.pts _ hk).elim fun Q hQ => ?_
  -- `add_with_opts(t, r, tbl[d >> 1], 1, 1, 1)`
  refine (addOpts_t hV 1#32 h₁.2.1 h₁.2.2.2
    (PointAt.of_live?_eq (p := aiPtr L.tbl _) (h₁.2.2.1 _ (Ne.symm hBT.ne_r))
      (PointAt.of_live?_eq (p := aiPtr L.tbl _) (hu.caller _ hBT.below hBT.ne_r) hQ.1))).elim
    fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv5
  simp_return
  exact k _ h₂.2.1
    ((htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))).of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigitB_pos hb]
        exact (h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r)).mono tight_le_rBnd)
    (by rw [addDigitB_pos hb, ← hQ.2]; exact h₂.2.2.2)

/-- `^bb14`: `d <s 0`: `^bb15`, else `^bb16` with `addDigitB`'s values. -/
theorem step_bb14 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true)
    (R T : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r R rBnd) (hT : PointAt u.mem L.t T loose)
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

/-- `^bb15`: `add_final_mul(r, t); sub_with_opts(t, r, tbl[-d >> 1], 1, 1, 1)`, then `^bb16` with
`addDigitB`'s values. -/
theorem step_bb15 {Bt : ℕ → Ed25519.PrecomputedPoint} (hV : EntryEnv V r L)
    (hBT : BaseTable s r L Bt) (hW₂ : Digits W.w₂ 255#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (hb : ¬(0#16 <ₛ Common.Wnaf.slot W.w₂ j) = true)
    (hneg : (Common.Wnaf.slot W.w₂ j <ₛ 0#16) = true)
    (R T : Ed25519.Point) (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hT : PointAt u.mem L.t T loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : AtLadder s r L W P (addDigitB Bt R T (Common.Wnaf.slot W.w₂ j)) ⟨15, rfl, [v64 j]ₕ⟩) :
    StepThen s r L W Xf V P ⟨14, rfl, [v64 j, vd (Common.Wnaf.slot W.w₂ j)]ₕ⟩ u := by
  have hk := idx_neg_tbl (hW₂ j (by omega)).1 (hW₂ j (by omega)).2 hneg
  simp only [StepThen]
  generalize Common.Wnaf.slot W.w₂ j = d at hb hneg hk k ⊢
  denote_reduce_get
  -- `add_final_mul(r, t)`
  refine (finalMul_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  -- `tbl[-d >> 1]`
  denote_step_reduce v 6 [LLVM.const?] fold
  simp [hV.c9, hV.c11, hV.tbl, LLVM.sub, LLVM.sub?, LLVM.lshr, LLVM.lshr?, LLVM.zext,
    LLVM.zext?] at hv6
  replace hv6 := hv6.trans (gep_entryPtr 160 L.tbl _)
  refine (hBT.pts _ hk).elim fun Q hQ => ?_
  -- `sub_with_opts(t, r, tbl[-d >> 1], 1, 1, 1)`
  refine (subOpts_t hV 1#32 h₁.2.1 h₁.2.2.2
    (PointAt.of_live?_eq (p := aiPtr L.tbl _) (h₁.2.2.1 _ (Ne.symm hBT.ne_r))
      (PointAt.of_live?_eq (p := aiPtr L.tbl _) (hu.caller _ hBT.below hBT.ne_r) hQ.1))).elim
    fun u₂ h₂ => ?_
  peel_call h₂.1 with hV.t, hV.r, hV.c1, hv6
  simp_return
  exact k _ h₂.2.1
    ((htb.of_live?_eq (h₁.2.2.1 _ (Ne.symm hV.ai_r))).of_live?_eq (h₂.2.2.1 _ (Ne.symm hV.ai_t)))
    (by rw [addDigitB_neg hb hneg]
        exact (h₁.2.2.2.of_live?_eq (h₂.2.2.1 _ hV.t_r)).mono tight_le_rBnd)
    (by rw [addDigitB_neg hb hneg, ← hQ.2]; exact h₂.2.2.2)

end N2SlidePart

/-- `^bb12` through `^bb13`, or `^bb14` and `^bb15`, to `^bb16` with `addDigitB`'s values, walking
on by `k`. -/
theorem walk_bb12 {Bt : ℕ → Ed25519.PrecomputedPoint} (hV : EntryEnv V r L)
    (hBT : BaseTable s r L Bt) (hW₂ : Digits W.w₂ 255#16) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (R T : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R rBnd)
    (hT : PointAt u.mem L.t T loose)
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

/-- `^bb17`: `add_final_mul(r, t)`, then `^bb19` with `r = T` finished. -/
theorem step_bb17 (hV : EntryEnv V r L) {u : GlobalState} (T : Ed25519.Point)
    (hu : Frame s r L W u) (hT : PointAt u.mem L.t T loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : ∀ u', Frame s r L W u' → PointAt u'.mem r T.finalMul tight → P ⟨18, rfl, .nil⟩ u') :
    StepThen s r L W Xf V P ⟨16, rfl, .nil⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  refine (finalMul_rt hV hu hT).elim fun u₁ h₁ => ?_
  peel_call h₁.1 with hV.r, hV.t
  simp_return
  exact k _ h₁.2.1 h₁.2.2.2

/-- `^bb18`: `add_final_mul_projective(r, t)`; `j >s 0`: `^bb8(j - 1)`, else `^bb19`. From
`1 ≤ j` only the first, with `r = T` finished projectively, `R`'s `T` kept. -/
theorem step_bb18 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hj1 : 1 ≤ j) (hj : j ≤ 255) (R T : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r R rBnd) (hT : PointAt u.mem L.t T loose)
    {P : SuccArgs fd_ed25519_double_scalar_mul_base.sigs → GlobalState → Prop}
    (k : ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 →
      PointAt u'.mem r { T.finalMul with T := R.T } rBnd → P ⟨7, rfl, [v64 (j - 1)]ₕ⟩ u') :
    StepThen s r L W Xf V P ⟨17, rfl, [v64 j]ₕ⟩ u := by
  simp only [StepThen]
  denote_reduce_get
  -- `add_final_mul_projective(r, t)`
  refine (fd_ed25519_point_add_final_mul_projective_conforms r L.t u hu.refwf.wf (Ne.symm hV.t_r)
    hR.ptr hT.ptr (Dbln.coordBounds hT.ptr 0 L.t (coordPtr_zero _) (hT.bnd 0))
    (Dbln.coordBounds hT.ptr 1 _ rfl (hT.bnd 1)) (Dbln.coordBounds hT.ptr 3 _ rfl (hT.bnd 3))
    (Dbln.coordBounds hT.ptr 2 _ rfl (hT.bnd 2))).elim
    fun x h => h.elim fun y h => h.elim fun z h₁ => h₁.1.elim fun u₁ hc₁ => ?_
  peel_call hc₁.1 with hV.r, hV.t
  have hr := hR.ptr
  have h40 := (coordBits hr).1
  have h80 := (coordBits hr).2.1
  have h120 := (coordBits hr).2.2
  have hpt : IsPointPtr (((u.mem.splice r x).splice (r.withOffset 40) y).splice
      (r.withOffset 120) z) r :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr))
  -- `T` sits at bits 640 .. 960, apart from all three stores
  have hTlimb : ∀ i : Fin 5, readLimb? (r.withOffset 80) i
      (((u.mem.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z)
      = readLimb? (r.withOffset 80) i u.mem := fun i => by
    have hi : i.toNat < 5 := i.isLt
    rw [readLimb?_splice_of_disjoint i (.inr (.inr (by omega))),
      readLimb?_splice_of_disjoint i (.inr (.inl (by omega))),
      readLimb?_splice_of_disjoint i (.inr (.inl (by omega)))]
  have hR₁ : PointAt u₁.mem r { T.finalMul with T := R.T } rBnd :=
    PointAt.of_equiv hc₁.2.symm ⟨hpt, h₁.2.1.trans (by rw [hT.val, hR.val]), fun i => by
      fin_cases i
      · exact h₁.2.2.1
      · exact h₁.2.2.2.1
      · exact limbBounds_of_readLimb?_eq (h' := isCoordPtr hr 2) hTlimb (hR.bnd 2)
      · exact h₁.2.2.2.2.loose⟩
  have hu₁ := hu.store3 hV hc₁.2
  have htb₁ := htb.of_live?_eq (live?_store3 hc₁.2 _ (Ne.symm hV.ai_r))
  -- `j - 1`, `j >s 0`
  denote_step_reduce v 3 [LLVM.const?] fold
  rw [hV.c5, add_neg_one64 hj1 (by omega)] at hv2
  simp only [hV.c6, icmp_sgt_zero64 hj1 (show j < 2 ^ 63 by omega)] at hv3
  refine Common.Wnaf.term_condBr (by simp only [simp_spine, hv3]; rfl)
    ⟨fun _ h => (nomatch h), fun t htgt => ?_⟩
  obtain rfl := Sum.inr.inj htgt
  rw [if_pos (by decide)]
  simp only [Target.denote_mk, HVector.map, simp_spine, hv2]
  exact k u₁ hu₁ htb₁ hR₁

/-- `^bb16` through `^bb17` to `^bb19`, or through `^bb18` back to `^bb8(j - 1)`, walking on by
`stop19` or `stop8`. -/
theorem walk_bb16 (hV : EntryEnv V r L) {u : GlobalState}
    (j : Nat) (hj : j ≤ 255) (R T : Ed25519.Point) (hu : Frame s r L W u)
    (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R rBnd)
    (hT : PointAt u.mem L.t T loose)
    (stop19 : j = 0 → ∀ u', Frame s r L W u' → PointAt u'.mem r T.finalMul tight →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u')
    (stop8 : 1 ≤ j → ∀ u', Frame s r L W u' → Table u'.mem L.ai W.A 8 →
      PointAt u'.mem r { T.finalMul with T := R.T } rBnd →
      Runs s r L W Xf V ⟨7, rfl, [v64 (j - 1)]ₕ⟩ u') :
    Runs s r L W Xf V ⟨15, rfl, [v64 j]ₕ⟩ u :=
  .step (step_bb16 (P := Runs s r L W Xf V) hV j hj
    (fun hj0 => .step (step_bb17 hV T hu hT (stop19 hj0)))
    (fun hj0 => .step (step_bb18 hV j (by omega) hj R T hu htb hR hT (stop8 (by omega)))))

/-- One ladder iteration: from `^bb8(j)` with `r` representing `X`, to `^bb19` or `^bb8(j - 1)` with
`r` representing `ladderStep`. -/
theorem walk_iter {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point} (hV : EntryEnv V r L)
    (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255) (hBT : BaseTable s r L Bt)
    (hA : W.A.WellFormed) (hZ : W.A.Z = 1) (hG : G.WellFormed) (hB : BaseVals Bt G hG)
    {u : GlobalState} (j : Nat) (hj : j ≤ 255) (R : Ed25519.Point) {X : Edwards.Point Ed25519.curve}
    (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8) (hR : PointAt u.mem r R rBnd)
    (hX : R.Represents X)
    (stop19 : j = 0 → ∀ u' R', Frame s r L W u' → PointAt u'.mem r R' tight →
      R'.Represents (ladderStep (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j) →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u')
    (stop8 : 1 ≤ j → ∀ u' R', Frame s r L W u' → Table u'.mem L.ai W.A 8 →
      PointAt u'.mem r R' rBnd →
      R'.Represents (ladderStep (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j) →
      Runs s r L W Xf V ⟨7, rfl, [v64 (j - 1)]ₕ⟩ u') :
    Runs s r L W Xf V ⟨7, rfl, [v64 j]ₕ⟩ u := by
  have hd₁ := hD₁ j (by omega)
  have hd₂ := hD₂ j (by omega)
  obtain ⟨hT₁, hv₁⟩ := addDigit_represents hA hZ hX hd₁.1 hd₁.2
  obtain ⟨hT₂, hv₂⟩ := addDigitB_value (R := (addDigit W.A R (Common.Wnaf.slot W.w₁ j)).1)
    hG hB hT₁ hd₂.1 hd₂.2
  have hX₂ : (addDigitB Bt (addDigit W.A R (Common.Wnaf.slot W.w₁ j)).1
      (addDigit W.A R (Common.Wnaf.slot W.w₁ j)).2 (Common.Wnaf.slot W.w₂ j)).2.finalMul.Represents
      (ladderStep (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j) := by
    rw [ladderStep, ← hv₁, ← hv₂]
    exact Ed25519.Point.represents_toAffine hT₂
  exact walk_bb8 hV hD₁.digits15 j hj R hu htb hR fun _ hu₁ htb₁ hR₁ hT₁' =>
    walk_bb12 hV hBT hD₂.digits255 j hj _ _ hu₁ htb₁ hR₁ hT₁' fun _ hu₂ htb₂ hR₂ hT₂' =>
    walk_bb16 hV j hj _ _ hu₂ htb₂ hR₂ hT₂'
      (fun hj0 u₃ hu₃ hR₃ => stop19 hj0 u₃ _ hu₃ hR₃ hX₂)
      (fun hj1 u₃ hu₃ htb₃ hR₃ => stop8 hj1 u₃ _ hu₃ htb₃ hR₃ (hX₂.withT _))

/-- `^bb8(j)` through every remaining ladder iteration to `^bb19`, `r` representing the ladder's
value `Xf`; by induction on `j` over `walk_iter`. -/
theorem walk_bb8_all {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point}
    (hV : EntryEnv V r L) (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255)
    (hBT : BaseTable s r L Bt) (hA : W.A.WellFormed) (hZ : W.A.Z = 1) (hG : G.WellFormed)
    (hB : BaseVals Bt G hG)
    (stop19 : ∀ u' R', Frame s r L W u' → PointAt u'.mem r R' tight → R'.Represents Xf →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u') :
    ∀ (j : Nat), j ≤ 255 → ∀ (u : GlobalState) (R : Ed25519.Point)
      (X : Edwards.Point Ed25519.curve),
      ladder (W.A.toAffine hA) (G.toAffine hG) X W.w₁ W.w₂ j = Xf → Frame s r L W u →
      Table u.mem L.ai W.A 8 → PointAt u.mem r R rBnd → R.Represents X →
      Runs s r L W Xf V ⟨7, rfl, [v64 j]ₕ⟩ u
  | 0, hj, _, R, X, hXf, hu, htb, hR, hX =>
    walk_iter hV hD₁ hD₂ hBT hA hZ hG hB 0 hj R hu htb hR hX
      (fun _ u' R' hu' hR' hX' => stop19 u' R' hu' hR' (by rwa [← hXf, ladder_zero]))
      (fun hj1 => absurd hj1 (by omega))
  | j + 1, hj, _, R, X, hXf, hu, htb, hR, hX =>
    walk_iter hV hD₁ hD₂ hBT hA hZ hG hB (j + 1) hj R hu htb hR hX
      (fun hj0 => absurd hj0 (by omega))
      (fun _ u' R' hu' htb' hR' hX' =>
        walk_bb8_all hV hD₁ hD₂ hBT hA hZ hG hB stop19 j (by omega) u' R' _
          (by rw [← hXf, ladder_succ]) hu' htb' hR' hX')

/-- `^bb3(255)` through the leading-zero skip, `^bb6`, `^bb7` and the ladder to `^bb19`, `r`
representing the ladder's value. -/
theorem walk_loops {Bt : ℕ → Ed25519.PrecomputedPoint} {G : Ed25519.Point}
    (hV : EntryEnv V r L) (hD₁ : DigitVals W.w₁ 15) (hD₂ : DigitVals W.w₂ 255)
    (hBT : BaseTable s r L Bt) (hA : W.A.WellFormed) (hZ : W.A.Z = 1) (hG : G.WellFormed)
    (hB : BaseVals Bt G hG) (hXf : ladder (W.A.toAffine hA) (G.toAffine hG) 0 W.w₁ W.w₂ 255 = Xf)
    (stop19 : ∀ u' R', Frame s r L W u' → PointAt u'.mem r R' tight → R'.Represents Xf →
      Runs s r L W Xf V ⟨18, rfl, .nil⟩ u')
    {u : GlobalState} (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A 8)
    (hR : PointAt u.mem r .zero tight) :
    Runs s r L W Xf V ⟨2, rfl, [v32 255]ₕ⟩ u :=
  have hR' := hR.mono tight_le_rBnd
  have h0 : Ed25519.Point.zero.Represents (0 : Edwards.Point Ed25519.curve) :=
    toAffine_zero ▸ Ed25519.Point.represents_toAffine Ed25519.Point.wellFormed_zero
  walk_bb3_all hV hu 255 le_rfl
    (fun i' hi' _ hz => .step (step_bb6 (P := Runs s r L W Xf V) hV i' hi'
      (.step (step_bb7 hV i' hi'
        (walk_bb8_all hV hD₁ hD₂ hBT hA hZ hG hB stop19 i' hi' u _ 0
          ((ladder_skip (by omega) hz).trans hXf) hu htb hR' h0)))))
    (fun hz => stop19 u _ hu hR (by rw [← hXf, ladder_all_zero hz]; exact h0))

/-- `^bb19`: Lifetime ends, `return r`. -/
theorem step_bb19 (hV : EntryEnv V r L) {u : GlobalState} (R : Ed25519.Point)
    (hu : Frame s r L W u) (hR : PointAt u.mem r R tight) (hX : R.Represents Xf)
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
    (hBT : BaseTable s r L Bt) (hA : W.A.WellFormed) (hZ : W.A.Z = 1) (hG : G.WellFormed)
    (hB : BaseVals Bt G hG) (hXf : ladder (W.A.toAffine hA) (G.toAffine hG) 0 W.w₁ W.w₂ 255 = Xf)
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 7) {u : GlobalState}
    (hu : Frame s r L W u) (htb : Table u.mem L.ai W.A k) :
    Runs s r L W Xf V ⟨1, rfl, [v64 k]ₕ⟩ u :=
  walk_bb2_all hV
    (fun _ hu' htb' => .step (step_bb1 (P := Runs s r L W Xf V) hV hu' htb' fun _ hu₁ htb₁ hR₁ =>
      walk_loops hV hD₁ hD₂ hBT hA hZ hG hB hXf
        (fun _ R' hu₂ hR₂ hX₂ => .step (step_bb19 hV R' hu₂ hR₂ hX₂)) hu₁ htb₁ hR₁))
    k hk1 hk hu htb

end Steps

/-! ## Entering and leaving -/

/-- `RefWF` at a state that kept `w`'s blocks below its counter outside `apart`, apart now from
pointers at or above that counter too. -/
theorem refWF_widen {w w' : GlobalState} {apart apart' : List Pointer} (hw : w.RefWF apart)
    (hwf : w'.WF) (hg : w'.globals = w.globals)
    (hlive : ∀ b : BlockId, b.id < w.alloc.nextFreeBlock → (∀ p ∈ apart, b ≠ p.id) →
      w'.mem.live? b = w.mem.live? b)
    (hap : ∀ p ∈ apart', w.alloc.nextFreeBlock ≤ p.id.id ∨ p ∈ apart) : w'.RefWF apart' :=
  let apartA {q : Pointer} (hq : Apart q apart) (hb : q.id.id < w.alloc.nextFreeBlock) :
      Apart q apart' := fun p hp =>
    (hap p hp).elim (fun hle he => by have := congrArg BlockId.id he; omega) (hq p)
  let carry {name : String} {val : ZMod _root_.p} {q : Pointer} (hq : Apart q apart)
      (hgq : FieldGlobal w name q val) : FieldGlobal w' name q val :=
    let h := hlive q.id (hgq.below hw.wf) hq
    { addr := by simp only [GlobalPtr, hg]; exact hgq.addr
      ptr := isFieldElemPtr_of_live?_eq h hgq.ptr
      value := carryVal h hgq.value
      bnd := carryBnd h hgq.bnd }
  { wf := hwf
    gd := let ⟨q, hg', hq⟩ := hw.gd; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gone := let ⟨q, hg', hq⟩ := hw.gone; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gm1 := let ⟨q, hg', hq⟩ := hw.gm1; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gy0 := let ⟨q, hg', hq⟩ := hw.gy0; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gy1 := let ⟨q, hg', hq⟩ := hw.gy1; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gk := let ⟨q, hg', hq⟩ := hw.gk; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gzero := let ⟨q, hg', hq⟩ := hw.gzero; ⟨q, carry hq hg', apartA hq (hg'.below hw.wf)⟩
    gtbl := let ⟨q, hg', hq⟩ := hw.gtbl
      ⟨q, hg'.carry (by simp only [GlobalPtr, hg]; exact hg'.addr)
        (hlive q.id (hg'.below hw.wf) hq), apartA hq (hg'.below hw.wf)⟩ }

/-- `Written` with `r`'s own coordinates: the four stores change nothing. -/
theorem live?_splice_extract4 {m : MemoryState} {r : Pointer} {blk : LiveBlock}
    (hl : m.live? r.id = some blk) (q : BlockId) :
    ((((m.splice r (blk.bytes.extractLsb' r.offsetInBits (5 * 64))).splice (r.withOffset 40)
      (blk.bytes.extractLsb' (r.withOffset 40).offsetInBits (5 * 64))).splice (r.withOffset 120)
      (blk.bytes.extractLsb' (r.withOffset 120).offsetInBits (5 * 64))).splice (r.withOffset 80)
      (blk.bytes.extractLsb' (r.withOffset 80).offsetInBits (5 * 64))).live? q = m.live? q :=
  have h₁ := live?_splice_extract (p := r) (5 * 64) hl
  have h₂ := live?_splice_extract (p := r.withOffset 40) (5 * 64) ((h₁ r.id).trans hl)
  have h₃ := live?_splice_extract (p := r.withOffset 120) (5 * 64)
    ((h₂ r.id).trans ((h₁ r.id).trans hl))
  have h₄ := live?_splice_extract (p := r.withOffset 80) (5 * 64)
    ((h₃ r.id).trans ((h₂ r.id).trans ((h₁ r.id).trans hl)))
  (h₄ q).trans ((h₃ q).trans ((h₂ q).trans (h₁ q)))

/-- `wf_splice4` for three stores. -/
theorem wf_splice3 {t : GlobalState} {p₁ p₂ p₃ : Pointer}
    {w₁ w₂ w₃ : Nat} {x₁ : BitVec w₁} {x₂ : BitVec w₂} {x₃ : BitVec w₃} (ht : t.WF) :
    ({ t with mem := ((t.mem.splice p₁ x₁).splice p₂ x₂).splice p₃ x₃ } : GlobalState).WF :=
  fun q hq => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (ht q hq)))

/-- `^bb0`'s `alloca` widths in bits: `n1slide`, `n2slide`, `ai`, `a2`, `t`. -/
def allocW : Nat → Nat
  | 0 => 256 * 16
  | 1 => 256 * 16
  | 2 => 8 * (4 * 5 * 64)
  | _ => 4 * 5 * 64

/-- The `k`-th `alloca` of `^bb0`. -/
abbrev slot (s : GlobalState) (k : Nat) : Pointer := s.chainPtr allocW k

/-- `^bb0`: `wnaf(n1slide, n1, 4); wnaf(n2slide, n2, 8); set(ai[0], a); dbln(a2, a, 1);
into_precomputed(ai[0])`, then `br ^bb2(1)`. -/
theorem entry_run (r n1 a n2 : Pointer) (s : GlobalState) (hs : s.RefWF [r])
    (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a)
    (hn1 : IsByteBufPtr s.mem n1) (hn2 : IsByteBufPtr s.mem n2)
    (haX : BiasBounds (isCoordPtr ha 0)) (haY : LimbBounds (isCoordPtr ha 1))
    (haZ : LimbBounds.Loose (isCoordPtr ha 3)) (haT : LimbBounds.Loose (isCoordPtr ha 2))
    : ∃ (L : Locals) (Vout : fd_ed25519_double_scalar_mul_base.Γout.Valuation) (u : GlobalState),
      StateT.run (fd_ed25519_double_scalar_mul_base.entry.denote
          (Ctxt.Valuation.ofHVector [.value n2, .value a, .value n1, .value r]ₕ)) s
        = .value ((Vout, .inr ⟨1, rfl, [v64 1]ₕ⟩), u)
      ∧ L.tbl.id.id < s.alloc.nextFreeBlock ∧ L.tbl.id ≠ r.id
      ∧ GlobalPtr s "fd_ed25519_base_point_wnaf_table" L.tbl
      ∧ EntryEnv Vout r L ∧ ∃ W : Vals, W.A = readPoint ha ∧ Frame s r L W u
        ∧ Table u.mem L.ai W.A 1
        ∧ DigitVals W.w₁ 15 ∧ DigitVals W.w₂ 255
        ∧ Common.digitSum W.w₁ 256 = ((readBuf hn1).toNat % 2 ^ 255 : ℕ)
        ∧ Common.digitSum W.w₂ 256 = ((readBuf hn2).toNat % 2 ^ 255 : ℕ) := by
  denote_step_reduce v 12 [LLVM.const?]
  obtain ⟨gwafTable, hgwafTable, hgap⟩ := hs.gtbl
  peel_addressof hgwafTable.addr
  -- `%14 … %18`: `n1slide`, `n2slide`, `ai`, `a2`, `t`
  peel_alloca_chain s, allocW, 5
  fold_cells s, allocW, slot, 5
  subst hv0 hv1 hv2 hv3 hv4 hv5 hv6 hv7 hv8 hv9 hv10 hv11 hv12
  have hwL : (s.allocaChain allocW 5).WF := GlobalState.WF.allocaChain hs.wf 5
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
  refine (wnaf_run (slot s 0) n1 4#32 15 (s.allocaChain allocW 5) hwL
    ⟨GlobalState.fits_chainPtr (by omega), by simp⟩
    (isByteBufPtr_of_live?_eq (fb n1.id (lt_nextFreeBlock_of_fits hs.wf hn1.1)) hn1)
    (.inl ⟨rfl, rfl⟩)).elim fun u₁ h₁ => h₁.elim fun hrun₁ he₁ => ?_
  peel_call hrun₁

  -- `wnaf(n2slide, n2, 8)`
  obtain ⟨w₁, he₁, hd₁, hsum₁⟩ := he₁
  have hS₁ := (hsum₁ (hslot_below (lt_nextFreeBlock_of_fits hs.wf hn1.1))).trans
    (congrArg (fun x : BitVec 256 => ((x.toNat % 2 ^ 255 : ℕ) : ℤ))
      (readBuf_of_live?_eq (hp := hn1)
        (hp' := isByteBufPtr_of_live?_eq (fb n1.id (lt_nextFreeBlock_of_fits hs.wf hn1.1)) hn1)
        (fb n1.id (lt_nextFreeBlock_of_fits hs.wf hn1.1))))
  have hl₁ : ∀ b : BlockId, (slot s 0).id ≠ b →
      u₁.mem.live? b = (s.allocaChain allocW 5).mem.live? b := fun b hb =>
    (live?_of_equiv_mem he₁.symm b).trans (live?_splice_ne (p := slot s 0) hb)
  peel_lifetime
  refine (wnaf_run (slot s 1) n2 8#32 255 u₁ (GlobalState.WF.of_equiv hwL.splice he₁)
    ⟨fits_of_live?_eq (hl₁ _ (hslot (by omega))) (GlobalState.fits_chainPtr (by omega)), by simp⟩
    (isByteBufPtr_of_live?_eq ((hl₁ _ (hslot_below (lt_nextFreeBlock_of_fits hs.wf hn2.1))).trans
      (fb n2.id (lt_nextFreeBlock_of_fits hs.wf hn2.1))) hn2)
    (.inr ⟨rfl, rfl⟩)).elim fun u₂ h₂ => h₂.elim fun hrun₂ he₂ => ?_
  peel_call hrun₂

  iterate 3 peel_lifetime

  -- `set(ai[0], a)`
  obtain ⟨w₂, he₂, hd₂, hsum₂⟩ := he₂
  have hS₂ := (hsum₂ (hslot_below (lt_nextFreeBlock_of_fits hs.wf hn2.1))).trans
    (congrArg (fun x : BitVec 256 => ((x.toNat % 2 ^ 255 : ℕ) : ℤ))
      (readBuf_of_live?_eq (hp := hn2)
        (hp' := isByteBufPtr_of_live?_eq ((hl₁ _ (hslot_below (lt_nextFreeBlock_of_fits hs.wf hn2.1))).trans
          (fb n2.id (lt_nextFreeBlock_of_fits hs.wf hn2.1))) hn2)
        ((hl₁ _ (hslot_below (lt_nextFreeBlock_of_fits hs.wf hn2.1))).trans
          (fb n2.id (lt_nextFreeBlock_of_fits hs.wf hn2.1)))))
  have hl₂ : ∀ b : BlockId, (slot s 1).id ≠ b → u₂.mem.live? b = u₁.mem.live? b := fun b hb =>
    (live?_of_equiv_mem he₂.symm b).trans (live?_splice_ne (p := slot s 1) hb)
  have hna : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs.wf ha.1
  have ha₂ : IsPointPtr u₂.mem a :=
    isPointPtr_of_live?_eq ((hl₂ _ (hslot_below hna)).trans ((hl₁ _ (hslot_below hna)).trans
      (fb a.id hna))) ha
  have hai₂ : IsPointPtr u₂.mem (slot s 2) :=
    ⟨fits_of_live?_eq ((hl₂ _ (hslot (by omega))).trans (hl₁ _ (hslot (by omega))))
      (Fits.mono (GlobalState.fits_chainPtr (w := allocW) (s := s) (k := 5) (show 2 < 5 by omega))
        (by simp [allocW])), by simp⟩
  have hw₂ : u₂.WF := GlobalState.WF.of_equiv (GlobalState.WF.of_equiv hwL.splice he₁).splice he₂
  refine (fd_ed25519_point_set_conforms (slot s 2) a u₂ hw₂ (hslot_below hna) hai₂ ha₂).elim
    fun oX h => h.elim fun oY h => h.elim fun oZ h => h.elim fun oT hset => hset.1.elim
    fun u₃ h₃ => h₃.elim fun hrun₃ he₃ => ?_
  peel_call hrun₃

  -- `dbln(a2, a, 1)`
  have hl₃ : ∀ b : BlockId, (slot s 2).id ≠ b → u₃.mem.live? b = u₂.mem.live? b := fun b hb =>
    (live?_of_equiv_mem he₃.symm b).trans
      ((live?_splice_ne (p := (slot s 2).withOffset 80) hb).trans
      ((live?_splice_ne (p := (slot s 2).withOffset 120) hb).trans
        ((live?_splice_ne (p := (slot s 2).withOffset 40) hb).trans
          (live?_splice_ne (p := slot s 2) hb))))
  have hla₃ : u₃.mem.live? a.id = s.mem.live? a.id :=
    (hl₃ _ (hslot_below hna)).trans ((hl₂ _ (hslot_below hna)).trans
      ((hl₁ _ (hslot_below hna)).trans (fb a.id hna)))
  have ha2₃ : IsPointPtr u₃.mem (slot s 3) :=
    ⟨fits_of_live?_eq ((hl₃ _ (hslot (by omega))).trans ((hl₂ _ (hslot (by omega))).trans
        (hl₁ _ (hslot (by omega))))) (GlobalState.fits_chainPtr (show 3 < 5 by omega)), by simp⟩
  refine (fd_ed25519_point_dbln_conforms (slot s 3) a 1#32 u₃ ((wf_splice4 hw₂).of_equiv he₃)
    ha2₃ (isPointPtr_of_live?_eq hla₃ ha)
    (carryBias (q := a.withOffset ((0 : Fin 4) * (5 * 8))) hla₃ haX)
    (carryBnd (q := a.withOffset ((1 : Fin 4) * (5 * 8))) hla₃ haY)
    (carryBnd (q := a.withOffset ((3 : Fin 4) * (5 * 8))) hla₃ haZ) (by decide)).elim
    fun dX h => h.elim fun dY h => h.elim fun dZ h => h.elim fun dT h => h.1.elim
    fun u₄ h₄ => h₄.elim fun hrun₄ he₄ => ?_
  peel_call hrun₄

  -- `into_precomputed(ai[0])`
  have hw₃ : u₃.WF := (wf_splice4 hw₂).of_equiv he₃
  have hl₄ : ∀ b : BlockId, (slot s 3).id ≠ b → u₄.mem.live? b = u₃.mem.live? b := fun b hb =>
    (live?_of_equiv_mem he₄.symm b).trans
      ((live?_splice_ne (p := (slot s 3).withOffset 80) hb).trans
      ((live?_splice_ne (p := (slot s 3).withOffset 120) hb).trans
        ((live?_splice_ne (p := (slot s 3).withOffset 40) hb).trans
          (live?_splice_ne (p := slot s 3) hb))))
  have hla₂ : u₂.mem.live? a.id = s.mem.live? a.id :=
    (hl₂ _ (hslot_below hna)).trans ((hl₁ _ (hslot_below hna)).trans (fb a.id hna))
  have hl₄₂ : u₄.mem.live? (slot s 2).id = u₃.mem.live? (slot s 2).id := hl₄ _ (hslot (by omega))
  have hai₄ : IsPointPtr u₄.mem (slot s 2) :=
    isPointPtr_of_live?_eq hl₄₂ (isPointPtr_of_equiv he₃.symm
      (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hai₂)))))
  -- `ai[0]`'s coordinates are `a`'s, copied by `set`
  have copy : ∀ {q qa : Pointer} {B : ℕ}, q.id = (slot s 2).id →
      (∀ i, readLimb? q i u₃.mem = readLimb? qa i u₂.mem) →
      (∀ (i : Fin 5) (l : ℕ), readLimb? qa i u₂.mem = some l → l ≤ B) →
      (h : IsFieldElemPtr u₄.mem q) → LimbBounds h B := fun hq hc hb h =>
    limbBounds_of_readLimb? h fun i l hl =>
      hb i l ((hc i).symm.trans ((readLimb?_of_live?_eq (hq ▸ hl₄₂) i).symm.trans hl))
  have copyBias : ∀ {q qa : Pointer}, q.id = (slot s 2).id →
      (∀ i, readLimb? q i u₃.mem = readLimb? qa i u₂.mem) → BiasBounds? qa u₂.mem →
      (h : IsFieldElemPtr u₄.mem q) → BiasBounds h := fun hq hc hb h =>
    biasBounds_of_readLimb? h fun i l hl =>
      hb i l ((hc i).symm.trans ((readLimb?_of_live?_eq (hq ▸ hl₄₂) i).symm.trans hl))
  have hrefwf₄ : u₄.RefWF [slot s 2] :=
    refWF_widen hs ((wf_splice4 hw₃).of_equiv he₄)
      (he₄.globals.symm.trans (he₃.globals.symm.trans (he₂.globals.symm.trans
        (he₁.globals.symm.trans rfl))))
      (fun b hb hbr => (hl₄ b (hslot_below hb)).trans ((hl₃ b (hslot_below hb)).trans
        ((hl₂ b (hslot_below hb)).trans ((hl₁ b (hslot_below hb)).trans (fb b hb)))))
      (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simp)
  refine (fd_curve25519_into_precomputed_conforms (slot s 2) u₄ hai₄ hrefwf₄
    (copyBias (q := slot s 2) (qa := a) rfl
      (fun i => (readLimb?_of_equiv_mem he₃ (slot s 2) i).trans (hset.2.1 i))
      (Dbln.coordBias ha₂ 0 a (coordPtr_zero a)
        (carryBias (q := a.withOffset ((0 : Fin 4) * (5 * 8))) hla₂ haX)) _)
    (copy (q := (slot s 2).withOffset 40) (qa := a.withOffset 40) rfl
      (fun i => (readLimb?_of_equiv_mem he₃ ((slot s 2).withOffset 40) i).trans (hset.2.2.1 i))
      (limbBounds_of_live?_eq (p := a.withOffset 40) hla₂ (Dbln.coordBounds ha 1 _ rfl haY)) _)
    (copy (q := (slot s 2).withOffset 80) (qa := a.withOffset 80) rfl
      (fun i => (readLimb?_of_equiv_mem he₃ ((slot s 2).withOffset 80) i).trans (hset.2.2.2.1 i))
      (limbBounds_of_live?_eq (p := a.withOffset 80) hla₂ (Dbln.coordBounds ha 2 _ rfl haT))
      _)).elim
    fun u₅ h₅ => h₅.elim fun hrun₅ he₅ => ?_
  -- the spec's `Valuation.singleton`, as the `ofHVector` `peel_call` matches by reference
  have hrun₅' : StateT.run (runFunction (fd_curve25519_into_precomputed.denote
      (Ctxt.Valuation.ofHVector [PoisonOr.value (slot s 2)]ₕ))) u₄ = .value ([]ₕ, u₅) := hrun₅
  peel_call hrun₅'

  simp_return
  refine ⟨⟨gwafTable, (slot s 0), (slot s 1), (slot s 2), (slot s 3), (slot s 4)⟩,
    hgwafTable.below hs.wf, hgap r (by simp), hgwafTable.addr, ?_⟩
  constructor

  case left =>
    constructor <;> simp
    all_goals first
      | exact hslot_below (lt_nextFreeBlock_of_fits hs.wf hr.1)
      | exact hslot (by omega)

  case right =>
    refine he₅.elim fun eX h' => h'.elim fun eY h' => h'.elim fun eT h₅ => ?_
    have hw₄ : u₄.WF := (wf_splice4 hw₃).of_equiv he₄
    have hl₅ : ∀ b : BlockId, (slot s 2).id ≠ b → u₅.mem.live? b = u₄.mem.live? b := fun b hb =>
      (live?_of_equiv_mem h₅.1.symm b).trans
        ((live?_splice_ne (p := (slot s 2).withOffset 80) hb).trans
          ((live?_splice_ne (p := (slot s 2).withOffset 40) hb).trans
            (live?_splice_ne (p := slot s 2) hb)))
    have hbelow : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → u₅.mem.live? b = s.mem.live? b :=
      fun b hb => (hl₅ b (hslot_below hb)).trans ((hl₄ b (hslot_below hb)).trans
        ((hl₃ b (hslot_below hb)).trans ((hl₂ b (hslot_below hb)).trans
          ((hl₁ b (hslot_below hb)).trans (fb b hb)))))
    have hrb : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs.wf hr.1
    have hfits₁ : Fits u₁.mem (slot s 0) (256 * 16) :=
      fits_of_live?_eq (live?_of_equiv_mem he₁.symm _)
        (fits_splice (GlobalState.fits_chainPtr (by omega)))
    have hfits₂ : Fits u₂.mem (slot s 1) (256 * 16) :=
      fits_of_live?_eq (live?_of_equiv_mem he₂.symm _) (fits_splice
        (fits_of_live?_eq (hl₁ _ (hslot (by omega))) (GlobalState.fits_chainPtr (by omega))))
    have hs₁ : Common.IsSlidesPtr u₅.mem (slot s 0) :=
      ⟨fits_of_live?_eq ((hl₅ _ (hslot (by omega))).trans ((hl₄ _ (hslot (by omega))).trans
        ((hl₃ _ (hslot (by omega))).trans (hl₂ _ (hslot (by omega)))))) hfits₁, by simp⟩
    have hs₂ : Common.IsSlidesPtr u₅.mem (slot s 1) :=
      ⟨fits_of_live?_eq ((hl₅ _ (hslot (by omega))).trans ((hl₄ _ (hslot (by omega))).trans
        (hl₃ _ (hslot (by omega))))) hfits₂, by simp⟩
    -- `a2 = dbln 1 a`, tight
    have hA2 : PointAt u₅.mem (slot s 3) ((readPoint ha).dbln 1#32) tight :=
      (PointAt.of_equiv he₄.symm ⟨_, h.2.1.trans (congrArg _ (readPoint_of_live?_eq hla₃ ha _)),
        h.2.2⟩).of_live?_eq (hl₅ _ (hslot (by omega)))
    -- `ai[0]`: `a`'s point through `set`, then `into_precomputed`
    have hai₄A : readPoint hai₄ = readPoint ha :=
      (readPoint_of_live?_eq (hl₄₂.trans (live?_of_equiv_mem he₃.symm _))
        (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hai₂))))
        hai₄).trans
        (hset.2.2.2.2.2.trans (readPoint_of_live?_eq hla₂ ha ha₂))
    have h40 := (coordBits hai₄).1
    have h80 := (coordBits hai₄).2.1
    have h120 := (coordBits hai₄).2.2
    -- `Z` is untouched by `into_precomputed`, `a`'s loose one
    have hZ₄ : LimbBounds (isCoordPtr hai₄ 3) 0x18000000000000 :=
      copy (q := (slot s 2).withOffset 120) (qa := a.withOffset 120) rfl
        (fun i => (readLimb?_of_equiv_mem he₃ _ i).trans (hset.2.2.2.2.1 i))
        (limbBounds_of_live?_eq (p := a.withOffset 120) hla₂ (Dbln.coordBounds ha 3 _ rfl haZ)) _
    have htb : Table u₅.mem (slot s 2) (readPoint ha) 1 := fun k hk => by
      obtain rfl : k = 0 := by omega
      rw [aiPtr, entryPtr_zero]
      refine ⟨_, PointAt.of_equiv h₅.1.symm
        ⟨isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hai₄)), rfl, fun i => ?_⟩,
        h₅.2.1.trans (congrArg _ hai₄A)⟩
      fin_cases i
      · exact limbBounds_congr_bound (coordPtr_zero _).symm h₅.2.2.1
      · exact limbBounds_congr_bound (coordPtr_one _).symm h₅.2.2.2.1
      · exact (limbBounds_congr_bound (coordPtr_two _).symm h₅.2.2.2.2).loose
      · refine limbBounds_of_readLimb? _
          (bounds_of_limbs (p := (slot s 2).withOffset 120) (fun j => ?_)
            (limbBounds_readLimb? _ hZ₄))
        rw [readLimb?_splice_of_disjoint j (Or.inr (Or.inl (by simp only [h80, h120]; omega))),
          readLimb?_splice_of_disjoint j (Or.inr (Or.inl (by simp only [h40, h120]; omega))),
          readLimb?_splice_of_disjoint j (Or.inr (Or.inl (by simp only [h120]; omega)))]
    have hw₁ : SlidesAt u₅.mem (slot s 0) w₁ :=
      (SlidesAt.splice (m := (s.allocaChain allocW 5).mem)
        ⟨GlobalState.fits_chainPtr (by omega), by simp⟩ w₁).of_live?_eq
        (((hl₅ _ (hslot (by omega))).trans ((hl₄ _ (hslot (by omega))).trans
          ((hl₃ _ (hslot (by omega))).trans (hl₂ _ (hslot (by omega)))))).trans
          (live?_of_equiv_mem he₁.symm _))
    have hw₂ : SlidesAt u₅.mem (slot s 1) w₂ :=
      (SlidesAt.splice (m := u₁.mem)
        ⟨fits_of_live?_eq (hl₁ _ (hslot (by omega))) (GlobalState.fits_chainPtr (by omega)),
          by simp⟩ w₂).of_live?_eq
        (((hl₅ _ (hslot (by omega))).trans ((hl₄ _ (hslot (by omega))).trans
          (hl₃ _ (hslot (by omega))))).trans (live?_of_equiv_mem he₂.symm _))
    refine ⟨⟨w₁, w₂, readPoint ha⟩, rfl, (show Frame _ _ _ _ _ from
      { refwf := refWF_widen hs ((wf_splice3 hw₄).of_equiv h₅.1)
          (h₅.1.globals.symm.trans (he₄.globals.symm.trans (he₃.globals.symm.trans
            (he₂.globals.symm.trans (he₁.globals.symm.trans rfl)))))
          (fun b hb _ => hbelow b hb) (fun p hp => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl
            · exact Or.inr (by simp)
            all_goals exact Or.inl (by simp))
        rptr := isPointPtr_of_live?_eq (hbelow _ hrb) hr
        tptr := ⟨fits_of_live?_eq ((hl₅ _ (hslot (by omega))).trans
          ((hl₄ _ (hslot (by omega))).trans ((hl₃ _ (hslot (by omega))).trans
            ((hl₂ _ (hslot (by omega))).trans (hl₁ _ (hslot (by omega)))))))
          (GlobalState.fits_chainPtr (show 4 < 5 by omega)), by simp⟩
        fresh := ⟨by simp, by simp⟩
        aifits := ⟨fits_of_live?_eq (live?_of_equiv_mem h₅.1.symm _)
          (fits_splice (fits_splice (fits_splice (fits_of_live?_eq (hl₄ _ (hslot (by omega)))
            (fits_of_live?_eq (live?_of_equiv_mem he₃.symm _)
              (fits_splice (fits_splice (fits_splice (fits_splice
                (fits_of_live?_eq ((hl₂ _ (hslot (by omega))).trans (hl₁ _ (hslot (by omega))))
                  (GlobalState.fits_chainPtr (show 2 < 5 by omega)))))))))))), by simp⟩
        n1slide := hw₁
        n2slide := hw₂
        a2 := hA2
        caller := fun b hb _ => hbelow b hb
        written := hr.1.elim fun blk ⟨hblk, _⟩ =>
          ⟨_, _, _, _, (hbelow _ hrb).trans
            (live?_splice_extract4 (blk := blk) (by simp [MemoryState.live?, hblk]) r.id).symm⟩ }),
      htb, hd₁, hd₂, hS₁, hS₂⟩

end DoubleScalarMulBase

open DoubleScalarMulBase Common.DoubleScalarMulBase in
theorem fd_ed25519_double_scalar_mul_base_conforms (r n1 a n2 : Pointer) (s : GlobalState)
    (hs : s.RefWF [r]) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a)
    (hn1 : IsByteBufPtr s.mem n1) (hn2 : IsByteBufPtr s.mem n2)
    (haX : BiasBounds (isCoordPtr ha 0)) (haY : LimbBounds (isCoordPtr ha 1))
    (haZ : LimbBounds.Loose (isCoordPtr ha 3)) (haT : LimbBounds.Loose (isCoordPtr ha 2))
    : fd_ed25519_double_scalar_mul_base_spec r n1 a n2 s := by
  simp only [fd_ed25519_double_scalar_mul_base_spec, Cfg.denote]
  intro _ _ _ _ hAa hZa Bt hTbl hB
  refine run_runFunction' _ ?_x
  obtain ⟨L, Vout, u₀, hentry, htbl, htblr, hgp, hV, W, hWA, hu₀, htb₀, hD₁, hD₂, hS₁, hS₂⟩ :=
    entry_run r n1 a n2 s hs hr ha hn1 hn2 haX haY haZ haT
  have hA : W.A.WellFormed := hWA ▸ hAa
  have hZ : W.A.Z = 1 := hWA ▸ hZa
  have hpts : ∀ k < 128, ∃ P, PointAt s.mem (aiPtr L.tbl k) P loose ∧
      Ed25519.PrecomputedPoint.ofSlots P = Bt k := fun k hk =>
    (hTbl L.tbl hgp k hk).elim fun h ⟨hb, hv⟩ => ⟨_, ⟨h, rfl, hb⟩, hv⟩
  obtain ⟨rs, u, hrun, rfl, hF, R, hRu, hRX⟩ :=
    walk_bb2 hV hD₁ hD₂ ⟨htbl, htblr, hpts⟩ hA hZ Ed25519.wellFormed_basePoint hB rfl 1 le_rfl
      (by omega) hu₀ htb₀
  -- `r` holds `(n₁ mod 2^255)·a + (n₂ mod 2^255)·G`
  rw [ladder_digitSum, hS₁, hS₂] at hRX
  obtain ⟨oX, oY, oZ, oT, hlr⟩ := hF.written
  refine ⟨u, ?run, oX, oY, oZ, oT, ?equiv, ?val, ?bnd⟩
  case bnd =>
    exact fun i => carryBnd (q := r.withOffset (i * (5 * 8))) hlr.symm (hRu.bnd i)
  case val =>
    rw [readPoint_of_live?_eq hlr.symm hRu.ptr, hRu.val,
      ← Ed25519.Point.toAffine_congr hWA hA hAa, ← natCast_zsmul, ← natCast_zsmul]
    exact hRX
  case run =>
    rw [EffectM.run_bind, hentry, PoisonOr.value_bind]
    exact hrun
  case equiv =>
    refine (popFrame_equiv_block hs.wf (lt_nextFreeBlock_of_fits hs.wf hr.1)
      hF.caller (fun b hbr => ?_) hlr).symm
    have hrb : r.id ≠ b := fun h => hbr h.symm
    exact (live?_splice_ne (p := r.withOffset 80) hrb).trans
      ((live?_splice_ne (p := r.withOffset 120) hrb).trans
        ((live?_splice_ne (p := r.withOffset 40) hrb).trans (live?_splice_ne (p := r) hrb)))

end Firedancer.Ref
