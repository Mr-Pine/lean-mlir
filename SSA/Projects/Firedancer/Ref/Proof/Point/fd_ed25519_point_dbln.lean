/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Spec.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Ref.Spec.Point.Dbl
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_partial_dbl
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Ref.Proof.Point.fd_ed25519_point_add_final_mul_projective

/-!
# `fd_ed25519_point_dbln` conformance (ref)

`^bb0` allocates the 160-byte `t`, runs `partial_dbl(t, a)` and branches on
`n >s 1`; `^bb2(i)` is the loop body `add_final_mul_projective(r, t);
partial_dbl(t, r); i + 1 <u n`; `^bb1` is `add_final_mul(r, t)` and the return.

`Inv` is what holds at the loop header after `k` bodies: `t` is
`partialDbl (dbl^[k] a)` with loose limbs, every caller block but `r` is as on
entry, and `r`'s block is `s`'s up to what a final four-coordinate store at `r`
overwrites (`Covered`) -- the loop's stores to `r` are all inside that range.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

namespace Dbln

/-! ### Later stores at `r` absorb earlier ones -/

/-- `live?` of a store into the block `b` it addresses. -/
theorem live?_splice_of_id {m : MemoryState} {p : Pointer} {b : BlockId} (hp : p.id = b)
    {w : Nat} (x : BitVec w) :
    (m.splice p x).live? b
      = (m.live? b).map fun blk => { length := blk.length, bytes := spliceBits blk.bytes p.offsetInBits x } := by
  subst hp
  cases hb : m.live? p.id with
  | none => exact splicedDead hb
  | some blk => exact splicedLive m p blk hb x

/-- Stores at `o + {0, 320, 960}` followed by stores at `o + {0, 320, 960, 640}`
are the latter alone. -/
theorem spliceBits_absorb {n : Nat} (bytes : BitVec n) (o : Nat) (x₁ y₁ z₁ x y z v : BitVec 320) :
    spliceBits (spliceBits (spliceBits (spliceBits (spliceBits (spliceBits (spliceBits bytes
      o x₁) (o + 320) y₁) (o + 960) z₁) o x) (o + 320) y) (o + 960) z) (o + 640) v
    = spliceBits (spliceBits (spliceBits (spliceBits bytes o x) (o + 320) y) (o + 960) z)
      (o + 640) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  split_ifs <;> rfl

/-- `r`'s block after `X, Y, Z` stores and then a full four-coordinate store is
the block after the four-coordinate store alone. -/
theorem live?_absorb {m : MemoryState} {r : Pointer}
    (h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320)
    (h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640)
    (h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960)
    (x₁ y₁ z₁ x y z v : BitVec (5 * 64)) :
    (((((((m.splice r x₁).splice (r.withOffset 40) y₁).splice (r.withOffset 120) z₁).splice
      r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).splice (r.withOffset 80) v).live? r.id
    = ((((m.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).splice
      (r.withOffset 80) v).live? r.id := by
  simp only [live?_splice_of_id (p := r.withOffset 80) (b := r.id) rfl,
    live?_splice_of_id (p := r.withOffset 120) (b := r.id) rfl,
    live?_splice_of_id (p := r.withOffset 40) (b := r.id) rfl,
    live?_splice_of_id (p := r) (b := r.id) rfl, Option.map_map]
  congr 1
  funext blk
  simp only [Function.comp_apply, h40, h80, h120]
  rw [spliceBits_absorb]

/-- `r`'s block in `u` is `s`'s, up to what a store of all four coordinates at
`r` overwrites. -/
def Covered (s u : GlobalState) (r : Pointer) : Prop :=
  ∀ x y z v : BitVec (5 * 64),
    ((((u.mem.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).splice
      (r.withOffset 80) v).live? r.id
    = ((((s.mem.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).splice
      (r.withOffset 80) v).live? r.id

theorem Covered.of_live? {s u : GlobalState} {r : Pointer}
    (h : u.mem.live? r.id = s.mem.live? r.id) : Covered s u r := fun _ _ _ _ =>
  live?_splice_congr (p := r.withOffset 80) (live?_splice_congr (p := r.withOffset 120)
    (live?_splice_congr (p := r.withOffset 40) (live?_splice_congr (p := r) h)))

/-- A step that stored `X, Y, Z` at `r` keeps `r` covered. -/
theorem Covered.step {s u u' : GlobalState} {r : Pointer}
    (h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320)
    (h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640)
    (h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960)
    (hc : Covered s u r) {x₁ y₁ z₁ : BitVec (5 * 64)}
    (h : u'.mem.live? r.id
      = (((u.mem.splice r x₁).splice (r.withOffset 40) y₁).splice (r.withOffset 120) z₁).live? r.id) :
    Covered s u' r := fun x y z v =>
  (live?_splice_congr (p := r.withOffset 80) (live?_splice_congr (p := r.withOffset 120)
    (live?_splice_congr (p := r.withOffset 40) (live?_splice_congr (p := r) h)))).trans
    ((live?_absorb h40 h80 h120 x₁ y₁ z₁ x y z v).trans (hc x y z v))

/-! ### The three callees, as steps -/

/-- `LimbBounds` of coordinate `i`, in `readLimb?` form at its pointer. -/
theorem coordBounds {m : MemoryState} {p : Pointer} {B : ℕ} (h : IsPointPtr m p) (i : Fin 4)
    (q : Pointer) (hq : p.withOffset (i * (5 * 8)) = q) (hb : LimbBounds (isCoordPtr h i) B) :
    ∀ (j : Fin 5) (l : ℕ), readLimb? q j m = some l → l ≤ B := by
  subst hq; exact limbBounds_readLimb? _ hb

/-- `partial_dbl(t, src)`: `t` becomes `partialDbl src`, nothing but `t`'s block moves. -/
theorem partialDbl_step {t src : Pointer} {w : GlobalState} (hw : w.WF)
    (ht : IsPointPtr w.mem t) (hsrc : IsPointPtr w.mem src)
    (bX : ∀ (i : Fin 5) (l : ℕ), readLimb? src i w.mem = some l → l ≤ 0x8000000000000)
    (bY : ∀ (i : Fin 5) (l : ℕ), readLimb? (src.withOffset 40) i w.mem = some l → l ≤ 0x8000000000000)
    (bZ : ∀ (i : Fin 5) (l : ℕ), readLimb? (src.withOffset 120) i w.mem = some l → l ≤ 0x18000000000000) :
    ∃ w' : GlobalState,
      StateT.run (runFunction (fd_ed25519_partial_dbl.denote
        (Ctxt.Valuation.ofHVector [.value src, .value t]ₕ))) w = .value ([.value t]ₕ, w')
      ∧ w'.WF ∧ (∀ b : BlockId, t.id ≠ b → w'.mem.live? b = w.mem.live? b)
      ∧ ∃ ht' : IsPointPtr w'.mem t, readPoint ht' = (readPoint hsrc).partialDbl
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? t i w'.mem = some l → l ≤ 0x18000000000000)
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 40) i w'.mem = some l → l ≤ 0x18000000000000)
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 120) i w'.mem = some l → l ≤ 0x18000000000000)
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 80) i w'.mem = some l → l ≤ 0x18000000000000) := by
  obtain ⟨oT, oZ, oY, oX, ⟨w', hrun, heq⟩, hval, cX, cY, cT, cZ⟩ :=
    fd_ed25519_partial_dbl_conforms t src w hw ht hsrc bX bY bZ
  have hpt : IsPointPtr ((((w.mem.splice (t.withOffset 80) oT).splice (t.withOffset 120) oZ).splice
      (t.withOffset 40) oY).splice t oX) t :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice ht)))
  have ht' : IsPointPtr w'.mem t := isPointPtr_of_equiv heq.symm hpt
  refine ⟨w', hrun, (wf_splice4 hw).of_equiv heq, fun b hb => ?_, ht',
    (readPoint_of_live?_eq (live?_of_equiv_mem heq.symm t.id) hpt ht').trans hval,
    bounds_of_limbs (readLimb?_of_equiv_mem heq t) (coordBounds hpt 0 t (by simp [Pointer.withOffset]) cX),
    bounds_of_limbs (readLimb?_of_equiv_mem heq _) (coordBounds hpt 1 _ rfl cY),
    bounds_of_limbs (readLimb?_of_equiv_mem heq _) (coordBounds hpt 3 _ rfl cZ.loose),
    bounds_of_limbs (readLimb?_of_equiv_mem heq _) (coordBounds hpt 2 _ rfl cT.loose)⟩
  exact (heq.live b).symm.trans ((live?_splice_ne (p := t) hb).trans
    ((live?_splice_ne (p := t.withOffset 40) hb).trans ((live?_splice_ne (p := t.withOffset 120) hb).trans
      (live?_splice_ne (p := t.withOffset 80) hb))))

/-- `add_final_mul_projective(r, t)`: `X, Y, Z` stored at `r`, tight. -/
theorem proj_step {r t : Pointer} {w : GlobalState} (hw : w.WF) (hne : r.id ≠ t.id)
    (hr : IsPointPtr w.mem r) (ht : IsPointPtr w.mem t)
    (bX : ∀ (i : Fin 5) (l : ℕ), readLimb? t i w.mem = some l → l ≤ 0x18000000000000)
    (bY : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 40) i w.mem = some l → l ≤ 0x18000000000000)
    (bZ : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 120) i w.mem = some l → l ≤ 0x18000000000000)
    (bT : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 80) i w.mem = some l → l ≤ 0x18000000000000) :
    ∃ (x y z : BitVec (5 * 64)) (w' : GlobalState),
      StateT.run (runFunction (fd_ed25519_point_add_final_mul_projective.denote
        (Ctxt.Valuation.ofHVector [.value t, .value r]ₕ))) w = .value ([.value r]ₕ, w')
      ∧ w'.WF ∧ (∀ b : BlockId, r.id ≠ b → w'.mem.live? b = w.mem.live? b)
      ∧ w'.mem.live? r.id
        = (((w.mem.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z).live? r.id
      ∧ ∃ hr' : IsPointPtr w'.mem r,
        readPoint hr' = { (readPoint ht).finalMul with T := (readPoint hr).T }
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? r i w'.mem = some l → l ≤ 0x8000000000000)
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? (r.withOffset 40) i w'.mem = some l → l ≤ 0x8000000000000)
        ∧ (∀ (i : Fin 5) (l : ℕ), readLimb? (r.withOffset 120) i w'.mem = some l → l ≤ 0x18000000000000) := by
  obtain ⟨x, y, z, ⟨w', hrun, heq⟩, hval, cX, cY, cZ⟩ :=
    fd_ed25519_point_add_final_mul_projective_conforms r t w hw hne hr ht bX bY bZ bT
  have hpt : IsPointPtr (((w.mem.splice r x).splice (r.withOffset 40) y).splice (r.withOffset 120) z) r :=
    isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr))
  have hr' : IsPointPtr w'.mem r := isPointPtr_of_equiv heq.symm hpt
  refine ⟨x, y, z, w', hrun, (wf_splice3 hw).of_equiv heq, fun b hb => ?_,
    live?_of_equiv_mem heq.symm r.id, hr',
    (readPoint_of_live?_eq (live?_of_equiv_mem heq.symm r.id) hpt hr').trans hval,
    bounds_of_limbs (readLimb?_of_equiv_mem heq r) (coordBounds hpt 0 r (by simp [Pointer.withOffset]) cX),
    bounds_of_limbs (readLimb?_of_equiv_mem heq _) (coordBounds hpt 1 _ rfl cY),
    bounds_of_limbs (readLimb?_of_equiv_mem heq _) (coordBounds hpt 3 _ rfl cZ.loose)⟩
  exact (heq.live b).symm.trans ((live?_splice_ne (p := r.withOffset 120) hb).trans
    ((live?_splice_ne (p := r.withOffset 40) hb).trans (live?_splice_ne (p := r) hb)))

/-- `add_final_mul(r, t)`: all four coordinates stored at `r`. -/
theorem final_step {r t : Pointer} {w : GlobalState} (hw : w.WF) (hne : r.id ≠ t.id)
    (hr : IsPointPtr w.mem r) (ht : IsPointPtr w.mem t)
    (bX : ∀ (i : Fin 5) (l : ℕ), readLimb? t i w.mem = some l → l ≤ 0x18000000000000)
    (bY : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 40) i w.mem = some l → l ≤ 0x18000000000000)
    (bZ : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 120) i w.mem = some l → l ≤ 0x18000000000000)
    (bT : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 80) i w.mem = some l → l ≤ 0x18000000000000) :
    ∃ (x y z v : BitVec (5 * 64)) (w' : GlobalState),
      StateT.run (runFunction (fd_ed25519_point_add_final_mul.denote
        (Ctxt.Valuation.ofHVector [.value t, .value r]ₕ))) w = .value ([.value r]ₕ, w')
      ∧ (∀ b : BlockId, r.id ≠ b → w'.mem.live? b = w.mem.live? b)
      ∧ w'.mem.live? r.id = ((((w.mem.splice r x).splice (r.withOffset 40) y).splice
          (r.withOffset 120) z).splice (r.withOffset 80) v).live? r.id
      ∧ ∃ hpt : IsPointPtr ((((w.mem.splice r x).splice (r.withOffset 40) y).splice
          (r.withOffset 120) z).splice (r.withOffset 80) v) r,
        readPoint hpt = (readPoint ht).finalMul ∧ AllLimbBounds hpt := by
  obtain ⟨x, y, z, v, ⟨w', hrun, heq⟩, hval, hb⟩ :=
    fd_ed25519_point_add_final_mul_conforms r t w hw hne hr ht bX bY bZ bT
  refine ⟨x, y, z, v, w', hrun, fun b hb => ?_, live?_of_equiv_mem heq.symm r.id, _, hval, hb⟩
  exact (heq.live b).symm.trans ((live?_splice_ne (p := r.withOffset 80) hb).trans
    ((live?_splice_ne (p := r.withOffset 120) hb).trans
      ((live?_splice_ne (p := r.withOffset 40) hb).trans (live?_splice_ne (p := r) hb))))

/-! ### The loop -/

/-- The loop header after some bodies, `Q` the point doubled so far: `t` holds
`partialDbl Q`, loose. -/
structure Inv (s : GlobalState) (r t : Pointer) (Q : Point) (u : GlobalState) : Prop where
  wf : u.WF
  frame : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ r.id → u.mem.live? b = s.mem.live? b
  cover : Covered s u r
  hr : IsPointPtr u.mem r
  ht : IsPointPtr u.mem t
  val : readPoint ht = Q.partialDbl
  bX : ∀ (i : Fin 5) (l : ℕ), readLimb? t i u.mem = some l → l ≤ 0x18000000000000
  bY : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 40) i u.mem = some l → l ≤ 0x18000000000000
  bZ : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 120) i u.mem = some l → l ≤ 0x18000000000000
  bT : ∀ (i : Fin 5) (l : ℕ), readLimb? (t.withOffset 80) i u.mem = some l → l ≤ 0x18000000000000

/-- The entry block's values, as the tail blocks read them. -/
abbrev entryVal (r a t : Pointer) (n : BitVec 32) : fd_ed25519_point_dbln.Γout.Valuation :=
  PoisonOr.value (BitVec.ofBool (BitVec.ofInt 32 1 <ₛ n)) ::ᵥ PoisonOr.value t ::ᵥ
  PoisonOr.value t ::ᵥ PoisonOr.value (BitVec.ofInt 8 1) ::ᵥ PoisonOr.value (BitVec.ofInt 32 1) ::ᵥ
  PoisonOr.value n ::ᵥ PoisonOr.value a ::ᵥ PoisonOr.value r ::ᵥ Ctxt.Valuation.nil

/-- `^bb2` with the counter at `i`. -/
abbrev hdr (i : BitVec 8) : SuccArgs fd_ed25519_point_dbln.sigs := ⟨1, by rfl, [PoisonOr.value i]ₕ⟩

/-- `^bb1`. -/
abbrev exit : SuccArgs fd_ed25519_point_dbln.sigs := ⟨0, by rfl, HVector.nil⟩

/-- Where the walk stands after `k` of `K` bodies. -/
def tgt (K k : ℕ) : SuccArgs fd_ed25519_point_dbln.sigs :=
  if k = K then exit else hdr (BitVec.ofNat 8 (k + 1))

/-- `zext` then `icmp ult` on values. -/
theorem tailEval (j : BitVec 8) (n : BitVec 32) :
    LLVM.icmp LLVM.IntPred.ult (LLVM.zext 32 (PoisonOr.value j)) (PoisonOr.value n)
    = PoisonOr.value (BitVec.ofBool (BitVec.zeroExtend 32 j <ᵤ n)) := by
  simp only [LLVM.zext, LLVM.zext?, LLVM.icmp, LLVM.icmp?, PoisonOr.value_bind,
    Bool.false_eq_true, false_and, if_false, LLVM.icmp']

/-- The `i8` counter increment, on a value. -/
theorem addEval (i : BitVec 8) :
    LLVM.add (PoisonOr.value i) (PoisonOr.value (BitVec.ofInt 8 1))
    = PoisonOr.value (i + BitVec.ofInt 8 1) := by
  simp only [LLVM.add, LLVM.add?, PoisonOr.value_bind, Bool.false_eq_true, false_and, if_false]

/-- The latch compares `k + 2` with `n`: the `i8` counter does not wrap below 255. -/
theorem latch (k : ℕ) (n : BitVec 32) (hk : k + 2 ≤ 255) :
    (BitVec.zeroExtend 32 (BitVec.ofNat 8 (k + 1) + BitVec.ofInt 8 1) <ᵤ n)
      = decide (k + 2 < n.toNat) := by
  simp [BitVec.ult]
  omega

theorem counter_succ (k : ℕ) :
    BitVec.ofNat 8 (k + 1) + BitVec.ofInt 8 1 = BitVec.ofNat 8 (k + 1 + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- One body: `add_final_mul_projective(r, t); partial_dbl(t, r)`, then the latch. -/
theorem loop_step {s : GlobalState} {r a t : Pointer} {n : BitVec 32} {P : Point} {K : ℕ}
    (hrN : r.id.id < s.alloc.nextFreeBlock) (htN : s.alloc.nextFreeBlock ≤ t.id.id)
    (h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320)
    (h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640)
    (h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960)
    (hK : K < 255) (hKn : 0 < K → K + 1 = n.toNat) :
    ∀ k u, k < K → Inv s r t (Point.dbl^[k] P) u → ∃ Vout u',
      StateT.run ((fd_ed25519_point_dbln.blocks.get (tgt K k).idx (tgt K k).hidx).2.denote
          (Ctxt.Valuation.ofHVector (tgt K k).args.reverse ++ entryVal r a t n)) u
        = .value ((Vout, .inr (tgt K (k + 1))), u')
      ∧ Inv s r t (Point.dbl^[k + 1] P) u' := by
  intro k u hk inv
  rw [show tgt K k = hdr (BitVec.ofNat 8 (k + 1)) from if_neg (Nat.ne_of_lt hk)]
  have hrt : r.id ≠ t.id := fun h => by have := congrArg BlockId.id h; omega
  obtain ⟨x, y, z, u₁, hrun₁, hu₁, hfr₁, hlr₁, hr₁, hv₁, bX₁, bY₁, bZ₁⟩ :=
    proj_step inv.wf hrt inv.hr inv.ht inv.bX inv.bY inv.bZ inv.bT
  have ht₁ : IsPointPtr u₁.mem t := isPointPtr_of_live?_eq (hfr₁ t.id hrt) inv.ht
  obtain ⟨u₂, hrun₂, hu₂, hfr₂, ht₂, hv₂, bX₂, bY₂, bZ₂, bT₂⟩ :=
    partialDbl_step hu₁ ht₁ hr₁ bX₁ bY₁ bZ₁
  have hlr₂ : u₂.mem.live? r.id = u₁.mem.live? r.id := hfr₂ r.id (Ne.symm hrt)
  refine ⟨?Vout, u₂, ?run, ?inv⟩
  case inv =>
    exact {
      wf := hu₂
      frame := fun b hb hbr =>
        (hfr₂ b (fun h => by have := congrArg BlockId.id h; omega)).trans
          ((hfr₁ b (fun h => hbr h.symm)).trans (inv.frame b hb hbr))
      cover := Covered.step h40 h80 h120 inv.cover (hlr₂.trans hlr₁)
      hr := isPointPtr_of_live?_eq hlr₂ hr₁
      ht := ht₂
      val := by rw [hv₂, hv₁, inv.val, Function.iterate_succ_apply']; rfl
      bX := bX₂, bY := bY₂, bZ := bZ₂, bT := bT₂ }
  case run =>
    dsimp only [hdr, fd_ed25519_point_dbln, Blocks.get]
    peel_call hrun₁
    peel_call hrun₂
    denote_step_all w
    denote_eval w 3 5
    simp only [simp_spine, entryVal] at hw3 hw5
    subst hw3 hw4 hw5
    simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm, tailEval,
      addEval, latch k n (by omega)]
    by_cases h : k + 1 = K
    · have hc : ¬ (k + 2 < n.toNat) := by have := hKn (by omega); omega
      rw [if_neg (show ¬ (BitVec.ofBool (decide (k + 2 < n.toNat)) = 1) by simp [hc]),
        show tgt K (k + 1) = exit from if_pos h]
      rfl
    · have hc : k + 2 < n.toNat := by have := hKn (by omega); omega
      rw [if_pos (show BitVec.ofBool (decide (k + 2 < n.toNat)) = 1 by simp [hc]),
        show tgt K (k + 1) = hdr (BitVec.ofNat 8 (k + 1 + 1)) from if_neg h, counter_succ]
      rfl

end Dbln

theorem fd_ed25519_point_dbln_conforms (r a : Pointer) (n : BitVec 32) (s : GlobalState)
    (hs : s.WF) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a)
    (haX : LimbBounds (isCoordPtr ha 0)) (haY : LimbBounds (isCoordPtr ha 1))
    (haZ : LimbBounds.Loose (isCoordPtr ha 3))
    (hn : n.toInt < 256) :
    fd_ed25519_point_dbln_spec r a n s hr ha := by
  simp only [fd_ed25519_point_dbln_spec]
  have h40 : (r.withOffset 40).offsetInBits = r.offsetInBits + 320 := by
    simpa using withOffset_offsetInBits (off := 40) (by have := hr.2; simp; omega)
  have h80 : (r.withOffset 80).offsetInBits = r.offsetInBits + 640 := by
    simpa using withOffset_offsetInBits (off := 80) (by have := hr.2; simp; omega)
  have h120 : (r.withOffset 120).offsetInBits = r.offsetInBits + 960 := by
    simpa using withOffset_offsetInBits (off := 120) (by have := hr.2; simp; omega)
  -- the doubling count
  obtain ⟨K, hKdef⟩ : ∃ K, dblnCount n - 1 = K := ⟨_, rfl⟩
  have hnc := BitVec.toInt_eq_toNat_cond n
  obtain ⟨hcount, hK, hKn⟩ : dblnCount n = K + 1 ∧ K < 255 ∧ (0 < K → K + 1 = n.toNat) := by
    have := n.isLt
    subst hKdef
    unfold dblnCount
    split <;> split at hnc <;> omega

  -- `fd_curve25519_edwards_t t[1]`
  obtain ⟨t, s₁, htdef, hs₁def, hs₁, hfit, htid, htoff, -, hfr⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (4 * 5 * 64)
  have hrN : r.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs hr.1
  have haN : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.1
  have htN : s.alloc.nextFreeBlock ≤ t.id.id := htid.ge
  have hne : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → t.id ≠ b :=
    fun b hb h => by have := congrArg BlockId.id h; omega
  have hrt : r.id ≠ t.id := fun h => hne r.id hrN h.symm
  have hla : s₁.mem.live? a.id = s.mem.live? a.id := hfr a.id (fun h => hne a.id haN h.symm)
  have hlr : s₁.mem.live? r.id = s.mem.live? r.id := hfr r.id (fun h => hne r.id hrN h.symm)
  have ht₁ : IsPointPtr s₁.mem t := ⟨hfit, by simp [htoff]⟩
  have ha₁ : IsPointPtr s₁.mem a := isPointPtr_of_live?_eq hla ha

  -- `partial_dbl(t, a)`
  obtain ⟨u₀, hrun₀, hu₀, hfr₀, ht₀, hv₀, bX₀, bY₀, bZ₀, bT₀⟩ :=
    Dbln.partialDbl_step hs₁ ht₁ ha₁
      (limbBounds_of_live?_eq (p := a) hla (Dbln.coordBounds ha 0 a (coordPtr_zero a) haX))
      (limbBounds_of_live?_eq (p := a.withOffset 40) hla (Dbln.coordBounds ha 1 _ rfl haY))
      (limbBounds_of_live?_eq (p := a.withOffset 120) hla (Dbln.coordBounds ha 3 _ rfl haZ))
  have hlr₀ : u₀.mem.live? r.id = s.mem.live? r.id := (hfr₀ r.id (Ne.symm hrt)).trans hlr
  have inv₀ : Dbln.Inv s r t (Point.dbl^[0] (readPoint ha)) u₀ := {
    wf := hu₀
    frame := fun b hb _ => (hfr₀ b (hne b hb)).trans (hfr b (fun h => hne b hb h.symm))
    cover := Dbln.Covered.of_live? hlr₀
    hr := isPointPtr_of_live?_eq hlr₀ hr
    ht := ht₀
    val := hv₀.trans (by rw [readPoint_of_live?_eq hla ha ha₁]; rfl)
    bX := bX₀, bY := bY₀, bZ := bZ₀, bT := bT₀ }

  -- the loop
  obtain ⟨uK, hloop, invK⟩ :=
    Blocks.run_loop (bs := fd_ed25519_point_dbln.blocks) (Vamb := Dbln.entryVal r a t n)
      (Inv := fun k u => Dbln.Inv s r t (Point.dbl^[k] (readPoint ha)) u) (t := Dbln.tgt K) (n := K)
      (Dbln.loop_step hrN htN h40 h80 h120 hK hKn) inv₀

  -- `add_final_mul(r, t)`
  obtain ⟨x, y, z, v, uf, hrunf, hfrf, hlrf, hpt, hvf, hbf⟩ :=
    Dbln.final_step invK.wf hrt invK.hr invK.ht invK.bX invK.bY invK.bZ invK.bT
  have hcov := invK.cover x y z v
  refine ⟨x, y, z, v, ⟨s.popFrame uf.mem, run_runFunction (s' := uf) ?run, ?equiv⟩, ?val, ?bnd⟩
  case val =>
    rw [readPoint_of_live?_eq hcov.symm hpt, hvf, invK.val, Point.finalMul_partialDbl,
      ← Function.iterate_succ_apply' Point.dbl, Point.dbln, hcount]
  case bnd =>
    exact fun i => limbBounds_of_readLimb? _
      (limbBounds_of_live?_eq hcov.symm (limbBounds_readLimb? _ (hbf i)))
  case equiv =>
    refine GlobalState.Equiv.symm (popFrame_equiv_block hs hrN
      (fun b hb hbr => (hfrf b (fun h => hbr h.symm)).trans (invK.frame b hb hbr))
      (fun b hbr => ?_) (hlrf.trans hcov))
    have hrb : r.id ≠ b := fun h => hbr h.symm
    exact (live?_splice_ne (p := r.withOffset 80) hrb).trans
      ((live?_splice_ne (p := r.withOffset 120) hrb).trans
        ((live?_splice_ne (p := r.withOffset 40) hrb).trans (live?_splice_ne (p := r) hrb)))
  case run =>
    simp only [Cfg.denote]
    denote_step_all v 1
    denote_eval v 0 1
    simp only [LLVM.const?] at hv0 hv1
    subst hv0 hv1
    peel_alloca from s as s₁ with hs₁def
    rw [← htdef]
    peel_lifetime
    peel_call hrun₀
    denote_step_all v 4
    denote_eval v 4 4
    simp only [LLVM.icmp, LLVM.icmp?, LLVM.icmp', PoisonOr.value_bind] at hv4
    subst hv4
    simp only [BlockCom.denote_term, Terminator.denote_condBr, simp_denote, simp_sllvm]
    refine Eq.trans (congrArg (fun tt => StateT.run (fd_ed25519_point_dbln.blocks.run
      (Dbln.entryVal r a t n) tt) u₀) (?_ : _ = Dbln.tgt K 0)) ?_
    · by_cases hn1 : n.toInt ≤ 1
      · have hK0 : K = 0 := by omega
        rw [if_neg (show ¬ (BitVec.ofBool (BitVec.ofInt 32 1 <ₛ n) = 1) by
          simp [BitVec.slt, show ¬ (1 < n.toInt) by omega]), show Dbln.tgt K 0 = Dbln.exit from if_pos hK0.symm]
        rfl
      · have hK0 : K ≠ 0 := by
          have := n.isLt
          simp only [dblnCount, if_neg hn1] at hcount; split at hnc <;> omega
        rw [if_pos (show BitVec.ofBool (BitVec.ofInt 32 1 <ₛ n) = 1 by
          simp [BitVec.slt, show 1 < n.toInt by omega]), show Dbln.tgt K 0 = Dbln.hdr (BitVec.ofNat 8 (0 + 1)) from
          if_neg (Ne.symm hK0)]
        rfl
    beta_reduce
    rw [hloop, show Dbln.tgt K K = Dbln.exit from if_pos rfl]
    have key : ∃ Vout, StateT.run ((fd_ed25519_point_dbln.blocks.get 0 (by rfl)).2.denote
        (Ctxt.Valuation.ofHVector (HVector.nil : HVector toType ([] : List SLLVM.Ty)).reverse
          ++ Dbln.entryVal r a t n)) uK
        = .value ((Vout, .inl [.value r]ₕ), uf) := by
      dsimp only [fd_ed25519_point_dbln, Blocks.get]
      refine ⟨?val, ?run⟩
      case run =>
        peel_call hrunf
        simp only [BlockCom.denote_var, BlockCom.denote_term, Terminator.denote_ret, simp_denote]
        rfl
    obtain ⟨Vout, hrun⟩ := key
    rw [Blocks.run_step (t := Dbln.exit)]
    dsimp only
    rw [EffectM.run_bind, hrun, PoisonOr.value_bind]
    rfl

end Firedancer.Ref
