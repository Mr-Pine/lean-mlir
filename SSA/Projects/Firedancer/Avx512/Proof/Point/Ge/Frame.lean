/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_quad_mul_fast
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# A point region's frame

`n` 64-byte slots, the out-parameters of the kernel calls; `r` the only caller
block written. `Frame n s m₁ u`: the slots are live in `u`, and below the entry
counter `u` reads as `m₁`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

namespace Ge

/-- The slot widths: all `vector<8xi64>`. -/
def cw : Nat → Nat := fun _ => 512

/-- Slot `k`, the `k`-th `alloca`. -/
def slot (s : GlobalState) (k : Nat) : Pointer := s.chainPtr cw k

@[simp] theorem slot_id (s : GlobalState) (k : Nat) :
    (slot s k).id.id = s.alloc.nextFreeBlock + k := GlobalState.chainPtr_id k

theorem slot_ne {s : GlobalState} {i j : Nat} (h : i ≠ j) : (slot s i).id ≠ (slot s j).id :=
  fun e => h (by have := congrArg BlockId.id e; simp only [slot_id] at this; omega)

structure Frame (n : Nat) (s : GlobalState) (m₁ : MemoryState) (u : GlobalState) : Prop where
  wf : u.WF
  counter : u.alloc.nextFreeBlock = s.alloc.nextFreeBlock + n
  slots : ∀ k, k < n → Fits u.mem (slot s k) 512
  below : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → u.mem.live? b = m₁.live? b

/-- `n` `alloca`s set the frame up. -/
theorem frame_allocaChain {s : GlobalState} (hs : s.WF) (n : Nat) :
    Frame n s s.mem (s.allocaChain cw n) where
  wf := GlobalState.WF.allocaChain hs n
  counter := GlobalState.nextFreeBlock_allocaChain n
  slots := fun _ hk => GlobalState.fits_chainPtr hk
  below := FrameBelow.allocaChain (le_refl _) (FrameBelow.refl _ _) n

/-- A store below the counter to `p`, mirrored in `m₁`. -/
theorem Frame.splice {n : Nat} {s : GlobalState} {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame n s m₁ u)
    (p : Pointer) {w : Nat} (x : BitVec w) :
    Frame n s (m₁.splice p x) { u with mem := u.mem.splice p x } where
  wf := hF.wf.splice
  counter := hF.counter
  slots := fun k hk => fits_splice (hF.slots k hk)
  below := fun b hb => by
    by_cases hpb : p.id = b
    · subst hpb; exact live?_splice_congr (hF.below _ hb)
    · rw [live?_splice_ne hpb, live?_splice_ne hpb]; exact hF.below b hb

/-- The popped frame of a callee that wrote three slots. -/
theorem Frame.call {n : Nat} {s : GlobalState} {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame n s m₁ u)
    (i j k : Nat) (a b c : Vector (BitVec 64) 8) :
    Frame n s m₁ (u.popFrame (((u.mem.writeVec (slot s i) a).writeVec (slot s j) b).writeVec
      (slot s k) c)) where
  wf := fun q hq => live?_killFrom_of_le hq
  counter := hF.counter
  slots := fun l hl => by
    refine fits_of_live?_eq (live?_killFrom_of_lt ?_) ?_
    · show (slot s l).id.id < u.alloc.nextFreeBlock
      rw [slot_id, hF.counter]; omega
    · simp only [MemoryState.writeVec]
      exact fits_splice (fits_splice (fits_splice (hF.slots l hl)))
  below := fun q hq => by
    have ne : ∀ l, (slot s l).id ≠ q := fun l e => by
      have := congrArg BlockId.id e; simp only [slot_id] at this; omega
    show (MemoryState.killFrom u.alloc.nextFreeBlock _).live? q = _
    rw [live?_killFrom_of_lt (by rw [hF.counter]; omega)]
    simp only [MemoryState.writeVec]
    rw [live?_splice_ne (ne k), live?_splice_ne (ne j), live?_splice_ne (ne i)]
    exact hF.below q hq

theorem isVecPtr_slot {n : Nat} {s : GlobalState} {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame n s m₁ u)
    {k : Nat} (hk : k < n) : IsVecPtr u.mem (slot s k) :=
  ⟨hF.slots k hk, by simp [slot, GlobalState.chainPtr]⟩

/-- A slot a callee wrote last reads back what it wrote, across the frame pop. -/
theorem readVec_call {n : Nat} {s : GlobalState} {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame n s m₁ u)
    {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (a b c : Vector (BitVec 64) 8) :
    let u' := u.popFrame (((u.mem.writeVec (slot s i) a).writeVec (slot s j) b).writeVec
      (slot s k) c)
    ∀ (hpi : IsVecPtr u'.mem (slot s i)) (hpj : IsVecPtr u'.mem (slot s j))
      (hpk : IsVecPtr u'.mem (slot s k)),
      readVec hpi = a ∧ readVec hpj = b ∧ readVec hpk = c := by
  intro u' hpi hpj hpk
  have lt : ∀ l, l < n → (slot s l).id.id < u.alloc.nextFreeBlock := fun l hl => by
    rw [slot_id, hF.counter]; omega
  have kill : ∀ l, l < n → u'.mem.live? (slot s l).id
      = (((u.mem.writeVec (slot s i) a).writeVec (slot s j) b).writeVec (slot s k) c).live?
          (slot s l).id := fun l hl => live?_killFrom_of_lt (lt l hl)
  simp only [MemoryState.writeVec] at kill
  refine ⟨readVec_eq_of ?_, readVec_eq_of ?_, readVec_eq_of ?_⟩
  · rw [readVec?_of_live?_eq (kill i hi), readVec?_splice_ne (slot_ne hik.symm),
      readVec?_splice_ne (slot_ne hij.symm)]
    exact readVec?_splice_self a (isVecPtr_slot hF hi)
  · rw [readVec?_of_live?_eq (kill j hj), readVec?_splice_ne (slot_ne hjk.symm)]
    exact readVec?_splice_self b ⟨fits_splice (hF.slots j hj), (isVecPtr_slot hF hj).2⟩
  · rw [readVec?_of_live?_eq (kill k hk)]
    exact readVec?_splice_self c ⟨fits_splice (fits_splice (hF.slots k hk)),
      (isVecPtr_slot hF hk).2⟩

/-- **One `fd_r43x6_quad_sqr_fast` call into slots `i, j, k`**, with its readback. -/
theorem sqr_step {n : Nat} {s : GlobalState} {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame n s m₁ u)
    (x : Quad) (hx : R43x6.U47 x.v03 ∧ R43x6.U47 x.v14 ∧ R43x6.U47 x.v25)
    {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {P : Prop}
    (kont : ∀ u' : GlobalState,
      StateT.run (runFunction ((Cfg.ofCom fd_r43x6_quad_sqr_fast).denote
          (Ctxt.Valuation.ofHVector [x.v25.map PoisonOr.value, x.v14.map PoisonOr.value,
            x.v03.map PoisonOr.value, PoisonOr.value (slot s k), PoisonOr.value (slot s j),
            PoisonOr.value (slot s i)]ₕ))) u = .value (.nil, u') →
      Frame n s m₁ u' →
      ∀ (hpi : IsVecPtr u'.mem (slot s i)) (hpj : IsVecPtr u'.mem (slot s j))
        (hpk : IsVecPtr u'.mem (slot s k)),
        readVec hpi = (quadSqrResult x).v03 → readVec hpj = (quadSqrResult x).v14 →
        readVec hpk = (quadSqrResult x).v25 → P) : P := by
  have hF' := hF.call i j k (quadSqrResult x).v03 (quadSqrResult x).v14 (quadSqrResult x).v25
  obtain ⟨ri, rj, rk⟩ := readVec_call hF hi hj hk hij hik hjk (quadSqrResult x).v03
    (quadSqrResult x).v14 (quadSqrResult x).v25 (isVecPtr_slot hF' hi) (isVecPtr_slot hF' hj)
    (isVecPtr_slot hF' hk)
  refine kont _ ?_ hF' _ _ _ ri rj rk
  rw [Cfg.denote_ofCom]
  refine run_runFunction (s' := { u with
    mem := ((u.mem.writeVec (slot s i) (quadSqrResult x).v03).writeVec (slot s j)
      (quadSqrResult x).v14).writeVec (slot s k) (quadSqrResult x).v25 }) ?_
  exact run_fd_r43x6_quad_sqr_fast x hx.1 hx.2.1 hx.2.2 _ _ _ u (hF.slots i hi)
    (fits_splice (hF.slots j hj)) (fits_splice (fits_splice (hF.slots k hk)))

/-- **One `fd_r43x6_quad_mul_fast` call into slots `i, j, k`**, with its readback. -/
theorem mul_step {n : Nat} {s : GlobalState} {m₁ : MemoryState} {u : GlobalState}
    (hF : Frame n s m₁ u)
    (x y : Quad) (hx : R43x6.U47 x.v03 ∧ R43x6.U47 x.v14 ∧ R43x6.U47 x.v25)
    (hy : R43x6.U47 y.v03 ∧ R43x6.U47 y.v14 ∧ R43x6.U47 y.v25)
    {i j k : Nat} (hi : i < n) (hj : j < n) (hk : k < n) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {P : Prop}
    (kont : ∀ u' : GlobalState,
      StateT.run (runFunction ((Cfg.ofCom fd_r43x6_quad_mul_fast).denote
          (Ctxt.Valuation.ofHVector [y.v25.map PoisonOr.value, y.v14.map PoisonOr.value,
            y.v03.map PoisonOr.value, x.v25.map PoisonOr.value, x.v14.map PoisonOr.value,
            x.v03.map PoisonOr.value, PoisonOr.value (slot s k), PoisonOr.value (slot s j),
            PoisonOr.value (slot s i)]ₕ))) u = .value (.nil, u') →
      Frame n s m₁ u' →
      ∀ (hpi : IsVecPtr u'.mem (slot s i)) (hpj : IsVecPtr u'.mem (slot s j))
        (hpk : IsVecPtr u'.mem (slot s k)),
        readVec hpi = (quadMulResult x y).v03 → readVec hpj = (quadMulResult x y).v14 →
        readVec hpk = (quadMulResult x y).v25 → P) : P := by
  have hF' := hF.call i j k (quadMulResult x y).v03 (quadMulResult x y).v14
    (quadMulResult x y).v25
  obtain ⟨ri, rj, rk⟩ := readVec_call hF hi hj hk hij hik hjk (quadMulResult x y).v03
    (quadMulResult x y).v14 (quadMulResult x y).v25 (isVecPtr_slot hF' hi)
    (isVecPtr_slot hF' hj) (isVecPtr_slot hF' hk)
  refine kont _ ?_ hF' _ _ _ ri rj rk
  rw [Cfg.denote_ofCom]
  refine run_runFunction (s' := { u with
    mem := ((u.mem.writeVec (slot s i) (quadMulResult x y).v03).writeVec (slot s j)
      (quadMulResult x y).v14).writeVec (slot s k) (quadMulResult x y).v25 }) ?_
  exact run_fd_r43x6_quad_mul_fast x y hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2 _ _ _ u
    (hF.slots i hi) (fits_splice (hF.slots j hj)) (fits_splice (fits_splice (hF.slots k hk)))

/-! ## `r`'s block -/

theorem live?_writeQuad_ne {m : MemoryState} {p : Pointer} {q : Quad} {b : BlockId}
    (h : p.id ≠ b) : (m.writeQuad p q).live? b = m.live? b := by
  simp only [MemoryState.writeQuad]
  rw [live?_splice_ne (p := p.withOffset 128) h, live?_splice_ne (p := p.withOffset 64) h,
    live?_splice_ne h]

/-- `writeQuad` looks only at `p`'s block. -/
theorem live?_writeQuad_congr {m₁ m₂ : MemoryState} {p : Pointer} (q : Quad)
    (h : m₁.live? p.id = m₂.live? p.id) :
    (m₁.writeQuad p q).live? p.id = (m₂.writeQuad p q).live? p.id := by
  simp only [MemoryState.writeQuad]
  exact live?_splice_congr (p := p.withOffset 128) (live?_splice_congr (p := p.withOffset 64)
    (live?_splice_congr h))

private theorem spliceBits_quad {n : Nat} (bytes : BitVec n) (o : Nat) (a b c : BitVec 512) :
    spliceBits (spliceBits (spliceBits bytes o a) (o + 512) b) (o + 1024) c
      = spliceBits bytes o (c ++ b ++ a) := by
  rw [spliceBits_append, spliceBits_append]

/-- **The second `writeQuad` hides the first**: three stores at `0`, `64` and `128` bytes
cover the whole QUAD. -/
theorem live?_writeQuad_writeQuad {m : MemoryState} {p : Pointer} (q₁ q₂ : Quad)
    (hp : p.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64) :
    ((m.writeQuad p q₁).writeQuad p q₂).live? p.id = (m.writeQuad p q₂).live? p.id := by
  have h64 : (p.withOffset 64).offsetInBits = p.offsetInBits + 512 := by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (64 : BitVec 64).toNat = 64 from rfl]; omega
  have h128 : (p.withOffset 128).offsetInBits = p.offsetInBits + 1024 := by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (128 : BitVec 64).toNat = 128 from rfl]; omega
  have hw : ∀ (m : MemoryState) (q : Quad),
      (m.writeQuad p q).live? p.id = (m.live? p.id).map fun blk =>
        ({ length := blk.length,
           bytes := spliceBits blk.bytes p.offsetInBits
             (vecBV q.v25 ++ vecBV q.v14 ++ vecBV q.v03) }
          : LiveBlock) := by
    intro m q
    cases hb : m.live? p.id with
    | none =>
      simp only [MemoryState.writeQuad, Option.map_none]
      exact splicedDead (p := p.withOffset 128) (splicedDead (p := p.withOffset 64)
        (splicedDead hb))
    | some blk =>
      have e1 := splicedLive m p blk hb (vecBV q.v03)
      have e2 := splicedLive _ (p.withOffset 64) _ e1 (vecBV q.v14)
      have e3 := splicedLive _ (p.withOffset 128) _ e2 (vecBV q.v25)
      simp only [MemoryState.writeQuad, Option.map_some]
      refine e3.trans ?_
      simp only [h64, h128, spliceBits_quad]
  rw [hw, hw, hw]
  cases m.live? p.id <;> simp [spliceBits_spliceBits_self]

/-! ## `a`'s three vectors -/

theorem offsetInBits_withOffset {p : Pointer} (hp : p.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64)
    {o : ℕ} (ho : o ≤ 128) :
    (p.withOffset (BitVec.ofNat 64 o)).offsetInBits = p.offsetInBits + 8 * o := by
  simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The QUAD `writeQuad` stored reads back. -/
theorem readQuad_writeQuad {m : MemoryState} {p : Pointer} {q : Quad}
    (hp : IsQuadPtr m p) (h : IsQuadPtr (m.writeQuad p q) p) : readQuad h = q := by
  obtain ⟨⟨blk, hblk, hlen⟩, hnw⟩ := hp
  simp only [LiveBlock.lengthInBits] at hlen
  have hl : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  have off64 := offsetInBits_withOffset (p := p) hnw (o := 64) (by omega)
  have off128 := offsetInBits_withOffset (p := p) hnw (o := 128) (by omega)
  have h1 := splicedLive m p blk hl (vecBV q.v03)
  have h2 : ((m.splice p (vecBV q.v03)).splice (p.withOffset 64) (vecBV q.v14)).live? p.id
      = some { length := blk.length,
               bytes := spliceBits (spliceBits blk.bytes p.offsetInBits (vecBV q.v03))
                 (p.offsetInBits + 512) (vecBV q.v14) } := by
    have e := splicedLive _ (p.withOffset 64) _ h1 (vecBV q.v14)
    rwa [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, off64] at e
  have h3 : (m.writeQuad p q).live? p.id
      = some { length := blk.length,
               bytes := spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits
                 (vecBV q.v03)) (p.offsetInBits + 512) (vecBV q.v14))
                 (p.offsetInBits + 1024) (vecBV q.v25) } := by
    have e := splicedLive _ (p.withOffset 128) _ h2 (vecBV q.v25)
    rwa [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, off128] at e
  have w25 : (spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits (vecBV q.v03))
        (p.offsetInBits + 512) (vecBV q.v14))
        (p.offsetInBits + 1024) (vecBV q.v25)).extractLsb' (p.offsetInBits + 1024) 512
      = vecBV q.v25 :=
    extractLsb'_spliceBits _ _ _ (by omega)
  have w14 : (spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits (vecBV q.v03))
        (p.offsetInBits + 512) (vecBV q.v14))
        (p.offsetInBits + 1024) (vecBV q.v25)).extractLsb' (p.offsetInBits + 512) 512
      = vecBV q.v14 := by
    rw [extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega)),
      extractLsb'_spliceBits _ _ _ (by omega)]
  have w03 : (spliceBits (spliceBits (spliceBits blk.bytes p.offsetInBits (vecBV q.v03))
        (p.offsetInBits + 512) (vecBV q.v14))
        (p.offsetInBits + 1024) (vecBV q.v25)).extractLsb' p.offsetInBits 512
      = vecBV q.v03 := by
    rw [extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega)),
      extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega)),
      extractLsb'_spliceBits _ _ _ (by omega)]
  have mapInj : ∀ {u v : Vector (BitVec 64) 8},
      u.map PoisonOr.value = v.map PoisonOr.value → u = v := by
    intro u v huv
    refine Vector.ext fun i hi => ?_
    have e : (u.map PoisonOr.value)[i] = (v.map PoisonOr.value)[i] := by rw [huv]
    simpa using e
  refine Quad.ext ?_ ?_ ?_
  · have hu := unflatten_readQuad_v03 h h3
    rw [w03, unflatten_vecBV] at hu
    exact (mapInj hu).symm
  · have hu := unflatten_readQuad_v14 h h3
    rw [w14, unflatten_vecBV] at hu
    exact (mapInj hu).symm
  · have hu := unflatten_readQuad_v25 h h3
    rw [w25, unflatten_vecBV] at hu
    exact (mapInj hu).symm

/-- A slot-sized read at `a`, `a + 64`, `a + 128` of a memory agreeing with `m` on `a`'s
block reads `readQuad`'s three vectors. -/
theorem readVec_quad {m m' : MemoryState} {a : Pointer} (ha : IsQuadPtr m a)
    (hl : m'.live? a.id = m.live? a.id) :
    (∀ hp : IsVecPtr m' a, readVec hp = (readQuad ha).v03)
      ∧ (∀ hp : IsVecPtr m' (a.withOffset 64), readVec hp = (readQuad ha).v14)
      ∧ (∀ hp : IsVecPtr m' (a.withOffset 128), readVec hp = (readQuad ha).v25) := by
  obtain ⟨blk, hblk, -⟩ := ha.1
  have hlive : m.live? a.id = some blk := by simp only [MemoryState.live?, hblk]
  have h64 := offsetInBits_withOffset (p := a) ha.2 (o := 64) (by omega)
  have h128 := offsetInBits_withOffset (p := a) ha.2 (o := 128) (by omega)
  have hq : readQuad ha =
      ⟨Vector.ofFn fun j => blk.bytes.extractLsb' (a.offsetInBits + 64 * j.val) 64,
      Vector.ofFn fun j => blk.bytes.extractLsb' (a.offsetInBits + 512 + 64 * j.val) 64,
      Vector.ofFn fun j => blk.bytes.extractLsb' (a.offsetInBits + 1024 + 64 * j.val) 64⟩ := by
    simp [readQuad, readQuad?, hlive]
  refine ⟨fun hp => readVec_eq_of ?_, fun hp => readVec_eq_of ?_, fun hp => readVec_eq_of ?_⟩
  · simp [readVec?, hl, hlive, hq]
  · have hl' : m'.live? (a.withOffset (BitVec.ofNat 64 64)).id = some blk := hl.trans hlive
    simp [readVec?, hl', hq, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, h64]
  · have hl' : m'.live? (a.withOffset (BitVec.ofNat 64 128)).id = some blk := hl.trans hlive
    simp [readVec?, hl', hq, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, h128]

/-- Fold a pointer the `alloca` prologue leaves expanded back to `slot s k`. -/
theorem slot_eq (s : GlobalState) (k : Nat) :
    (⟨⟨(s.allocaChain cw k).alloc.nextFreeBlock⟩, 0⟩ : Pointer) = slot s k := rfl

/-! ## Stores and loads through ambient pointers

`GeDecode2.peel_store_amb`/`peel_load_vec_amb`, restated: a tail block's
operands resolve in two passes, the block's spine and then the ambient facts. -/

macro "ge_store_amb " x:term ", " p:term ", " hp:term ", " st:term
    " as " st':term " := " hst':term " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_nil (s' := $st')
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_store (t := .vector 8 (.bitvec (.concrete 64)))
            (x := ($x).map PoisonOr.value) (flatten_vecBV $x)
            (show Fits (($st).mem) $p 512 from Fits.mono $hp (by omega)))]
          rw [$hst':term]
          rfl)]))

macro "ge_load_amb " v:term ", " p:term ", " hp:term ", " hval:term ", " st:term
    " with " l:term,+ : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_value (x := ($v).map PoisonOr.value) (s' := $st)
      (by try simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          try simp only [$[$l:term],*]
          rw [run_liftM (run_load (t := .vector 8 (.bitvec (.concrete 64)))
            (($hp).1.choose_spec.1)
            (by have := ($hp).1.choose_spec.2
                show ($p).offsetInBits + 512 ≤ _
                simp only [LiveBlock.lengthInBits] at *
                omega))]
          rw [unflatten_readVec $hp (live?_of_getElem? ($hp).1.choose_spec.1), $hval:term]
          rfl)]))

theorem fits_field {m : MemoryState} {r : Pointer} (hr : IsQuadPtr m r) :
    Fits m r 512 ∧ Fits m (r.withOffset 64) 512 ∧ Fits m (r.withOffset 128) 512 :=
  ⟨Fits.mono hr.1 (by omega), Fits.mono (remainingFits m r hr.1 64 (by simp)) (by simp),
    Fits.mono (remainingFits m r hr.1 128 (by simp)) (by simp)⟩

/-- The frame pop leaves the caller's memory with one `writeQuad` into `r`. -/
theorem popFrame_equiv {s u : GlobalState} (hs : s.WF) {r : Pointer}
    (hrlt : r.id.id < s.alloc.nextFreeBlock) {n : Nat} {m₁ : MemoryState} {q : Quad}
    (hF : Frame n s m₁ u)
    (hm : ∀ b, b ≠ r.id → m₁.live? b = s.mem.live? b)
    (hmr : m₁.live? r.id = (s.mem.writeQuad r q).live? r.id) :
    ({ s with mem := s.mem.writeQuad r q } : GlobalState) ≈ s.popFrame u.mem :=
  GlobalState.Equiv.symm (popFrame_equiv_block hs hrlt
    (fun b hb hne => (hF.below b hb).trans (hm b hne))
    (fun _ hne => live?_writeQuad_ne (Ne.symm hne))
    ((hF.below r.id hrlt).trans hmr))

/-! ## Reading and rewriting a QUAD -/

/-- A whole-QUAD store, as one splice of `p`'s block. -/
theorem live?_writeQuad {m : MemoryState} {p : Pointer} (hp : p.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64)
    (q : Quad) :
    (m.writeQuad p q).live? p.id = (m.live? p.id).map fun blk =>
        ({ length := blk.length,
           bytes := spliceBits blk.bytes p.offsetInBits
             (vecBV q.v25 ++ (vecBV q.v14 ++ vecBV q.v03)) } : LiveBlock) := by
  have h64 : (p.withOffset 64).offsetInBits = p.offsetInBits + 512 := by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (64 : BitVec 64).toNat = 64 from rfl]; omega
  have h128 : (p.withOffset 128).offsetInBits = p.offsetInBits + 1024 := by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      show (128 : BitVec 64).toNat = 128 from rfl]; omega
  cases hb : m.live? p.id with
  | none =>
    simp only [MemoryState.writeQuad, Option.map_none]
    exact splicedDead (p := p.withOffset 128) (splicedDead (p := p.withOffset 64)
      (splicedDead hb))
  | some blk =>
    have e1 := splicedLive m p blk hb (vecBV q.v03)
    have e2 := splicedLive _ (p.withOffset 64) _ e1 (vecBV q.v14)
    have e3 := splicedLive _ (p.withOffset 128) _ e2 (vecBV q.v25)
    simp only [MemoryState.writeQuad, Option.map_some]
    refine e3.trans ?_
    simp only [h64, h128, spliceBits_append]

theorem wf_writeQuad {t : GlobalState} {p : Pointer} {q : Quad} (ht : t.WF) :
    ({ t with mem := t.mem.writeQuad p q } : GlobalState).WF :=
  fun b hb => live?_splice_eq_none (live?_splice_eq_none (live?_splice_eq_none (ht b hb)))

theorem isQuadPtr_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (h : m'.live? p.id = m.live? p.id) (hp : IsQuadPtr m p) : IsQuadPtr m' p :=
  ⟨fits_of_live?_eq h hp.1, hp.2⟩

/-- Two memories reading the same QUAD at `p` read the same `readQuad`. -/
theorem readQuad_congr {m m' : MemoryState} {p : Pointer} (e : readQuad? p m' = readQuad? p m)
    (h : IsQuadPtr m p) (h' : IsQuadPtr m' p) : readQuad h' = readQuad h :=
    by
  simp only [readQuad, e]

/-- A store at or past `p`'s end leaves the QUAD at `p`. -/
theorem readQuad?_splice_of_le {m : MemoryState} {p q : Pointer} {w : ℕ} {x : BitVec w}
    (h : p.offsetInBits + 3 * 8 * 64 ≤ q.offsetInBits) :
    readQuad? p (m.splice q x) = readQuad? p m := by
  by_cases hid : q.id = p.id
  · rcases hb : m.live? q.id with _ | blk
    · have e := splicedDead (x := x) hb
      rw [hid] at e hb
      simp [readQuad?, e, hb]
    · have e := splicedLive m q blk hb x
      rw [hid] at e hb
      simp only [readQuad?, e, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      refine congrArg some (Quad.ext ?_ ?_ ?_) <;> refine Vector.ext fun j hj => ?_ <;>
        simp only [Vector.getElem_ofFn, Fin.toNat_eq_val, Fin.val_zero, Fin.val_one,
          Fin.val_two] <;>
        exact extractLsb'_spliceBits_of_disjoint _ _ _ _ (Or.inl (by omega))
  · simp only [readQuad?, live?_splice_ne hid]

/-- A `writeQuad` at or past `p`'s end leaves the QUAD at `p`. -/
theorem readQuad?_writeQuad_of_le {m : MemoryState} {p q : Pointer} {v : Quad}
    (hq : q.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64) (h : p.offsetInBits + 3 * 8 * 64 ≤ q.offsetInBits) :
    readQuad? p (m.writeQuad q v) = readQuad? p m := by
  have h64 := Ge.offsetInBits_withOffset (p := q) hq (o := 64) (by omega)
  have h128 := Ge.offsetInBits_withOffset (p := q) hq (o := 128) (by omega)
  simp only [MemoryState.writeQuad]
  rw [readQuad?_splice_of_le (q := q.withOffset 128) (by
      rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, h128]; omega),
    readQuad?_splice_of_le (q := q.withOffset 64) (by
      rw [show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, h64]; omega),
    readQuad?_splice_of_le h]

/-- A splice depends only on the bits spliced. -/
theorem spliceBits_congr_getLsbD {n w w' : ℕ} (bytes : BitVec n) (o : ℕ) {x : BitVec w}
    {y : BitVec w'} (hw : w = w') (h : ∀ i, x.getLsbD i = y.getLsbD i) :
    spliceBits bytes o x = spliceBits bytes o y := by
  subst hw; rw [BitVec.eq_of_getLsbD_eq fun i _ => h i]

theorem getLsbD_BV (q : Quad) (i : ℕ) :
    q.BV.getLsbD i = (vecBV q.v25 ++ (vecBV q.v14 ++ vecBV q.v03)).getLsbD i := by
  rw [Quad.BV_append]
  simp only [BitVec.getLsbD_append]
  split_ifs <;> first | omega | with_reducible rfl |
    rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)] | rw [Nat.sub_sub]

/-- `set_zero`'s single store is a `writeQuad`. -/
theorem live?_splice_BV {m : MemoryState} {p : Pointer} (hp : p.offset.toNat + 3 * 8 * 8 ≤ 2 ^ 64)
    (q : Quad) (b : BlockId) : (m.splice p q.BV).live? b = (m.writeQuad p q).live? b := by
  by_cases hb : p.id = b
  · subst hb
    rw [live?_writeQuad hp q]
    rcases h : m.live? p.id with _ | blk
    · exact splicedDead h
    · refine (splicedLive m p blk h q.BV).trans (congrArg some ?_)
      show ({ length := blk.length, bytes := spliceBits blk.bytes p.offsetInBits q.BV } : LiveBlock)
        = { length := blk.length,
            bytes := spliceBits blk.bytes p.offsetInBits (vecBV q.v25 ++ (vecBV q.v14 ++ vecBV q.v03)) }
      rw [spliceBits_congr_getLsbD _ _ rfl (getLsbD_BV q)]
  · rw [live?_splice_ne hb, live?_writeQuad_ne hb]

/-- A lane of a flattened vector, bit by bit. -/
theorem getLsbD_vecBV (v : Vector (BitVec 64) 8) {k : ℕ} (hk : k < 512) :
    (vecBV v).getLsbD k = (v[k / 64]'(by omega)).getLsbD (k % 64) := by
  have := congrArg (fun z : BitVec 64 => z.getLsbD (k % 64)) (extractLsb'_vecBV v (k / 64) (by omega))
  simp only [BitVec.getLsbD_extractLsb', Nat.div_add_mod' k 64,
    decide_eq_true (Nat.mod_lt k (show 64 > 0 by omega)), Bool.true_and] at this
  exact this

/-- Storing a QUAD's own vectors back changes nothing. -/
theorem live?_writeQuad_readQuad {m : MemoryState} {r : Pointer} (hr : IsQuadPtr m r) :
    (m.writeQuad r (readQuad hr)).live? r.id = m.live? r.id := by
  have ⟨⟨blk, hblk, hlen⟩, hoff⟩ := hr
  have hl : m.live? r.id = some blk := by simp only [MemoryState.live?, hblk]
  have hq : readQuad hr =
      ⟨Vector.ofFn fun j => blk.bytes.extractLsb' (r.offsetInBits + 64 * j.val) 64,
      Vector.ofFn fun j => blk.bytes.extractLsb' (r.offsetInBits + 512 + 64 * j.val) 64,
      Vector.ofFn fun j => blk.bytes.extractLsb' (r.offsetInBits + 1024 + 64 * j.val) 64⟩ := by
    simp [readQuad, readQuad?, hl]
  rw [live?_writeQuad hoff, hl, Option.map_some, hq]
  congr 1
  show _ = ({ length := blk.length, bytes := blk.bytes } : LiveBlock)
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getLsbD_spliceBits]
  split_ifs with h
  · simp only [BitVec.getLsbD_append]
    split_ifs <;>
      rw [getLsbD_vecBV _ (by omega), Vector.getElem_ofFn, BitVec.getLsbD_extractLsb'] <;>
      simp only [decide_eq_true (Nat.mod_lt _ (show 64 > 0 by omega)), Bool.true_and] <;>
      exact congrArg _ (by omega)
  · rfl

end Ge

end Firedancer.Avx512
