/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_repsqr_mul2
import SSA.Projects.Firedancer.Avx512.Proof.Quad

/-!
# One `fd_r43x6_repsqr_mul2` call, peeled

The `Ref/Proof/Step/` shape again, for the ladder `fd_r43x6_pow22523_2` and
`fd_r43x6_invert` are built from. Unlike `fd_r43x6_sqr_fast` this kernel is
impure -- it writes through *two* `wwl_t *` out-parameters -- so it needs the
ref's `Wrote₂` treatment: what the call leaves at the two destinations, and
that it left everything else alone.

`Wrote2` is stated over `readVec`, which needs three transport lemmas that did
not exist: a slot the call did not touch reads the same, and a slot it did
reads back what was spliced. They are the vector counterparts of
`readWord?_splice_ne`/`_self` in `Proof/Memory.lean` and belong beside them;
they are here while `readVec` has only this one user.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## Reading a `wwl_t` slot across a call -/

/-- A slot in a state that agrees on its block reads the same. -/
theorem readVec?_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (hl : m'.live? p.id = m.live? p.id) : readVec? p m' = readVec? p m := by
  simp only [readVec?, hl]

/-- A slot the call did not write reads the same. -/
theorem readVec?_splice_ne {m : MemoryState} {p q : Pointer} {w : Nat} {x : BitVec w}
    (hq : q.id ≠ p.id) : readVec? p (m.splice q x) = readVec? p m :=
  readVec?_of_live?_eq (live?_splice_ne hq)

/-- ... and one it did reads back what was written, provided the slot fits. -/
theorem readVec?_splice_self {m : MemoryState} {p : Pointer} (v : Vector (BitVec 64) 8)
    (hp : IsVecPtr m p) : readVec? p (m.splice p (vecBV v)) = some v := by
  obtain ⟨⟨blk, hblk, hlen⟩, hoff⟩ := hp
  have hlive : m.live? p.id = some blk := by simp only [MemoryState.live?, hblk]
  have hbits : p.offsetInBits + 512 ≤ 8 * blk.length := by
    simpa [LiveBlock.lengthInBits] using hlen
  simp [readVec?, splicedLive m p blk hlive (vecBV v)]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  rw [extractLsb'_spliceBits_of_subrange blk.bytes p.offsetInBits (p.offsetInBits + 64 * j)
      (vecBV v) (by omega) (by omega) (by omega),
    show p.offsetInBits + 64 * j - p.offsetInBits = j * 64 from by omega,
    extractLsb'_vecBV v j hj]

/-- The `readVec` forms of the two above, with the `IsVecPtr` witness carried. -/
theorem readVec_of_live?_eq {m m' : MemoryState} {p : Pointer}
    (hl : m'.live? p.id = m.live? p.id) (hp : IsVecPtr m p) :
    ∃ h' : IsVecPtr m' p, readVec h' = readVec hp :=
  ⟨⟨fits_of_live?_eq hl hp.1, hp.2⟩, by
    simp only [readVec, readVec?_of_live?_eq hl]⟩

theorem readVec_eq_of {m : MemoryState} {p : Pointer} {h : IsVecPtr m p}
    {v : Vector (BitVec 64) 8} (hv : readVec? p m = some v) : readVec h = v := by
  simp only [readVec, hv, Option.get_some]

/-! ## What one call leaves -/

/-- The state half of a peeled `fd_r43x6_repsqr_mul2( da, _, _, db, _, _, n )`:
the two destinations hold `va`/`vb` with the `u44` limbs `FD_R43X6_MUL2_INL`
leaves, and every block but those two reads as it did before the call.

`z6`/`z7` are not fields: the fold zeroes both lanes unconditionally, so
`foldVec_getElem_six`/`_seven` give them for free wherever the next kernel's
contract asks. -/
structure Wrote2 (da db : Pointer) (va vb : Vector (BitVec 64) 8)
    (u u' : GlobalState) : Prop where
  wf : u'.WF
  /-- The symbol table is untouched: `runFunction` restores it. -/
  globals : u'.globals = u.globals
  /-- Only the two destinations moved. -/
  other : ∀ c : BlockId, c ≠ da.id → c ≠ db.id → u'.mem.live? c = u.mem.live? c
  ptrA : IsVecPtr u'.mem da
  ptrB : IsVecPtr u'.mem db
  valA : readVec ptrA = va
  valB : readVec ptrB = vb
  u44A : R43x6.U44 (va.take R43x6.limbCount)
  u44B : R43x6.U44 (vb.take R43x6.limbCount)

namespace Wrote2

variable {da db : Pointer} {va vb : Vector (BitVec 64) 8} {u u' : GlobalState}

/-- A slot the call did not write keeps its contents, `IsVecPtr` witness and
all. This is what carries the ladder's earlier rungs across a later call. -/
theorem survive (w : Wrote2 da db va vb u u') {r : Pointer}
    (hra : r.id ≠ da.id) (hrb : r.id ≠ db.id) (h : IsVecPtr u.mem r) :
    ∃ h' : IsVecPtr u'.mem r, readVec h' = readVec h :=
  readVec_of_live?_eq (w.other r.id hra hrb) h

/-- ... and the frame condition extends across it. -/
theorem frameBelow {n₀ : Nat} {s : GlobalState} (w : Wrote2 da db va vb u u')
    (hda : n₀ ≤ da.id.id) (hdb : n₀ ≤ db.id.id) (hf : FrameBelow n₀ s u) :
    FrameBelow n₀ s u' :=
  fun c hc => (w.other c (fun h => absurd hc (by rw [h]; omega))
    (fun h => absurd hc (by rw [h]; omega))).trans (hf c hc)

end Wrote2

/-! ## The call -/

/-- **One `fd_r43x6_repsqr_mul2` call**, in the form `peel_call_nil` takes it:
the run equation, and a `Wrote2` holding `[xa^(2^n)] ya` and `[xb^(2^n)] yb`.

`n` arrives as the `i64` the region's constant supplies, so the exponent comes
out as `n.toNat`; every call site here has a literal, and `hn63` is a `decide`
there.

The `[6]`/`[7]` hypotheses are `fd_r43x6_sqr_fast`'s and `fd_r43x6_mul_fast`'s
contract on their inputs, which `u47` does not give; for an operand that is
itself a rung they are `foldVec_getElem_six`/`_seven`. -/
theorem repsqr_mul2_step (da db : Pointer) (xa ya xb yb : Vector (BitVec 64) 8)
    (n : BitVec 64) {u : GlobalState} (hu : u.WF)
    (hda : IsVecPtr u.mem da) (hdb : IsVecPtr u.mem db) (hne : da.id ≠ db.id)
    (hn63 : n.toNat < 2 ^ 63)
    (hxa : R43x6.U47 (xa.take R43x6.limbCount)) (hxa6 : xa[6] = 0) (hxa7 : xa[7] = 0)
    (hya : R43x6.U47 (ya.take R43x6.limbCount)) (hya6 : ya[6] = 0) (hya7 : ya[7] = 0)
    (hxb : R43x6.U47 (xb.take R43x6.limbCount)) (hxb6 : xb[6] = 0) (hxb7 : xb[7] = 0)
    (hyb : R43x6.U47 (yb.take R43x6.limbCount)) (hyb6 : yb[6] = 0) (hyb7 : yb[7] = 0) :
    ∃ (u' : GlobalState) (va vb : Vector (BitVec 64) 8),
      StateT.run (runFunction (fd_r43x6_repsqr_mul2.denote (Ctxt.Valuation.ofHVector
          [.value n, yb.map PoisonOr.value, xb.map PoisonOr.value, .value db,
            ya.map PoisonOr.value, xa.map PoisonOr.value, .value da]ₕ))) u
        = .value ([]ₕ, u')
      ∧ vecValue va = vecValue xa ^ 2 ^ n.toNat * vecValue ya
      ∧ vecValue vb = vecValue xb ^ 2 ^ n.toNat * vecValue yb
      ∧ Wrote2 da db va vb u u' := by
  obtain ⟨u', hrun, va, vb, heq, hva, hvb, h44a, h44b⟩ :=
    fd_r43x6_repsqr_mul2_conforms da db xa ya xb yb n u hu hda hdb hne hn63
      hxa hxa6 hxa7 hya hya6 hya7 hxb hxb6 hxb7 hyb hyb6 hyb7
  -- the two splices, in the order the spec writes them
  have hdaS : IsVecPtr (u.mem.splice da (vecBV va)) da := ⟨fits_splice hda.1, hda.2⟩
  have hdbS : IsVecPtr ((u.mem.splice da (vecBV va)).splice db (vecBV vb)) db :=
    ⟨fits_splice (fits_splice hdb.1), hdb.2⟩
  have hwf : ({ alloc := u.alloc, mem := (u.mem.splice da (vecBV va)).splice db (vecBV vb), globals := u.globals } : GlobalState).WF := hu.splice.splice
  refine ⟨u', va, vb, hrun, hva, hvb, ?_⟩
  refine { wf := GlobalState.WF.of_equiv hwf (GlobalState.Equiv.symm heq)
           globals := heq.globals
           other := ?other
           ptrA := ?ptrA, ptrB := ?ptrB, valA := ?valA, valB := ?valB
           u44A := h44a, u44B := h44b }
  case other =>
    intro c hca hcb
    rw [heq.live c, live?_splice_ne (fun h => hcb h.symm),
      live?_splice_ne (fun h => hca h.symm)]
  case ptrA =>
    exact ⟨fits_of_live?_eq (heq.live da.id) (fits_splice (fits_splice hda.1)), hda.2⟩
  case ptrB =>
    exact ⟨fits_of_live?_eq (heq.live db.id) (fits_splice (fits_splice hdb.1)), hdb.2⟩
  case valA =>
    refine readVec_eq_of ?_
    rw [readVec?_of_live?_eq (heq.live da.id), readVec?_splice_ne (Ne.symm hne)]
    exact readVec?_splice_self va hda
  case valB =>
    refine readVec_eq_of ?_
    rw [readVec?_of_live?_eq (heq.live db.id)]
    exact readVec?_splice_self vb ⟨fits_splice hdb.1, hdb.2⟩

end Firedancer.Avx512
