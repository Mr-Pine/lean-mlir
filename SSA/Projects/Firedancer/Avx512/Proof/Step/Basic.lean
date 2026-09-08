/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Fold
import SSA.Projects.Firedancer.Avx512.Proof.Quad
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# Reading and writing a `wwl_t` slot

The `Ref/Proof/Step/Basic.lean` of the avx512 side: what a peeled call leaves
behind, and how to read a slot back afterwards. Nothing here names a kernel --
every `fd_r43x6` callee that writes `wwl_t` out-parameters uses it.

`readVec` had no transport lemmas at all; these are its counterparts of
`readWord?_splice_ne`/`_self` in `Proof/Memory.lean`, and belong beside them
once a second caller wants them.
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

/-- `live?` from the `getElem?` form: the direction `getElem?_of_live?` does not
give, and the one a `Fits` witness hands you. Unfolding `live?` by `simp` at a
call site instead blows the recursion depth, since the block comes out of a
`choose` rather than a constructor. -/
theorem live?_of_getElem? {m : MemoryState} {q : BlockId} {b : LiveBlock}
    (h : m[q]? = some (.live b)) : m.live? q = some b := by
  unfold MemoryState.live?; rw [h]

/-- **What a whole-vector load at a slot reads**: the vector `readVec` says it
holds. `peel_load` leaves the `unflatten` of a 512-bit extract; this is the
bridge from that to the `Wrote2.valA`/`valB` a call left behind, and is what
lets a rung be read back out one or two calls later.

The `Quad` counterpart is `unflatten_readQuad_v03`; this is the same argument
at one vector rather than three. -/
theorem unflatten_readVec {m : MemoryState} {p : Pointer} (h : IsVecPtr m p)
    {blk : LiveBlock} (hblk : m.live? p.id = some blk) :
    LLVM.Ty.unflatten (.vector 8 (.bitvec (.concrete 64)))
        (blk.bytes.extractLsb' p.offsetInBits
          (LLVM.Ty.width (.vector 8 (.bitvec (.concrete 64)))))
      = (readVec h).map PoisonOr.value := by
  apply Vector.ext
  intro i hi
  simp [readVec, readVec?, hblk, LLVM.Ty.unflatten]
  show (blk.bytes.extractLsb' p.offsetInBits 512).extractLsb' (i * 64) 64
      = blk.bytes.extractLsb' (p.offsetInBits + 64 * i) 64
  rw [BitVec.extractLsb'_extractLsb'_of_le (show i * 64 + 64 ≤ 512 from by omega),
    Nat.mul_comm i 64]

/-- `peel_load_vec v, p, hp, hval, s` runs the next whole-vector load at a slot
`hp` says is a `wwl_t` and `hval` says holds `v`.

`peel_load` would do it too, but it binds the `unflatten` of a 512-bit extract,
which then has to be rewritten to `v` *in the goal* -- and on a block the size
of `fd_r43x6_pow22523_2`'s that one `rw` is 47 seconds. Here the same reasoning
happens in the step lemma's side goal, which is small, and the goal only ever
sees `v`. The block and its `live?` equation come out of `hp` rather than being
passed: destructing the `∃` in `Fits` at the call site would revert the walk
goal, which costs about as much again. -/
macro "peel_load_vec " v:term ", " p:term ", " hp:term ", " hval:term ", " st:term : tactic =>
  `(tactic|
   (try simp only [bind_assoc]
    rw [BlockCom.run_bind_denote_var_of_value (x := ($v).map PoisonOr.value) (s' := $st)
      (by simp only [Expr.denoteOp, Ctxt.Valuation.singleton, simp_denote, simp_sllvm]
          rw [run_liftM (run_load (t := .vector 8 (.bitvec (.concrete 64)))
            (($hp).1.choose_spec.1)
            (by have := ($hp).1.choose_spec.2
                show ($p).offsetInBits + 512 ≤ _
                simp only [LiveBlock.lengthInBits] at *
                omega))]
          rw [unflatten_readVec $hp (live?_of_getElem? ($hp).1.choose_spec.1), $hval:term]
          rfl)]))


/-- What a peeled call leaves at *two* `wwl_t` out-parameters: the ref's
`Wrote₂`, at vectors. The two destinations hold `va`/`vb` with the `u44` limbs
and zero high lanes the fold leaves, and every block but those two reads as it
did before the call.

The zero lanes are fields rather than being recovered at the call site: the
values come out of a spec as abstract vectors, so nothing downstream can see
that they are a `foldVec`. -/
structure Wrote2 (da db : Pointer) (va vb : Vector (BitVec 64) 8)
    (u u' : GlobalState) : Prop where
  wf : u'.WF
  /-- The symbol table is untouched: `runFunction` restores it. -/
  globals : u'.globals = u.globals
  /-- Only the two destinations moved. -/
  other : ∀ c : BlockId, c ≠ da.id → c ≠ db.id → u'.mem.live? c = u.mem.live? c
  /-- The memory the call leaves: `u`'s with the two destinations written.
  Everything else here follows from it, but a caller that only needs a slot to
  still read back should not have to redo that; the last call of a ladder,
  whose destinations are the *caller's* blocks, is the one that wants this. -/
  mem : u' ≈ ({ u with mem := (u.mem.splice da (vecBV va)).splice db (vecBV vb) }
    : GlobalState)
  ptrA : IsVecPtr u'.mem da
  ptrB : IsVecPtr u'.mem db
  valA : readVec ptrA = va
  valB : readVec ptrB = vb
  u44A : R43x6.U44 (va.take R43x6.limbCount)
  u44B : R43x6.U44 (vb.take R43x6.limbCount)
  /-- Lane 6, which the fold zeroes -- the next kernel's contract. -/
  z6A : va[6] = 0
  z7A : va[7] = 0
  z6B : vb[6] = 0
  z7B : vb[7] = 0

namespace Wrote2

variable {da db : Pointer} {va vb : Vector (BitVec 64) 8} {u u' : GlobalState}

/-- A slot the call did not write keeps its contents, `IsVecPtr` witness and
all. This is what carries a ladder's earlier rungs across a later call. -/
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

end Firedancer.Avx512
