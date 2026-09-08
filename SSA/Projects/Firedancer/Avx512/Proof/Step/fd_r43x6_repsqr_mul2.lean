/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Step.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_repsqr_mul2
import SSA.Projects.Firedancer.Avx512.Proof.Step.Basic

/-!
# One `fd_r43x6_repsqr_mul2` call, peeled

The `Ref/Proof/Step/` shape again, for the ladder `fd_r43x6_pow22523_2` and
`fd_r43x6_invert` are built from. Unlike `fd_r43x6_sqr_fast` this kernel is
impure -- it writes through *two* `wwl_t *` out-parameters -- so it needs the
ref's `Wrote₂` treatment: what the call leaves at the two destinations, and
that it left everything else alone.

`Wrote2`, the `readVec` transport lemmas it is stated over, and `peel_load_vec`
are all in `Step/Basic.lean`: none of them name a kernel.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)


/-- **One `fd_r43x6_repsqr_mul2` call**, in the form `peel_call` takes it:
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
  obtain ⟨u', hrun, va, vb, heq, hva, hvb, h44a, h44b, z6a, z7a, z6b, z7b⟩ :=
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
           mem := heq
           ptrA := ?ptrA, ptrB := ?ptrB, valA := ?valA, valB := ?valB
           u44A := h44a, u44B := h44b
           z6A := z6a, z7A := z7a, z6B := z6b, z7B := z7b }
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

