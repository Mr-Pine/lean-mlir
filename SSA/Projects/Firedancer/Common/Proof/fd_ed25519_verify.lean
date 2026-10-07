/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_curve25519_scalar_reduce
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_verify
import SSA.Projects.Firedancer.Proof.Memory
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# `fd_ed25519_verify`: what the ref and AVX-512 proofs share

The return value bound with the state, the round constants carried across a call, `scalar_reduce`'s
stores, and what an encoding determines.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `run_runFunction'` with the return value existential too, bound before the
state so each path picks its own. -/
theorem run_runFunction_ret {α β : Type} {body : EffectM α} {s : GlobalState} (f : β → α)
    (P : GlobalState → β → Prop)
    (h :
      ∃ (x : β) (s' : GlobalState),
        StateT.run body s = .value (f x, s') ∧ P (s.popFrame s'.mem) x) :
    ∃ (s' : GlobalState) (x : β), StateT.run (runFunction body) s = .value (f x, s') ∧ P s' x :=
  let ⟨x, t, hrun, hP⟩ := h
  ⟨s.popFrame t.mem, x, run_runFunction hrun, hP⟩

/-! ### The round constants across a call -/

/-- The round-constant table survives states that keep the symbol table and every caller block
but `sha`'s. -/
theorem Sha512KHolds.of_live?_eq {s t : GlobalState} {sha : Pointer} {k : BitVec (80 * 64)}
    (hs : s.WF) (h : Sha512KHolds s sha k) (hg : t.globals = s.globals)
    (hl :
      ∀ b : BlockId, b ≠ sha.id → b.id < s.alloc.nextFreeBlock → t.mem.live? b = s.mem.live? b) :
    Sha512KHolds t sha k :=
  let ⟨q, ⟨hp, hfit, hval⟩, hne⟩ := h
  ⟨q,
    ⟨by
      unfold GlobalPtr at hp ⊢; rw [hg]; exact hp,
      (readWord_of_live?_eq (hl q.id hne (lt_nextFreeBlock_of_fits hs hfit)) hfit).imp fun _ hv =>
        hv.trans hval⟩,
    hne⟩

/-- `readWord` across states that agree on the block. -/
theorem readWord_eq_of_live?_eq {m m' : MemoryState} {p : Pointer} {w : Nat} {h' : Fits m' p w}
    (hl : m'.live? p.id = m.live? p.id) (h : Fits m p w) : readWord h' = readWord h :=
  readWord_eq_of ((readWord?_of_live?_eq hl).trans (readWord?_eq_some h rfl))

/-! ### `scalar_reduce`'s four stores -/

/-- The four words `scalar_reduce` stores, read back as its 32-byte output. -/
theorem readBuf_scalarOutMem {m : MemoryState} {r : Pointer} {w : Fin 4 → BitVec 64}
    (hm : IsByteBufPtr m r) (h : IsByteBufPtr (scalarOutMem m r w) r) :
    readBuf h = packWords w := by
  obtain ⟨⟨b, hb, hlen⟩, hoff⟩ := hm
  have hl : m.live? r.id = some b := by simp only [MemoryState.live?, hb]
  have ho :
    ∀ k : BitVec 64, k.toNat < 32 → (r.withOffset k).offsetInBits = r.offsetInBits + 8 * k.toNat :=
    fun k hk => by
    simp only [Pointer.withOffset, Pointer.offsetInBits, BitVec.toNat_add,
      Nat.mod_eq_of_lt (show r.offset.toNat + k.toNat < 2 ^ 64 by omega)]
    omega
  have h4 :=
    splicedLive _ (r.withOffset 24) _
      (splicedLive _ (r.withOffset 16) _
        (splicedLive _ (r.withOffset 8) _ (splicedLive m r b hl (w 0)) (w 1)) (w 2))
      (w 3)
  rw [ho 8 (by decide), ho 16 (by decide), ho 24 (by decide)] at h4
  have e : (scalarOutMem m r w).live? r.id = _ := h4
  simp only [readBuf, readBuf?, e, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.get_some]
  ext i hi
  have hin : r.offsetInBits + i < 8 * b.length := by
    simp only [LiveBlock.lengthInBits] at hlen; omega
  show _ = (w 3 ++ w 2 ++ w 1 ++ w 0).getLsbD i
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  have e16 : (16 : BitVec 64).toNat = 16 := rfl
  have e24 : (24 : BitVec 64).toNat = 24 := rfl
  rw [e8, e16, e24]
  clear h4 e ho hb hl h
  simp only [BitVec.getElem_extractLsb', getLsbD_spliceBits, BitVec.getLsbD_append]
  split_ifs <;>
    first
    | omega
    | exact congrArg (BitVec.getLsbD _) (by omega)

theorem live?_scalarOutMem_ne {m : MemoryState} {r : Pointer} {w : Fin 4 → BitVec 64} {b : BlockId}
    (h : r.id ≠ b) : (scalarOutMem m r w).live? b = m.live? b := by
  simp only [scalarOutMem, live?_splice_ne (p := r.withOffset 24) h,
    live?_splice_ne (p := r.withOffset 16) h, live?_splice_ne (p := r.withOffset 8) h,
    live?_splice_ne h]

/-- Across `scalar_reduce`'s `≈`: first-order, so the kernel never unfolds the stores. -/
theorem wf_of_equiv_scalarOutMem {s t : GlobalState} {r : Pointer} {w : Fin 4 → BitVec 64}
    (hs : s.WF) (he : t ≈ ({ s with mem := scalarOutMem s.mem r w } : GlobalState)) : t.WF :=
  fun q hq =>
  (he.live q).trans
    (by
      unfold scalarOutMem
      iterate 4 refine live?_splice_eq_none ?_
      exact
        hs q
          (by
            rw [he.alloc] at hq; exact hq))

/-! ### Encodings -/

theorem sq_mul_den (V : Edwards.Point curve) : V.x ^ 2 * (d * V.y ^ 2 + 1) = V.y ^ 2 - 1 := by
  have h : -V.x ^ 2 + V.y ^ 2 = 1 + d * V.x ^ 2 * V.y ^ 2 := V.on
  linear_combination -h

theorem den_ne_zero (V : Edwards.Point curve) : d * V.y ^ 2 + 1 ≠ 0 := fun h0 => by
  have h := sq_mul_den V
  rw [h0, mul_zero] at h
  have hy : V.y ^ 2 = 1 := by linear_combination -h
  rw [hy, mul_one] at h0
  exact absurd (by linear_combination h0 : d = -1) (by decide)

/-- An encoded point makes the decompression ratio a square. -/
theorem isSquare_of_encodes {b : BitVec 256} {V : Edwards.Point curve} (h : Encodes b V) :
    IsSquare
      ((((b.extractLsb' 0 255).toNat : ZMod p) ^ 2 - 1) /
        (d * ((b.extractLsb' 0 255).toNat : ZMod p) ^ 2 + 1)) := by
  rw [← h.1]
  exact ⟨V.x, by rw [← sq_mul_den, mul_div_assoc, div_self (den_ne_zero V), mul_one, sq]⟩

/-- An encoding names at most one point: `y` fixes `x²`, the sign bit `x`. -/
theorem encodes_unique {b : BitVec 256} {V W : Edwards.Point curve} (hV : Encodes b V)
    (hW : Encodes b W) : V = W := by
  have hy : V.y = W.y := hV.1.trans hW.1.symm
  have hx2 : V.x ^ 2 = W.x ^ 2 := by
    apply mul_right_cancel₀ (den_ne_zero V)
    rw [sq_mul_den, hy, sq_mul_den]
  refine Edwards.Point.ext ?_ hy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx2 with h | h
  · exact h
  by_cases h0 : W.x = 0
  · rw [h, h0, neg_zero]
  have hV0 : V.x ≠ 0 := by
    rw [h]; exact neg_ne_zero.mpr h0
  have hpar := (hV.2 hV0).trans (hW.2 h0).symm
  rw [h, ZMod.neg_val, if_neg h0] at hpar
  have hlt := ZMod.val_lt W.x
  have hpos : W.x.val ≠ 0 := (ZMod.val_ne_zero W.x).mpr h0
  have hp : p % 2 = 1 := by decide
  omega

/-! ### Comparing points -/

/-- `SamePoint` against a well-formed point is equality of what they stand for. -/
theorem samePoint_iff_of_represents {P Q : Point} {V : Edwards.Point curve} (hP : P.Represents V)
    (hQ : Q.WellFormed) : P.SamePoint Q ↔ V = Q.toAffine hQ :=
  ⟨fun h => Edwards.Point.ext (hP.x_eq.symm.trans h.1) (hP.y_eq.symm.trans h.2), fun h =>
    ⟨hP.x_eq.trans (congrArg Edwards.Point.x h), hP.y_eq.trans (congrArg Edwards.Point.y h)⟩⟩

end Firedancer.Common
