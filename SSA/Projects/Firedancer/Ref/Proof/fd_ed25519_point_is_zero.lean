import SSA.Projects.Firedancer.Ref.Spec.fd_ed25519_point_is_zero
import SSA.Projects.Firedancer.Ref.Mlir.fd_ed25519_point_is_zero
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations

import SSA.Projects.Firedancer.Ref.Proof.fd_f25519_is_zero
import SSA.Projects.Firedancer.Ref.Proof.fd_f25519_eq

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

set_option maxHeartbeats 3200000 in
theorem fd_ed25519_point_is_zero_conforms (p: Pointer) (s: GlobalState)
  (hs : s.WF)
  (hp : IsPointPtr s.mem p)
  (hpbounds : AllLimbBounds hp) :
  fd_ed25519_point_is_zero_spec p s hp := by
    simp only [fd_ed25519_point_is_zero_spec, Cfg.denote]
    intro hz

    -- coordinate 0 sits at offset 0, so it *is* `p`
    have xFieldElemPtr : IsFieldElemPtr s.mem p := by
      simpa [Pointer.withOffset] using isCoordPtr p hp 0
    have xCoordBounds : LimbBounds xFieldElemPtr :=
      limbBounds_congr (by simp [Pointer.withOffset]) (coordLimbBounds hp hpbounds 0)

    obtain ⟨iszstate, hiszstate, hiszstate_eq⟩ :=
      fd_f25519_is_zero_conforms p s hs xFieldElemPtr xCoordBounds

    let yPtr := p.withOffset (5 * 8)
    have yPtr₀ : IsFieldElemPtr s.mem yPtr := by
      simpa [yPtr, Pointer.withOffset] using isCoordPtr p hp 1
    have yFieldElemPtr : IsFieldElemPtr iszstate.mem yPtr :=
      ⟨fits_equiv hiszstate_eq yPtr₀.1, yPtr₀.2⟩
    have yCoordBounds₀ : LimbBounds yPtr₀ :=
      limbBounds_congr (by simp [yPtr, Pointer.withOffset]) (coordLimbBounds hp hpbounds 1)
    have yCoordBounds : LimbBounds yFieldElemPtr :=
      limbBounds_of_equiv hiszstate_eq yCoordBounds₀

    let zPtr := p.withOffset (3 * 5 * 8)
    have zPtr₀ : IsFieldElemPtr s.mem zPtr := by
      simpa [zPtr, Pointer.withOffset] using isCoordPtr p hp 3
    have zFieldElemPtr : IsFieldElemPtr iszstate.mem zPtr :=
      ⟨fits_equiv hiszstate_eq zPtr₀.1, zPtr₀.2⟩
    have zCoordBounds₀ : LimbBounds zPtr₀ :=
      limbBounds_congr (by simp [zPtr, Pointer.withOffset]) (coordLimbBounds hp hpbounds 3)
    have zCoordBounds : LimbBounds zFieldElemPtr :=
      limbBounds_of_equiv hiszstate_eq zCoordBounds₀

    obtain ⟨eqstate, heqstate, heqstate_eq⟩ :=
      fd_f25519_eq_conforms yPtr zPtr iszstate (hs.of_equiv hiszstate_eq) yFieldElemPtr zFieldElemPtr yCoordBounds zCoordBounds

    refine ⟨s.popFrame eqstate.mem, run_runFunction (s' := eqstate) ?_, ?_⟩
    case refine_2 =>
      have hchain := GlobalState.Equiv.trans hiszstate_eq heqstate_eq
      exact GlobalState.Equiv.symm
        (GlobalState.killFrom_equiv eqstate.mem hs (fun q _ => (hchain.2 q).symm))

    denote_step_all v 2
    denote_eval v 2 2
    simp only [LLVM.const?] at hv0 hv1 hv2
    subst hv0 hv1 hv2

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value (if readFieldElem? p s.mem = some 0 then 1#32 else 0#32)) (s' := iszstate) ?_).trans ?_
    · exact hiszstate

    denote_step_all v 5
    denote_eval v 4 5
    simp [Ctxt.Valuation.singleton, gep, ptradd, LLVM.const?, LLVM.add, LLVM.mul, LLVM.add?, LLVM.mul?] at hv4 hv5
    have v4Value : v4 = .value yPtr := by
      simp [hv4, yPtr, Pointer.withOffset, simp_sllvm]
    have v5Value : v5 = .value zPtr := by
      simp [hv5, zPtr, Pointer.withOffset, simp_sllvm]
    subst v4Value v5Value
    clear hv4 hv5

    refine (BlockCom.run_bind_denote_call_of_value
        (x := PoisonOr.value (if readFieldElem? yPtr iszstate.mem = readFieldElem? zPtr iszstate.mem then 1#32 else 0#32)) (s' := eqstate) ?_).trans ?_
    · exact heqstate

    denote_step_all v 7
    denote_eval v 7 7
    simp [LLVM.and, LLVM.and?] at hv7
    subst hv7

    simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]

    let P := readPoint hp

    -- the four coordinates of `P`, named
    obtain ⟨c, hc⟩ : ∃ c : Fin 4 → ZMod _root_.p, ∀ i, readCoordinate? p i s.mem = some (c i) :=
      ⟨fun i => (readFieldElem? (p.withOffset (i * (5 * 8))) s.mem).get
          (readFieldElem?_isSome (isCoordPtr p hp i)),
        fun i => (Option.some_get _).symm⟩
    have hPdef : P = decodePoint ![c 0, c 1, c 2, c 3] := by
      have h4 : readPoint? p s.mem = some (decodePoint ![c 0, c 1, c 2, c 3]) := by
        simp [readPoint?, hc]
      simp only [P, readPoint, h4, Option.get_some]

    have x : readFieldElem p s.mem xFieldElemPtr = P.X := by
      have hc0 : readFieldElem? p s.mem = some (c 0) := by
        rw [← hc 0]; simp [readCoordinate?, Pointer.withOffset]
      rw [hPdef]; simp [decodePoint, readFieldElem, hc0]
    have x' : readFieldElem? p s.mem = some P.X := by
      rw [← x]
      exact (Option.some_get _).symm
    have y : readFieldElem yPtr iszstate.mem yFieldElemPtr = P.Y := by
      have hc1 : readFieldElem? yPtr iszstate.mem = some (c 1) := by
        rw [← readFieldElem?_of_equiv hiszstate_eq yPtr, ← hc 1]
        simp [readCoordinate?, yPtr, Pointer.withOffset]
      rw [hPdef]; simp [decodePoint, readFieldElem, hc1]
    have y' : readFieldElem? yPtr iszstate.mem = some P.Y := by
      rw [← y]
      exact (Option.some_get _).symm
    have z : readFieldElem zPtr iszstate.mem zFieldElemPtr = P.Z := by
      have hc3 : readFieldElem? zPtr iszstate.mem = some (c 3) := by
        rw [← readFieldElem?_of_equiv hiszstate_eq zPtr, ← hc 3]
        simp [readCoordinate?, zPtr, Pointer.withOffset]
      rw [hPdef]; simp [decodePoint, readFieldElem, hc3]
    have z' : readFieldElem? zPtr iszstate.mem = some P.Z := by
      rw [← z]
      exact (Option.some_get _).symm
    rw [x', y', z']
    have hgoal : Ed25519.Point.zero.SamePoint (readPoint hp) ↔ (P.Y = P.Z ∧ P.X = 0) := by
      rw [Ed25519.Point.samePoint_iff_cross isUnit_one hz]
      simp [Ed25519.Point.zero, P, eq_comm, and_comm]
    by_cases h1 : P.Y = P.Z <;> by_cases h2 : P.X = 0 <;> simp [h1, h2, hgoal]

end Firedancer.Ref
