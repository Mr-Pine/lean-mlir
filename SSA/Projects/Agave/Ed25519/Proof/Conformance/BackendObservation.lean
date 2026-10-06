import SSA.Projects.Agave.Ed25519.Proof.Conformance.ScalarAvx2
import SSA.Projects.Agave.Ed25519.Spec.Field
import SSA.Projects.RIR.Semantics.Func

/-! The affine memory observation and local, per-backend refinement obligation.
This file proves only composition of separately supplied refinements; it does
not supply a memory-bearing compiler CFG refinement. -/

namespace Agave.Ed25519.Conformance.BackendExecution

open LeanMLIR.RIR PointArithmetic Tables DoubleBase

abbrev Backend := Vals [.ptr, .ptr, .ptr, .ptr] → EffectM (Vals [])

/-- The common ABI is `(output, scalar A, point A, scalar B)`. Both extracted
backends return an ordinary four-coordinate, five-u64-per-coordinate point. -/
structure Invocation where
  output : Pointer
  scalarA : Pointer
  pointA : Pointer
  scalarB : Pointer

def Invocation.args (i : Invocation) : Vals [.ptr, .ptr, .ptr, .ptr] :=
  .cons (.value i.output) (.cons (.value i.scalarA)
    (.cons (.value i.pointA) (.cons (.value i.scalarB) .nil)))

def readCoordinate (state : GlobalState) (point : Pointer) (coordinate : Fin 4) : F :=
  (Field.serialValue (fun limb : Fin 5 =>
    state.mem.readAt (point.add (BitVec.ofNat 64
      (40 * coordinate.val + 8 * limb.val))) 64) : F)

def readPoint (state : GlobalState) (point : Pointer) : Extended F :=
  ⟨readCoordinate state point 0, readCoordinate state point 1,
    readCoordinate state point 2, readCoordinate state point 3⟩

/-- The complete point lies in a live allocation and its field/limb offsets
cannot wrap the 64-bit pointer. No bound on unrelated allocations is needed. -/
def PointReadable (state : GlobalState) (point : Pointer) : Prop :=
  Fits state.mem point 1280 ∧ point.offset.toNat + 160 ≤ 2 ^ 64

theorem pointReadable_limb_fits (state : GlobalState) (point : Pointer)
    (h : PointReadable state point) (coordinate : Fin 4) (limb : Fin 5) :
    Fits state.mem (point.add (BitVec.ofNat 64
      (40 * coordinate.val + 8 * limb.val))) 64 := by
  have hc := coordinate.isLt
  have hl := limb.isLt
  have hoff : 40 * coordinate.val + 8 * limb.val < 2 ^ 64 := by omega
  apply Fits.add hoff
  · simp only [BitVec.uaddOverflow, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hoff, decide_eq_true_iff]
    have hb := h.2
    omega
  · exact h.1.mono (by omega)

def inputResult (math : Nat → Extended F → Nat → Extended F)
    (i : Invocation) (state : GlobalState) : Extended F :=
  math (state.mem.readAt i.scalarA 256).toNat (readPoint state i.pointA)
    (state.mem.readAt i.scalarB 256).toNat

/-- A local proof obligation for one CFG invocation. Affine readback is all
composition requires; final heaps and projective representatives may differ.
The output range witness prevents totalized invalid reads from counting as
successful observations. There is no assumption about the other backend. -/
def RefinesAt (backend : Backend) (math : Nat → Extended F → Nat → Extended F)
    (i : Invocation) (state : GlobalState) : Prop :=
  ∃ resultState : GlobalState,
    backend i.args state = .value (.nil, resultState) ∧
    PointReadable resultState i.output ∧
    affine (readPoint resultState i.output) = affine (inputResult math i state)

/-- Execute the actual backend, read its ordinary point output, and apply the
mathematical canonical encoder. Poison or an unreadable result remains `none`. -/
noncomputable def observe (backend : Backend) (i : Invocation)
    (state : GlobalState) : Option Verifier.Bytes32 := by
  classical
  exact match backend i.args state with
    | .poison => none
    | .value (_, resultState) =>
        if PointReadable resultState i.output then
          some (compressMath (readPoint resultState i.output))
        else none

theorem observe_eq_of_refinement (backend : Backend)
    (math : Nat → Extended F → Nat → Extended F) (i : Invocation) (state : GlobalState)
    (hrefines : RefinesAt backend math i state) :
    observe backend i state = some (compressMath (inputResult math i state)) := by
  obtain ⟨resultState, hcall, hfits, haffine⟩ := hrefines
  simp only [observe, hcall, ite_eq_left hfits]
  exact congrArg (fun xy => some (encodeAffine xy)) haffine

/-- Separate refinements to the two concrete algorithms imply observation
equality. This theorem assumes no relation between the backend executions. -/
theorem observations_eq_of_per_backend_refinements
    (serial avx2 : Backend) (i : Invocation) (state : GlobalState)
    (hserial : RefinesAt serial serialMath i state)
    (havx2 : RefinesAt avx2 avx2Math i state) :
    observe serial i state = observe avx2 i state := by
  rw [observe_eq_of_refinement _ _ _ _ hserial,
    observe_eq_of_refinement _ _ _ _ havx2]
  exact congrArg some (scalar_avx2_math_compression_eq _ _ _)

end Agave.Ed25519.Conformance.BackendExecution
