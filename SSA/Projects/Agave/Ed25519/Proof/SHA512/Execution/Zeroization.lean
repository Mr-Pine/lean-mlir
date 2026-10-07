import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Frame

/-! Exact execution and frame behavior of the 64 auxiliary byte stores. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

/-- A register/pointer association used only to describe an actual store list. -/
def zeroStoreList (targets : List (Reg Γ .ptr × Pointer)) (zero : Reg Γ (.bv 8)) :
    List (Instr Γ) := targets.map fun target => .store target.1 zero

/-- Sequential stores preserve the environment and allocation counter, even
when two destination pointers alias. Safety follows from allocation liveness. -/
theorem zeroStoreList_run (targets : List (Reg Γ .ptr × Pointer))
    (E : Env Γ) (s : GlobalState) (zero : Reg Γ (.bv 8))
    (hz : E.read zero = .value 0#8)
    (hread : ∀ target ∈ targets, E.read target.1 = .value target.2)
    (hlive : ∀ target ∈ targets, SmallRange s.mem target.2 1) :
    (List.foldlM Instr.run E (zeroStoreList targets zero) : EffectM (Env Γ)) s =
      .value (E, {s with mem := zeroBytes s.mem (targets.map Prod.snd)}) := by
  induction targets generalizing s with
  | nil => simp [zeroStoreList, zeroBytes, List.foldlM_nil, EffectM.pure_eq]
  | cons target rest ih =>
    have hr := hread target (by simp)
    have hf := (hlive target (by simp)).fits
    have hstep : Instr.run E (.store target.1 zero) s =
        .value (E, {s with mem := s.mem.storeAt target.2 0#8}) := by
      simp [Instr.run, Operation.store, hr, hz, hf,
        EffectM.bind_eq, EffectM.pure_eq, mlir_effect, throwUBIf]
    have ht := ih {s with mem := s.mem.storeAt target.2 0#8}
      (fun t ht => hread t (by simp [ht]))
      (fun t ht => (hlive t (by simp [ht])).storeAt _ _)
    simpa [zeroStoreList, zeroBytes, List.foldlM_cons,
      EffectM.bind_eq, hstep] using ht

/-- Registers 87 through 150 are the one-byte auxiliary allocations. -/
def scratchReg (i : Fin 64) : Reg program.Γ .ptr :=
  match i.val with
  | 0 => (%87)
  | 1 => (%88)
  | 2 => (%89)
  | 3 => (%90)
  | 4 => (%91)
  | 5 => (%92)
  | 6 => (%93)
  | 7 => (%94)
  | 8 => (%95)
  | 9 => (%96)
  | 10 => (%97)
  | 11 => (%98)
  | 12 => (%99)
  | 13 => (%100)
  | 14 => (%101)
  | 15 => (%102)
  | 16 => (%103)
  | 17 => (%104)
  | 18 => (%105)
  | 19 => (%106)
  | 20 => (%107)
  | 21 => (%108)
  | 22 => (%109)
  | 23 => (%110)
  | 24 => (%111)
  | 25 => (%112)
  | 26 => (%113)
  | 27 => (%114)
  | 28 => (%115)
  | 29 => (%116)
  | 30 => (%117)
  | 31 => (%118)
  | 32 => (%119)
  | 33 => (%120)
  | 34 => (%121)
  | 35 => (%122)
  | 36 => (%123)
  | 37 => (%124)
  | 38 => (%125)
  | 39 => (%126)
  | 40 => (%127)
  | 41 => (%128)
  | 42 => (%129)
  | 43 => (%130)
  | 44 => (%131)
  | 45 => (%132)
  | 46 => (%133)
  | 47 => (%134)
  | 48 => (%135)
  | 49 => (%136)
  | 50 => (%137)
  | 51 => (%138)
  | 52 => (%139)
  | 53 => (%140)
  | 54 => (%141)
  | 55 => (%142)
  | 56 => (%143)
  | 57 => (%144)
  | 58 => (%145)
  | 59 => (%146)
  | 60 => (%147)
  | 61 => (%148)
  | 62 => (%149)
  | _ => (%150)

def scratchTargets (scratch : Fin 64 → Pointer) : List (Reg program.Γ .ptr × Pointer) :=
  List.ofFn fun i => (scratchReg i, scratch i)

/-- Structural certificate against the imported block, without reimporting a
modified or zeroization-free body. -/
theorem scratch_store_slice (p : Primitives) (scratch : Fin 64 → Pointer) :
    ((program.bb3 p).body.drop 43).take 64 =
      zeroStoreList (scratchTargets scratch) (%8) := by
  rfl

/-- All sixty-four volatile scratch-byte stores in the imported bb3. -/
theorem scratch_zeroization (p : Primitives) (E : Env program.Γ) (s : GlobalState)
    (scratch : Fin 64 → Pointer)
    (hz : E.read (%8) = .value 0#8)
    (hread : ∀ i, E.read (scratchReg i) = .value (scratch i))
    (hlive : ∀ i, SmallRange s.mem (scratch i) 1) :
    (List.foldlM Instr.run E (((program.bb3 p).body.drop 43).take 64) :
      EffectM (Env program.Γ)) s =
      .value (E, {s with mem := zeroBytes s.mem (List.ofFn scratch)}) := by
  rw [scratch_store_slice p scratch]
  have hr : ∀ target ∈ scratchTargets scratch, E.read target.1 = .value target.2 := by
    intro target ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact hread i
  have hl : ∀ target ∈ scratchTargets scratch, SmallRange s.mem target.2 1 := by
    intro target ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact hlive i
  simpa [scratchTargets, List.map_ofFn] using
    zeroStoreList_run (scratchTargets scratch) E s (%8) hz hr hl

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
