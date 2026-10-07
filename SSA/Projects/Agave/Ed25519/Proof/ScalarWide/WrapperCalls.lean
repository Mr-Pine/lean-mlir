import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryCall
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FiveWordMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Linked

/-! Both actual wrapper call sites, followed by their actual 40-byte copies.
Callee execution comes from the complete imported Montgomery body; the premises
are only local register, memory, and limb facts. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Bridge
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

def montgomeryCopyState (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant : Pointer) : GlobalState :=
  copy40State (ScalarMontgomeryMul.callPostState state a b tmp operand constant) operand tmp

theorem low_copy_run (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (dst src : Pointer)
    (hdst : E.read (%75) = .value dst) (hsrc : E.read (%73) = .value src)
    (h40 : E.read (%4) = .value 40#64)
    (hdlive : SmallRange state.mem dst 40) (hslive : SmallRange state.mem src 40)
    (hne : dst.id ≠ src.id) :
    List.foldlM Instr.run E (((program.entry linkedPrimitives g).body.drop 321).take 3) state =
      .value (E, copy40State state dst src) := by
  have hfd := hdlive.fits
  have hfs := hslive.fits
  have hd : (Range.of dst 320).Disjoint (Range.of src 320) := Range.disjoint_of_id_ne hne
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy,
    copy40State, hdst, hsrc, h40, hfd, hfs, hd,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem low_call_copy_run (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (a b : Fin 5 → BitVec 64) (tmp operand constant : Pointer)
    (htmp : E.read (%73) = .value tmp) (hop : E.read (%75) = .value operand)
    (hc : E.read (%39) = .value constant) (h40 : E.read (%4) = .value 40#64)
    (hwf : state.WF) (htlive : SmallRange state.mem tmp 40)
    (holive : SmallRange state.mem operand 40) (hclive : SmallRange state.mem constant 40)
    (hne : operand.id ≠ tmp.id)
    (ha : ∀ i : Fin 5, state.mem.readAt (operand.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i)
    (hb : ∀ i : Fin 5, state.mem.readAt (constant.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i)
    (habound : ∀ i, (a i).toNat < 2 ^ 52) (hbbound : ∀ i, (b i).toNat < 2 ^ 52)
    (hbcanonical : ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) < subgroupOrder) :
    (program.entry linkedPrimitives g).runBodyFrom E 320 state =
      (program.entry linkedPrimitives g).runBodyFrom E 324
        (montgomeryCopyState state a b tmp operand constant) := by
  have hcall := ScalarMontgomeryMul.program_call montgomeryPrimitives rfl state a b
    tmp operand constant hwf htlive holive hclive ha hb habound hbbound hbcanonical
  rw [low_montgomery_call linkedPrimitives g E state _ tmp operand constant htmp hop hc hcall]
  have htlive' := ScalarMontgomeryMul.outputStores_smallRange state.mem tmp tmp
    (ScalarMontgomeryMul.tailWords (ScalarMontgomeryMul.quotient52 a b operand constant)) 40 htlive
  have holive' := ScalarMontgomeryMul.outputStores_smallRange state.mem tmp operand
    (ScalarMontgomeryMul.tailWords (ScalarMontgomeryMul.quotient52 a b operand constant)) 40 holive
  exact ScalarMontgomeryMul.runBodyFrom_chunk (low_copy_run g E
    (ScalarMontgomeryMul.callPostState state a b tmp operand constant) operand tmp
    hop htmp h40 holive' htlive' hne)

theorem high_copy_run (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (dst src : Pointer)
    (hdst : E.read (%74) = .value dst) (hsrc : E.read (%72) = .value src)
    (h40 : E.read (%4) = .value 40#64)
    (hdlive : SmallRange state.mem dst 40) (hslive : SmallRange state.mem src 40)
    (hne : dst.id ≠ src.id) :
    List.foldlM Instr.run E (((program.entry linkedPrimitives g).body.drop 325).take 5) state =
      .value (E, copy40State state dst src) := by
  have hfd := hdlive.fits
  have hfs := hslive.fits
  have hd : (Range.of dst 320).Disjoint (Range.of src 320) := Range.disjoint_of_id_ne hne
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run, Operation.memcpy,
    copy40State, hdst, hsrc, h40, hfd, hfs, hd,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem high_call_copy_run (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (a b : Fin 5 → BitVec 64) (tmp operand constant : Pointer)
    (htmp : E.read (%72) = .value tmp) (hop : E.read (%74) = .value operand)
    (hc : E.read (%40) = .value constant) (h40 : E.read (%4) = .value 40#64)
    (hwf : state.WF) (htlive : SmallRange state.mem tmp 40)
    (holive : SmallRange state.mem operand 40) (hclive : SmallRange state.mem constant 40)
    (hne : operand.id ≠ tmp.id)
    (ha : ∀ i : Fin 5, state.mem.readAt (operand.add (BitVec.ofNat 64 (8 * i.val))) 64 = a i)
    (hb : ∀ i : Fin 5, state.mem.readAt (constant.add (BitVec.ofNat 64 (8 * i.val))) 64 = b i)
    (habound : ∀ i, (a i).toNat < 2 ^ 52) (hbbound : ∀ i, (b i).toNat < 2 ^ 52)
    (hbcanonical : ScalarMontgomeryMul.limbValue (fun i => (b i).toNat) < subgroupOrder) :
    (program.entry linkedPrimitives g).runBodyFrom E 324 state =
      (program.entry linkedPrimitives g).runBodyFrom E 330
        (montgomeryCopyState state a b tmp operand constant) := by
  have hcall := ScalarMontgomeryMul.program_call montgomeryPrimitives rfl state a b
    tmp operand constant hwf htlive holive hclive ha hb habound hbbound hbcanonical
  rw [high_montgomery_call linkedPrimitives g E state _ tmp operand constant htmp hop hc hcall]
  have htlive' := ScalarMontgomeryMul.outputStores_smallRange state.mem tmp tmp
    (ScalarMontgomeryMul.tailWords (ScalarMontgomeryMul.quotient52 a b operand constant)) 40 htlive
  have holive' := ScalarMontgomeryMul.outputStores_smallRange state.mem tmp operand
    (ScalarMontgomeryMul.tailWords (ScalarMontgomeryMul.quotient52 a b operand constant)) 40 holive
  exact ScalarMontgomeryMul.runBodyFrom_chunk (high_copy_run g E
    (ScalarMontgomeryMul.callPostState state a b tmp operand constant) operand tmp
    hop htmp h40 holive' htlive' hne)

/-- Call-and-copy retains every live range and raises the counter by ten. -/
theorem montgomeryCopyState_range (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant q : Pointer) (bytes : Nat) (h : SmallRange state.mem q bytes) :
    SmallRange (montgomeryCopyState state a b tmp operand constant).mem q bytes := by
  exact (ScalarMontgomeryMul.outputStores_smallRange state.mem tmp q
    (ScalarMontgomeryMul.tailWords (ScalarMontgomeryMul.quotient52 a b operand constant))
    bytes h).storeAt _ _

theorem montgomeryCopyState_count (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant : Pointer) :
    (montgomeryCopyState state a b tmp operand constant).alloc.nextFreeBlock =
      state.alloc.nextFreeBlock + 10 := rfl

theorem montgomeryCopyState_read (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant : Pointer)
    (htlive : SmallRange state.mem tmp 40) (holive : SmallRange state.mem operand 40)
    (i : Fin 5) :
    (montgomeryCopyState state a b tmp operand constant).mem.readAt
      (operand.add (BitVec.ofNat 64 (8 * i.val))) 64 =
      ScalarMontgomeryMul.tailWords (ScalarMontgomeryMul.quotient52 a b operand constant) i := by
  rw [montgomeryCopyState, copy40_read _ _ _
    (ScalarMontgomeryMul.outputStores_smallRange _ _ _ _ _ holive)
    (ScalarMontgomeryMul.outputStores_smallRange _ _ _ _ _ htlive)]
  exact ScalarMontgomeryMul.outputStores_read state.mem tmp _ htlive i

end Agave.Ed25519.Verifier.Execution.ScalarWide
