import SSA.Projects.Firedancer.Ref.Mlir.Field.fd_f25519_set
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Ref.Proof.MemoryOperations
import SSA.Projects.Firedancer.Ref.Proof.Field.fd_f25519_set

/-!
# Locals-frame machinery, exercised

A synthetic region -- not a lifted artifact -- with the shape
`fd_f25519_pow22523` steps through between its loops: three aggregate locals
(`fd_f25519_t t[1]`) and a chain of calls that write locals from locals,
ending in a write through the out-parameter. The proof is the intended
workout for `GlobalState.exists_afterAlloca_facts`, `FrameBelow`, and
`popFrame_equiv_splice`: one frame fact rides through every step, and the
`popFrame` ending discharges against the single out-splice.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

def localsChain_region : MLIR.AST.Region 0 := [mlir_region|
{
  ^bb0(%arg0: !llvm.ptr, %arg1: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %1 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %2 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %3 = "llvm.alloca"(%0) <{alignment = 16 : i64, elem_type = !llvm.array<1 x struct<"struct.fd_f25519", (array<5 x i64>)>>}> : (i32) -> !llvm.ptr
    %4 = "llvm.call"(%1, %arg1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %5 = "llvm.call"(%2, %1) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %6 = "llvm.call"(%3, %2) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %7 = "llvm.call"(%arg0, %3) <{CConv = #llvm.cconv<fastcc>, callee = @fd_f25519_set, fastmathFlags = #llvm.fastmath<none>}> : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "llvm.return"(%arg0) : (!llvm.ptr) -> ()
}
]

def localsChain : Cfg (Ctxt.ofList [SLLVM.Ty.ptr, SLLVM.Ty.ptr]) [SLLVM.Ty.ptr] :=
  [sllvm_cfg_of| localsChain_region with @fd_f25519_set := fd_f25519_set]

theorem localsChain_conforms (o a : Pointer) (s : GlobalState) (hs : s.WF)
    (ho : IsFieldElemPtr s.mem o) (ha : IsFieldElemPtr s.mem a) :
    ∃ out : BitVec (5 * 64),
      (∃ s' : GlobalState,
        StateT.run (runFunction (localsChain.denote
            (Ctxt.Valuation.ofHVector [.value a, .value o]ₕ))) s
          = .value ([.value o]ₕ, s')
        ∧ ({ s with mem := s.mem.splice o out } : GlobalState) ≈ s')
      ∧ ∀ i : Fin 5, readLimb? o i (s.mem.splice o out) = readLimb? a i s.mem := by
  simp only [Cfg.denote]

  -- `fd_f25519_t t1[1], t2[1], t3[1]`
  obtain ⟨t₁, s₁, ht₁def, hs₁def, hs₁WF, hfit₁, hid₁, hoff₁, hctr₁, hfr₁⟩ :=
    GlobalState.exists_afterAlloca_facts s hs (5 * 64)
  obtain ⟨t₂, s₂, ht₂def, hs₂def, hs₂WF, hfit₂, hid₂, hoff₂, hctr₂, hfr₂⟩ :=
    GlobalState.exists_afterAlloca_facts s₁ hs₁WF (5 * 64)
  obtain ⟨t₃, s₃, ht₃def, hs₃def, hs₃WF, hfit₃, hid₃, hoff₃, hctr₃, hfr₃⟩ :=
    GlobalState.exists_afterAlloca_facts s₂ hs₂WF (5 * 64)

  -- ids: the caller's blocks predate the frame, the locals are successive
  have hno : o.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ho.1
  have hna : a.id.id < s.alloc.nextFreeBlock := lt_nextFreeBlock_of_fits hs ha.1
  have ht₁a : t₁.id ≠ a.id := fun h => by rw [h] at hid₁; omega
  have ht₂t₁ : t₂.id ≠ t₁.id := fun h => by rw [h, hid₁] at hid₂; omega
  have ht₃t₂ : t₃.id ≠ t₂.id := fun h => by rw [h, hid₂] at hid₃; omega
  have ht₃t₁ : t₃.id ≠ t₁.id := fun h => by rw [h, hid₁] at hid₃; omega
  have hot₃ : o.id ≠ t₃.id := fun h => by rw [h, hid₃, hctr₂, hctr₁] at hno; omega

  -- one frame fact through the three allocas
  have fb₁ : FrameBelow s.alloc.nextFreeBlock s s₁ :=
    hs₁def ▸ FrameBelow.afterAlloca (le_refl _) (FrameBelow.refl _ _)
  have fb₂ : FrameBelow s.alloc.nextFreeBlock s s₂ :=
    hs₂def ▸ FrameBelow.afterAlloca (by omega) fb₁
  have fb₃ : FrameBelow s.alloc.nextFreeBlock s s₃ :=
    hs₃def ▸ FrameBelow.afterAlloca (by omega) fb₂

  -- the locals and the caller's elements, in `s₃`
  have pt₁s₃ : IsFieldElemPtr s₃.mem t₁ :=
    ⟨fits_of_live?_eq (hfr₃ t₁.id (Ne.symm ht₃t₁))
      (fits_of_live?_eq (hfr₂ t₁.id (Ne.symm ht₂t₁)) hfit₁), by simp [hoff₁]⟩
  have pt₂s₃ : IsFieldElemPtr s₃.mem t₂ :=
    ⟨fits_of_live?_eq (hfr₃ t₂.id (Ne.symm ht₃t₂)) hfit₂, by simp [hoff₂]⟩
  have pt₃s₃ : IsFieldElemPtr s₃.mem t₃ := ⟨hfit₃, by simp [hoff₃]⟩
  have pas₃ : IsFieldElemPtr s₃.mem a := isFieldElemPtr_of_live?_eq (fb₃ a.id hna) ha
  have pos₃ : IsFieldElemPtr s₃.mem o := isFieldElemPtr_of_live?_eq (fb₃ o.id hno) ho

  -- `t1 ≔ a`
  obtain ⟨o₁, ⟨u₁, hrun₁, heq₁⟩, hcopy₁⟩ :=
    fd_f25519_set_conforms t₁ a s₃ hs₃WF ht₁a pt₁s₃ pas₃
  have hu₁WF : u₁.WF := GlobalState.WF.of_equiv hs₃WF.splice heq₁
  have hlive₁ : ∀ b : BlockId, t₁.id ≠ b → u₁.mem.live? b = s₃.mem.live? b :=
    fun b hb => (heq₁.live b).symm.trans (live?_splice_ne hb)
  have fbu₁ : FrameBelow s.alloc.nextFreeBlock s u₁ :=
    FrameBelow.of_equiv heq₁ (FrameBelow.splice (by omega) fb₃)
  have pt₂u₁ : IsFieldElemPtr u₁.mem t₂ :=
    isFieldElemPtr_of_live?_eq (hlive₁ t₂.id (Ne.symm ht₂t₁)) pt₂s₃
  have pt₁u₁ : IsFieldElemPtr u₁.mem t₁ :=
    ⟨fits_equiv heq₁ (by simpa using fits_splice pt₁s₃.1), pt₁s₃.2⟩

  -- `t2 ≔ t1`
  obtain ⟨o₂, ⟨u₂, hrun₂, heq₂⟩, hcopy₂⟩ :=
    fd_f25519_set_conforms t₂ t₁ u₁ hu₁WF ht₂t₁ pt₂u₁ pt₁u₁
  have hu₂WF : u₂.WF := GlobalState.WF.of_equiv hu₁WF.splice heq₂
  have hlive₂ : ∀ b : BlockId, t₂.id ≠ b → u₂.mem.live? b = u₁.mem.live? b :=
    fun b hb => (heq₂.live b).symm.trans (live?_splice_ne hb)
  have fbu₂ : FrameBelow s.alloc.nextFreeBlock s u₂ :=
    FrameBelow.of_equiv heq₂ (FrameBelow.splice (by omega) fbu₁)
  have pt₃u₂ : IsFieldElemPtr u₂.mem t₃ :=
    isFieldElemPtr_of_live?_eq (hlive₂ t₃.id (Ne.symm ht₃t₂))
      (isFieldElemPtr_of_live?_eq (hlive₁ t₃.id (Ne.symm ht₃t₁)) pt₃s₃)
  have pt₂u₂ : IsFieldElemPtr u₂.mem t₂ :=
    ⟨fits_equiv heq₂ (by simpa using fits_splice pt₂u₁.1), pt₂u₁.2⟩

  -- `t3 ≔ t2`
  obtain ⟨o₃, ⟨u₃, hrun₃, heq₃⟩, hcopy₃⟩ :=
    fd_f25519_set_conforms t₃ t₂ u₂ hu₂WF ht₃t₂ pt₃u₂ pt₂u₂
  have hu₃WF : u₃.WF := GlobalState.WF.of_equiv hu₂WF.splice heq₃
  have hlive₃ : ∀ b : BlockId, t₃.id ≠ b → u₃.mem.live? b = u₂.mem.live? b :=
    fun b hb => (heq₃.live b).symm.trans (live?_splice_ne hb)
  have fbu₃ : FrameBelow s.alloc.nextFreeBlock s u₃ :=
    FrameBelow.of_equiv heq₃ (FrameBelow.splice (by omega) fbu₂)
  have pou₃ : IsFieldElemPtr u₃.mem o := isFieldElemPtr_of_live?_eq (fbu₃ o.id hno) ho
  have pt₃u₃ : IsFieldElemPtr u₃.mem t₃ :=
    ⟨fits_equiv heq₃ (by simpa using fits_splice pt₃u₂.1), pt₃u₂.2⟩

  -- `o ≔ t3`, through the out-parameter
  obtain ⟨o₄, ⟨u₄, hrun₄, heq₄⟩, hcopy₄⟩ :=
    fd_f25519_set_conforms o t₃ u₃ hu₃WF hot₃ pou₃ pt₃u₃

  refine ⟨o₄, ⟨s.popFrame u₄.mem, run_runFunction (s' := u₄) ?run, ?equiv⟩, ?value⟩

  case value =>
    intro i
    -- the value that arrived at `o` walked `a → t1 → t2 → t3 → o`
    have hread₁ : readLimb? t₁ i u₁.mem = readLimb? a i s.mem :=
      (readLimb?_of_equiv heq₁ t₁ i).symm.trans
        ((hcopy₁ i).trans (readLimb?_of_live?_eq (fb₃ a.id hna) i))
    have hread₂ : readLimb? t₂ i u₂.mem = readLimb? a i s.mem :=
      (readLimb?_of_equiv heq₂ t₂ i).symm.trans ((hcopy₂ i).trans hread₁)
    have hread₃ : readLimb? t₃ i u₃.mem = readLimb? a i s.mem :=
      (readLimb?_of_equiv heq₃ t₃ i).symm.trans ((hcopy₃ i).trans hread₂)
    exact (readLimb?_of_live?_eq (live?_splice_congr (fbu₃ o.id hno).symm) i).trans
      ((hcopy₄ i).trans hread₃)

  case equiv =>
    have hf : ∀ b : BlockId, b.id < s.alloc.nextFreeBlock → b ≠ o.id →
        u₄.mem.live? b = s.mem.live? b := by
      intro b hb hbo
      rw [(heq₄.live b).symm, live?_splice_ne (fun h => hbo h.symm)]
      exact fbu₃ b hb
    have hoval : u₄.mem.live? o.id = (s.mem.splice o o₄).live? o.id :=
      (heq₄.live o.id).symm.trans (live?_splice_congr (fbu₃ o.id hno))
    exact popFrame_equiv_splice hs hno hf hoval

  case run =>
    denote_step_all v 0
    denote_eval v 0 0
    simp only [LLVM.const?] at hv0
    subst hv0
    peel_alloca from s as s₁ with hs₁def
    peel_alloca from s₁ as s₂ with hs₂def
    peel_alloca from s₂ as s₃ with hs₃def
    rw [← ht₁def, ← ht₂def, ← ht₃def]
    peel_call hrun₁
    peel_call hrun₂
    peel_call hrun₃
    peel_call hrun₄
    simp [BlockCom.denote_term, Terminator.denote_ret, simp_denote, simp_sllvm]

end Firedancer.Ref
