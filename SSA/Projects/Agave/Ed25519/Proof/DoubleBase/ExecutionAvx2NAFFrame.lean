import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Iteration

/-! Exact register frame of each NAF loop. Every argument and every register
outside its compiler-assigned loop temporaries is retained. In particular this
preserves all global addresses, constants, scratch pointers and digit-array
pointers needed by the other emitter, table setup, point loop and final store. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR NAF NAF.RIR
set_option maxRecDepth 10000

structure RegisterFrame (lo hi : Nat) (before after : ⟪Γ⟫) : Prop where
  arguments : after.args = before.args
  values : ∀ i : Fin Γ.n, i.val < lo ∨ hi ≤ i.val → after.vals i = before.vals i

theorem RegisterFrame.refl (lo hi : Nat) (E : ⟪Γ⟫) : RegisterFrame lo hi E E :=
  ⟨rfl, fun _ _ => rfl⟩

theorem RegisterFrame.trans (hEF : RegisterFrame lo hi E F)
    (hFG : RegisterFrame lo hi F G) : RegisterFrame lo hi E G :=
  ⟨hFG.arguments.trans hEF.arguments,
    fun i hi => (hFG.values i hi).trans (hEF.values i hi)⟩

theorem RegisterFrame.weaken (h : RegisterFrame lo hi E F)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : RegisterFrame lo' hi' E F := by
  refine ⟨h.arguments, ?_⟩
  intro i hout
  exact h.values i (by omega)

theorem RegisterFrame.write {Γ : Ctx} {E F : ⟪Γ⟫} (h : RegisterFrame lo hi E F)
    (dst : Dst Γ t) (v : ⟦t⟧) (hd : lo ≤ dst.i.val ∧ dst.i.val < hi) :
    RegisterFrame lo hi E (F.write dst v) := by
  refine ⟨h.arguments, ?_⟩
  intro i hout
  have hne : i ≠ dst.i := by
    intro heq
    have hv := congrArg Fin.val heq
    omega
  simpa [Env.write, Env.set, hne] using h.values i hout

theorem RegisterFrame.read {Γ : Ctx} {E F : ⟪Γ⟫} (h : RegisterFrame lo hi E F) (r : Reg Γ t)
    (hr : match r with
      | .arg _ _ => True
      | .val i _ => i.val < lo ∨ hi ≤ i.val) : F.read r = E.read r := by
  cases r with
  | arg i hi => simp only [Env.read, h.arguments]
  | val i hi => simp only [Env.read, h.values i hr]

theorem loadedEnv5_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 268 298 (loopEnv5 E scratch pos carry)
      (loadedEnv5 E scratch pos carry bits) := by
  unfold loadedEnv5
  dsimp only
  split_ifs
  · unfold loadResult5
    rw [loadInput_loop5]
    iterate 7 apply RegisterFrame.write (hd := by decide)
    exact RegisterFrame.refl _ _ _
  · unfold crossResult5
    rw [crossInput_load5]
    unfold loadResult5
    rw [loadInput_loop5]
    iterate 13 apply RegisterFrame.write (hd := by decide)
    exact RegisterFrame.refl _ _ _

theorem controlEnv5_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 268 298 (loopEnv5 E scratch pos carry)
      (controlEnv5 E scratch pos carry bits) := by
  unfold controlEnv5 windowResult5
  rw [windowInput_loaded5]
  iterate 4 apply RegisterFrame.write (hd := by decide)
  exact loadedEnv5_frame E scratch pos carry bits

theorem evenExitEnv5_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 268 298 (loopEnv5 E scratch pos carry)
      (evenResult5 (controlEnv5 E scratch pos carry bits) pos) := by
  unfold evenResult5
  rw [evenInput_control5]
  iterate 2 apply RegisterFrame.write (hd := by decide)
  exact controlEnv5_frame E scratch pos carry bits

theorem oddExitEnv5_frame (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 268 298 (loopEnv5 E scratch pos carry)
      (storeResult5 (controlEnv5 E scratch pos carry bits) out pos
        (sum5 (mask5 (WordWindow.rawWindow bits pos.val 5)) carry)) := by
  unfold storeResult5
  rw [storeInput_control5]
  iterate 8 apply RegisterFrame.write (hd := by decide)
  exact controlEnv5_frame E scratch pos carry bits

theorem evenNextEnv5_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 268 298 (loopEnv5 E scratch pos carry)
      (evenNextEnv5 E scratch pos carry bits) := by
  unfold evenNextEnv5
  apply RegisterFrame.write (hd := by decide)
  exact evenExitEnv5_frame E scratch pos carry bits

theorem oddNextEnv5_frame (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 268 298 (loopEnv5 E scratch pos carry)
      (oddNextEnv5 E scratch out pos carry bits) := by
  unfold oddNextEnv5
  iterate 3 apply RegisterFrame.write (hd := by decide)
  exact oddExitEnv5_frame E scratch out pos carry bits

theorem loadedEnv8_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 299 327 (loopEnv8 E scratch pos carry)
      (loadedEnv8 E scratch pos carry bits) := by
  unfold loadedEnv8
  dsimp only
  split_ifs
  · unfold loadResult8
    rw [loadInput_loop8]
    iterate 7 apply RegisterFrame.write (hd := by decide)
    exact RegisterFrame.refl _ _ _
  · unfold crossResult8
    rw [crossInput_load8]
    unfold loadResult8
    rw [loadInput_loop8]
    iterate 13 apply RegisterFrame.write (hd := by decide)
    exact RegisterFrame.refl _ _ _

theorem controlEnv8_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 299 327 (loopEnv8 E scratch pos carry)
      (controlEnv8 E scratch pos carry bits) := by
  unfold controlEnv8 windowResult8
  rw [windowInput_loaded8]
  iterate 4 apply RegisterFrame.write (hd := by decide)
  exact loadedEnv8_frame E scratch pos carry bits

theorem evenExitEnv8_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 299 327 (loopEnv8 E scratch pos carry)
      (evenResult8 (controlEnv8 E scratch pos carry bits) pos) := by
  unfold evenResult8
  rw [evenInput_control8]
  iterate 2 apply RegisterFrame.write (hd := by decide)
  exact controlEnv8_frame E scratch pos carry bits

theorem oddExitEnv8_frame (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 299 327 (loopEnv8 E scratch pos carry)
      (storeResult8 (controlEnv8 E scratch pos carry bits) out pos
        (sum8 (mask8 (WordWindow.rawWindow bits pos.val 8)) carry)) := by
  unfold storeResult8
  rw [storeInput_control8]
  iterate 6 apply RegisterFrame.write (hd := by decide)
  exact controlEnv8_frame E scratch pos carry bits

theorem evenNextEnv8_frame (E : ⟪avx2Kernel.Γ⟫) (scratch : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 299 327 (loopEnv8 E scratch pos carry)
      (evenNextEnv8 E scratch pos carry bits) := by
  unfold evenNextEnv8
  apply RegisterFrame.write (hd := by decide)
  exact evenExitEnv8_frame E scratch pos carry bits

theorem oddNextEnv8_frame (E : ⟪avx2Kernel.Γ⟫) (scratch out : Pointer)
    (pos : Fin 256) (carry : Fin 2) (bits : BitVec 320) :
    RegisterFrame 299 327 (loopEnv8 E scratch pos carry)
      (oddNextEnv8 E scratch out pos carry bits) := by
  unfold oddNextEnv8
  iterate 3 apply RegisterFrame.write (hd := by decide)
  exact oddExitEnv8_frame E scratch out pos carry bits

end Agave.Ed25519.DoubleBase.ExecutionAvx2
