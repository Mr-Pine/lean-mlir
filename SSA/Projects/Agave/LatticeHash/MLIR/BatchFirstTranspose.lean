import SSA.Projects.Agave.LatticeHash.MLIR.BatchTranspose

namespace AgaveLatticeHash.MLIR.BatchFirstTranspose
open LeanMLIR SLLVM Firedancer
open InstCombine (LLVM)
open Blake3Compression
open BatchTranspose (Row8 Row8Ty)
private abbrev blockInput {Γ Γout : Ctxt SLLVM.Ty} {rets sigs}
    (_ : BlockCom Γ Γout rets sigs) := Γ
abbrev InCtx8 := blockInput agave_batch_8.cfgBlock_1

private theorem hvConsAppend {Γ : Ctxt SLLVM.Ty} {ts : List SLLVM.Ty} {t : SLLVM.Ty}
    (x : TyDenote.toType t) (xs : HVector TyDenote.toType ts) (V : Γ.Valuation) :
    (x ::ₕ xs) ++ V = x ::ᵥ (xs ++ V) := by
  exact Ctxt.Valuation.cons_append
private theorem hvNilAppend {Γ : Ctxt SLLVM.Ty} (V : Γ.Valuation) :
    (HVector.nil : HVector TyDenote.toType ([] : List SLLVM.Ty)) ++ V = V := rfl

private theorem targetIte {Γ : Ctxt SLLVM.Ty} {sigs} (V : Γ.Valuation)
    (p : Prop) [Decidable p] (a b : Target Γ sigs) :
    (if p then a else b).denote V = if p then a.denote V else b.denote V := by
  split <;> rfl

private theorem shuffle0 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 8, 1, 9, 4, 12, 5, 13] a b = #v[a[0], b[0], a[1], b[1], a[4], b[4], a[5], b[5]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle1 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 10, 3, 11, 6, 14, 7, 15] a b = #v[a[2], b[2], a[3], b[3], a[6], b[6], a[7], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle2 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 8, 9, 4, 5, 12, 13] a b = #v[a[0], a[1], b[0], b[1], a[4], a[5], b[4], b[5]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle3 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [2, 3, 10, 11, 6, 7, 14, 15] a b = #v[a[2], a[3], b[2], b[3], a[6], a[7], b[6], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle4 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [0, 1, 2, 3, 8, 9, 10, 11] a b = #v[a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

private theorem shuffle5 (a b : Row8) :
    LLVM.Ty.shufflevector (e := .bitvec (.concrete 32)) [4, 5, 6, 7, 12, 13, 14, 15] a b = #v[a[4], a[5], a[6], a[7], b[4], b[5], b[6], b[7]] := by
  ext i hi
  change i < 8 at hi
  interval_cases i <;> rfl

/-- Mathematical columns, with per-lane poison preserved. -/
def transposeRows8 (rows : Vector Row8 8) : Vector Row8 8 :=
  Vector.ofFn (fun col => Vector.ofFn (fun row => rows[row][col]))

private theorem transposeRows8_cols (rows : Vector Row8 8) :
    transposeRows8 rows = #v[#v[rows[0][0], rows[1][0], rows[2][0], rows[3][0], rows[4][0], rows[5][0], rows[6][0], rows[7][0]], #v[rows[0][1], rows[1][1], rows[2][1], rows[3][1], rows[4][1], rows[5][1], rows[6][1], rows[7][1]], #v[rows[0][2], rows[1][2], rows[2][2], rows[3][2], rows[4][2], rows[5][2], rows[6][2], rows[7][2]], #v[rows[0][3], rows[1][3], rows[2][3], rows[3][3], rows[4][3], rows[5][3], rows[6][3], rows[7][3]], #v[rows[0][4], rows[1][4], rows[2][4], rows[3][4], rows[4][4], rows[5][4], rows[6][4], rows[7][4]], #v[rows[0][5], rows[1][5], rows[2][5], rows[3][5], rows[4][5], rows[5][5], rows[6][5], rows[7][5]], #v[rows[0][6], rows[1][6], rows[2][6], rows[3][6], rows[4][6], rows[5][6], rows[6][6], rows[7][6]], #v[rows[0][7], rows[1][7], rows[2][7], rows[3][7], rows[4][7], rows[5][7], rows[6][7], rows[7][7]]] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> apply Vector.ext
  all_goals intro j hj
  all_goals interval_cases j <;> simp [transposeRows8]

def next8 (V : InCtx8.Valuation) (cols : Vector Row8 8) (off : LLVM.IntW 64) :
    SuccArgs agave_batch_8.cfgSigs :=
  ⟨2, rfl, V ⟨34, rfl⟩ ::ₕ
    V ⟨33, rfl⟩ ::ₕ
    V ⟨32, rfl⟩ ::ₕ
    V ⟨31, rfl⟩ ::ₕ
    V ⟨30, rfl⟩ ::ₕ
    V ⟨29, rfl⟩ ::ₕ
    V ⟨28, rfl⟩ ::ₕ
    V ⟨27, rfl⟩ ::ₕ
    V ⟨26, rfl⟩ ::ₕ
    V ⟨25, rfl⟩ ::ₕ
    V ⟨24, rfl⟩ ::ₕ
    V ⟨23, rfl⟩ ::ₕ
    V ⟨22, rfl⟩ ::ₕ
    V ⟨19, rfl⟩ ::ₕ
    V ⟨18, rfl⟩ ::ₕ
    V ⟨17, rfl⟩ ::ₕ
    V ⟨16, rfl⟩ ::ₕ
    V ⟨15, rfl⟩ ::ₕ
    V ⟨14, rfl⟩ ::ₕ
    V ⟨13, rfl⟩ ::ₕ
    V ⟨12, rfl⟩ ::ₕ
    V ⟨11, rfl⟩ ::ₕ
    V ⟨10, rfl⟩ ::ₕ
    V ⟨9, rfl⟩ ::ₕ
    V ⟨8, rfl⟩ ::ₕ
    V ⟨7, rfl⟩ ::ₕ
    V ⟨6, rfl⟩ ::ₕ
    cols[0] ::ₕ
    cols[1] ::ₕ
    cols[2] ::ₕ
    cols[3] ::ₕ
    cols[4] ::ₕ
    cols[5] ::ₕ
    cols[6] ::ₕ
    cols[7] ::ₕ
    off ::ₕ HVector.nil⟩

def panic8 (off : LLVM.IntW 64) : SuccArgs agave_batch_8.cfgSigs :=
  ⟨17, rfl, [off]ₕ⟩

def nextOffset8 (V : InCtx8.Valuation) : LLVM.IntW 64 :=
  LLVM.add (V ⟨20, rfl⟩) (V ⟨86, rfl⟩) {nsw := true, nuw := true}

/-- Two final first-half loads, mathematical transpose, then the compiler's
first second-half bounds guard with exact successor arguments. -/
def first8Spec (V : InCtx8.Valuation) :
    EffectM (HVector TyDenote.toType ([] : List SLLVM.Ty) ⊕ SuccArgs agave_batch_8.cfgSigs) := do
  let x0 : Row8 := V ⟨5, rfl⟩
  let x1 : Row8 := V ⟨4, rfl⟩
  let x2 : Row8 := V ⟨3, rfl⟩
  let x3 : Row8 := V ⟨2, rfl⟩
  let x4 : Row8 := V ⟨1, rfl⟩
  let x5 : Row8 := V ⟨0, rfl⟩
  let x6 : Row8 ← liftM (load (gep (V ⟨52, rfl⟩) 4 0 (V ⟨8, rfl⟩)) Row8Ty)
  let x7 : Row8 ← liftM (load (gep (V ⟨51, rfl⟩) 4 0 (V ⟨6, rfl⟩)) Row8Ty)
  let y0 : Row8 := #v[x0[0], x1[0], x2[0], x3[0], x4[0], x5[0], x6[0], x7[0]]
  let y1 : Row8 := #v[x0[1], x1[1], x2[1], x3[1], x4[1], x5[1], x6[1], x7[1]]
  let y2 : Row8 := #v[x0[2], x1[2], x2[2], x3[2], x4[2], x5[2], x6[2], x7[2]]
  let y3 : Row8 := #v[x0[3], x1[3], x2[3], x3[3], x4[3], x5[3], x6[3], x7[3]]
  let y4 : Row8 := #v[x0[4], x1[4], x2[4], x3[4], x4[4], x5[4], x6[4], x7[4]]
  let y5 : Row8 := #v[x0[5], x1[5], x2[5], x3[5], x4[5], x5[5], x6[5], x7[5]]
  let y6 : Row8 := #v[x0[6], x1[6], x2[6], x3[6], x4[6], x5[6], x6[6], x7[6]]
  let y7 : Row8 := #v[x0[7], x1[7], x2[7], x3[7], x4[7], x5[7], x6[7], x7[7]]
  let cols := #v[y0,y1,y2,y3,y4,y5,y6,y7]
  match LLVM.icmp .ugt (V ⟨21, rfl⟩) (V ⟨85, rfl⟩) with
  | .poison => throwUB
  | .value b => pure (.inr (if b = 1 then panic8 (nextOffset8 V)
      else next8 V cols (nextOffset8 V)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem first8_denote (V : InCtx8.Valuation) :
    (do let (_, r) ← agave_batch_8.cfgBlock_1.denote V; pure r) = first8Spec V := by
  simp only [first8Spec, BlockCom.denote, Terminator.denote, targetIte,
    next8, panic8, nextOffset8, simp_denote, simp_sllvm, bind_map_left]
  simp only [hvConsAppend, hvNilAppend, simp_spine]
  simp only [shuffle0, shuffle1, shuffle2, shuffle3, shuffle4, shuffle5,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [bind_pure]
  rfl

structure Env8 (V : InCtx8.Valuation) (p6 p7 : Pointer)
    (rows : Vector (Vector Word 8) 8) (off : BitVec 64) : Prop where
  load6 : gep (V ⟨52, rfl⟩) 4 0 (V ⟨8, rfl⟩) = .value p6
  load7 : gep (V ⟨51, rfl⟩) 4 0 (V ⟨6, rfl⟩) = .value p7
  row0 : V ⟨5, rfl⟩ = (rows[0]).map PoisonOr.value
  row1 : V ⟨4, rfl⟩ = (rows[1]).map PoisonOr.value
  row2 : V ⟨3, rfl⟩ = (rows[2]).map PoisonOr.value
  row3 : V ⟨2, rfl⟩ = (rows[3]).map PoisonOr.value
  row4 : V ⟨1, rfl⟩ = (rows[4]).map PoisonOr.value
  row5 : V ⟨0, rfl⟩ = (rows[5]).map PoisonOr.value
  offset : V ⟨21, rfl⟩ = .value off
  limit : V ⟨85, rfl⟩ = .value 995#64

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem first8Spec_run (V : InCtx8.Valuation) (p6 p7 : Pointer)
    (rows : Vector (Vector Word 8) 8) (off : BitVec 64)
    (hV : Env8 V p6 p7 rows off) (hb : off.toNat ≤ 960) (s : GlobalState)
    (hf6 : Fits s.mem p6 256) (hr6 : readWord? p6 256 s.mem = some (packBits rows[6]))
    (hf7 : Fits s.mem p7 256) (hr7 : readWord? p7 256 s.mem = some (packBits rows[7])) :
    StateT.run (first8Spec V) s =
      .value (.inr (next8 V (transposeRows8 (rows.map (·.map PoisonOr.value))) (nextOffset8 V)), s) := by
  have hc : LLVM.icmp .ugt (.value off) (.value 995#64) = .value 0#1 := by
    have hn : ¬995 < off.toNat := by omega
    simp [LLVM.icmp, LLVM.icmp?, LLVM.icmp', BitVec.ult, hn]
  unfold first8Spec
  simp only [hV.load6, hV.load7, hV.offset, hV.limit, hc, hV.row0, hV.row1, hV.row2, hV.row3, hV.row4, hV.row5]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[6] hf6 hr6)]
  simp only [PoisonOr.value_bind]
  rw [EffectM.run_bind, run_liftM (s := s) (run_load_vector rows[7] hf7 hr7)]
  simp only [PoisonOr.value_bind, Vector.getElem_map, show ¬(0#1 = 1) by decide, ↓reduceIte]
  rw [transposeRows8_cols]
  simp only [Vector.getElem_map]
  rfl

private theorem run_of_project {α β : Type} (x : EffectM (α × β))
    (s t : GlobalState) (b : β)
    (h : StateT.run (do let (_, r) ← x; pure r) s = .value (b, t)) :
    ∃ a, StateT.run x s = .value ((a, b), t) := by
  cases hx : StateT.run x s using PoisonOr.casesOn' with
  | poison =>
    simp only [EffectM.run_bind, hx, PoisonOr.poison_bind] at h
    exact (PoisonOr.poison_ne_value _ h).elim
  | value val =>
    rcases val with ⟨⟨a, b'⟩, t'⟩
    simp only [EffectM.run_bind, hx, PoisonOr.value_bind, EffectM.run_pure,
      PoisonOr.value_inj, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨a, rfl⟩

/-- The actual first-half transpose block returns its eight mathematical
columns and exact live arguments, with no memory change; its panic edge is
excluded for every legal lane offset. -/
theorem first8_run (V : InCtx8.Valuation) (p6 p7 : Pointer)
    (rows : Vector (Vector Word 8) 8) (off : BitVec 64)
    (hV : Env8 V p6 p7 rows off) (hb : off.toNat ≤ 960) (s : GlobalState)
    (hf6 : Fits s.mem p6 256) (hr6 : readWord? p6 256 s.mem = some (packBits rows[6]))
    (hf7 : Fits s.mem p7 256) (hr7 : readWord? p7 256 s.mem = some (packBits rows[7])) :
    ∃ V', StateT.run (agave_batch_8.cfgBlock_1.denote V) s =
      .value ((V', .inr (next8 V (transposeRows8 (rows.map (·.map PoisonOr.value))) (nextOffset8 V))), s) := by
  apply run_of_project
  rw [first8_denote]
  exact first8Spec_run V p6 p7 rows off hV hb s hf6 hr6 hf7 hr7

end AgaveLatticeHash.MLIR.BatchFirstTranspose
