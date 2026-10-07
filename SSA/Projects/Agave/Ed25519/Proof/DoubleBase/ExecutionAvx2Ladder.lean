import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2LadderState

/-! Control composition over five individual arithmetic blocks. The local
contracts below are proof obligations, not axioms or a claimed backend proof.
They concern only bb18, bb22, bb25, bb29 and bb33. All digit guards, zero paths
and decreasing backedges are executed here from their imported block proofs.
The additional context predicate carries the concrete table/scratch invariant;
its sole structural requirement is stability under writes to temporary registers. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Tables (F Represents)
set_option maxRecDepth 10000

variable {p : Avx2CFG.Primitives}

abbrev LocalContext := ⟪avx2Kernel.Γ⟫ → GlobalState → Prop

def ContextStable (ctx : LocalContext) : Prop :=
  ∀ E E' s, RegisterFrame 421 avx2Kernel.Γ.n E E' → ctx E s → ctx E' s

structure LadderReady (ctx : LocalContext) (a b : Nat) (da db : Pointer)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (pos : Fin 256) : Prop where
  control : ControlReady E da db
  cursor : E.read (%426) = .value (BitVec.ofNat 64 pos.val)
  digits : DigitMemory s da db a b
  localContext : ctx E s

theorem LadderReady.of_frame (hs : ContextStable ctx)
    (h : LadderReady ctx a b da db E s pos)
    (hf : RegisterFrame 427 avx2Kernel.Γ.n E E') :
    LadderReady ctx a b da db E' s pos :=
  ⟨h.control.of_frame hf, cursor_of_frame pos hf h.cursor, h.digits,
    hs E E' s (hf.weaken (by decide) (Nat.le_refl _)) h.localContext⟩

def signedPoint (table : TableIndex → Extended F) (side : Bool)
    (digit : Int) (Q : Extended F) : Extended F :=
  (digitOps side digit).foldl (avx2Step table) Q

def digitBlockA (digit : Int) : Fin 35 :=
  if digit < 0 then 20 else if digit = 0 then 26 else 23

def doubleStage (digit : Int) : PointStage := if digit = 0 then .afterA else .doubled

/-- A finite, successful local block execution and its exact continuation. -/
structure ArithmeticBlockPost (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (ctx : LocalContext) (a b : Nat) (da db : Pointer)
    (source target : Fin 35) (stage : PointStage) (Q : Extended F)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (pos : Fin 256)
    (E' : ⟪avx2Kernel.Γ⟫) (s' : GlobalState) : Prop where
  block : ((avx2Kernel p g).blocks source).run avx2Kernel.blockParams E s =
    .value ((E', .inr target), s')
  ready : LadderReady ctx a b da db E' s' pos
  point : PointAt stage E' Q
  registers : RegisterFrame 427 avx2Kernel.Γ.n E E'

theorem ArithmeticBlockPost.run (h : ArithmeticBlockPost p g ctx a b da db
    source target stage Q E s pos E' s') :
    (avx2Kernel p g).runFrom E source s = (avx2Kernel p g).runFrom E' target s' := by
  rw [Func.runFrom_eq, h.block]
  rfl

/-- Precisely the five arithmetic block obligations. Sign/index computation,
loads of B digits, all four index guards and loop termination are absent from
these premises and are discharged by the control composition below. -/
structure ArithmeticBlocks (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (ctx : LocalContext) (a b : Nat) (da db : Pointer)
    (table : TableIndex → Extended F) : Prop where
  double : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .loop E Q →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 18
      (digitBlockA (nafDigits 5 a pos.val)) (doubleStage (nafDigits 5 a pos.val))
      (avx2Double Q) E s pos E' s' ∧
      E'.read (%523) = .value (Execution.nafByte 5 a pos.val)
  subA : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .doubled E Q →
    nafDigits 5 a pos.val < 0 →
    E.read (%527) = .value (BitVec.ofNat 64 ((nafMagnitude5 a pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 22 26 .afterA
      (signedPoint table false (nafDigits 5 a pos.val) Q) E s pos E' s'
  addA : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .doubled E Q →
    0 < nafDigits 5 a pos.val →
    E.read (%625) = .value (BitVec.ofNat 64 ((nafMagnitude5 a pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 25 26 .afterA
      (signedPoint table false (nafDigits 5 a pos.val) Q) E s pos E' s'
  subB : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .afterA E Q →
    nafDigits 8 b pos.val < 0 →
    E.read (%708) = .value (BitVec.ofNat 64 ((nafMagnitude8 b pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 29 30 .afterB
      (signedPoint table true (nafDigits 8 b pos.val) Q) E s pos E' s'
  addB : ∀ E s pos Q, LadderReady ctx a b da db E s pos → PointAt .afterA E Q →
    0 < nafDigits 8 b pos.val →
    E.read (%813) = .value (BitVec.ofNat 64 ((nafMagnitude8 b pos.val).val / 2)) →
    ∃ E' s', ArithmeticBlockPost p g ctx a b da db 33 30 .afterB
      (signedPoint table true (nafDigits 8 b pos.val) Q) E s pos E' s'

/-- Width-five guard inputs follow from the already loaded signed NAF byte. -/
theorem negative5_ready (h : ControlReady E da db)
    (hr : E.read (%523) = .value (Execution.nafByte 5 a pos))
    (hn : nafDigits 5 a pos < 0) : negative5Input E (nafMagnitude5 a pos) = E := by
  have hd : E.read (%523) = .value (-BitVec.ofNat 8 (nafMagnitude5 a pos).val) := by
    rw [hr, (naf5_magnitude_cases a pos).2 (le_of_lt hn)]
  unfold negative5Input
  rw [Env.write_of_read E (%1) h.zeroByte, Env.write_of_read E (%10) h.one,
    Env.write_of_read E (%117) h.limit5, Env.write_of_read E (%523) hd]

theorem positive5_ready (h : ControlReady E da db)
    (hr : E.read (%523) = .value (Execution.nafByte 5 a pos))
    (hn : 0 ≤ nafDigits 5 a pos) : positive5Input E (nafMagnitude5 a pos) = E := by
  have hd : E.read (%523) = .value (BitVec.ofNat 8 (nafMagnitude5 a pos).val) := by
    rw [hr, (naf5_magnitude_cases a pos).1 hn]
  unfold positive5Input
  rw [Env.write_of_read E (%10) h.one, Env.write_of_read E (%117) h.limit5,
    Env.write_of_read E (%523) hd]

theorem negative5_frame (h : ControlReady E da db)
    (hr : E.read (%523) = .value (Execution.nafByte 5 a pos))
    (hn : nafDigits 5 a pos < 0) :
    RegisterFrame 427 avx2Kernel.Γ.n E (negative5Result E (nafMagnitude5 a pos)) := by
  unfold negative5Result
  rw [negative5_ready h hr hn]
  iterate 4 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem positive5_frame (h : ControlReady E da db)
    (hr : E.read (%523) = .value (Execution.nafByte 5 a pos))
    (hn : 0 ≤ nafDigits 5 a pos) :
    RegisterFrame 427 avx2Kernel.Γ.n E (positive5Result E (nafMagnitude5 a pos)) := by
  unfold positive5Result
  rw [positive5_ready h hr hn]
  iterate 3 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

/-- Actual bb18 and the selected width-five sign/guard/arithmetic path. -/
theorem double_and_A_run (hc : ArithmeticBlocks p g ctx a b da db table)
    (hs : ContextStable ctx) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (pos : Fin 256) (Q : Extended F) (hr : LadderReady ctx a b da db E s pos)
    (hp : PointAt .loop E Q) :
    ∃ E' s', (avx2Kernel p g).runFrom E 18 s = (avx2Kernel p g).runFrom E' 26 s' ∧
      LadderReady ctx a b da db E' s' pos ∧
      PointAt .afterA E' (signedPoint table false (nafDigits 5 a pos.val) (avx2Double Q)) := by
  obtain ⟨ED, sd, hd, hbyte⟩ := hc.double E s pos Q hr hp
  have hdrun := hd.run
  by_cases hn : nafDigits 5 a pos.val < 0
  · have hnz : nafDigits 5 a pos.val ≠ 0 := by omega
    have hpoint : PointAt .doubled ED (avx2Double Q) := by simpa [doubleStage, hnz] using hd.point
    have hg := negative5_run p g ED (nafMagnitude5 a pos.val) sd
    rw [negative5_ready hd.ready.control hbyte hn] at hg
    have hfr := negative5_frame hd.ready.control hbyte hn
    obtain ⟨E', s', hout⟩ := hc.subA _ sd pos (avx2Double Q)
      (hd.ready.of_frame hs hfr) (hpoint.negative5Result _) hn
      (by simp [negative5Result, mlir_env])
    refine ⟨E', s', ?_, hout.ready, hout.point⟩
    have hdrun' : (avx2Kernel p g).runFrom E 18 s =
        (avx2Kernel p g).runFrom ED 20 sd := by
      simpa [digitBlockA, hn] using hdrun
    exact hdrun'.trans (hg.trans hout.run)
  · by_cases hz : nafDigits 5 a pos.val = 0
    · refine ⟨ED, sd, ?_, hd.ready, ?_⟩
      · simpa [digitBlockA, hn, hz] using hdrun
      · simpa [doubleStage, signedPoint, hz, digitOps] using hd.point
    · have hpos : 0 < nafDigits 5 a pos.val := by omega
      have hpoint : PointAt .doubled ED (avx2Double Q) := by simpa [doubleStage, hz] using hd.point
      have hg := positive5_run p g ED (nafMagnitude5 a pos.val) sd
      rw [positive5_ready hd.ready.control hbyte (le_of_lt hpos)] at hg
      have hfr := positive5_frame hd.ready.control hbyte (le_of_lt hpos)
      obtain ⟨E', s', hout⟩ := hc.addA _ sd pos (avx2Double Q)
        (hd.ready.of_frame hs hfr) (hpoint.positive5Result _) hpos
        (by simp [positive5Result, mlir_env])
      refine ⟨E', s', ?_, hout.ready, hout.point⟩
      have hdrun' : (avx2Kernel p g).runFrom E 18 s =
          (avx2Kernel p g).runFrom ED 23 sd := by
        simpa [digitBlockA, hn, hz] using hdrun
      exact hdrun'.trans (hg.trans hout.run)

theorem dispatchB_frame (h : ControlReady E da db)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) (digit : BitVec 8) :
    RegisterFrame 427 avx2Kernel.Γ.n E (dispatchBResult E db pos digit) := by
  unfold dispatchBResult
  rw [dispatchBInput_of_ready E da db pos h hpos]
  iterate 3 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem dispatchBZero_frame (h : ControlReady E da db)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) (digit : BitVec 8) :
    RegisterFrame 427 avx2Kernel.Γ.n E (dispatchBZero E db pos digit) := by
  unfold dispatchBZero
  iterate 5 apply RegisterFrame.write (hd := by decide)
  exact dispatchB_frame h hpos digit

theorem dispatchB_negative_frame (h : ControlReady E da db)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val))
    (hn : nafDigits 8 b pos.val < 0) :
    RegisterFrame 427 avx2Kernel.Γ.n E
      (negative8Result (dispatchBResult E db pos (Execution.nafByte 8 b pos.val))
        (nafMagnitude8 b pos.val)) := by
  unfold negative8Result
  rw [dispatchB_negative_ready E db pos b h.one h.minusByte hn]
  iterate 4 apply RegisterFrame.write (hd := by decide)
  exact dispatchB_frame h hpos _

theorem dispatchB_positive_frame (h : ControlReady E da db)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val))
    (hn : 0 ≤ nafDigits 8 b pos.val) :
    RegisterFrame 427 avx2Kernel.Γ.n E
      (positive8Result (dispatchBResult E db pos (Execution.nafByte 8 b pos.val))
        (nafMagnitude8 b pos.val)) := by
  unfold positive8Result
  rw [dispatchB_positive_ready E db pos b h.one h.minusByte hn]
  iterate 3 apply RegisterFrame.write (hd := by decide)
  exact dispatchB_frame h hpos _

/-- B's byte load, signed switch, index guards and selected arithmetic block.
The zero branch transfers the packed point to bb30 without any field call. -/
theorem B_run (hc : ArithmeticBlocks p g ctx a b da db table)
    (hs : ContextStable ctx) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (pos : Fin 256) (Q : Extended F) (hr : LadderReady ctx a b da db E s pos)
    (hp : PointAt .afterA E Q) :
    ∃ E' s', (avx2Kernel p g).runFrom E 26 s = (avx2Kernel p g).runFrom E' 30 s' ∧
      LadderReady ctx a b da db E' s' pos ∧
      PointAt .afterB E' (signedPoint table true (nafDigits 8 b pos.val) Q) := by
  have hd := dispatchB_naf_guard_run p g E db pos b s hr.digits.bufferB
    (hr.digits.readB pos) hr.control.one hr.control.minusByte
  rw [dispatchBInput_of_ready E da db pos hr.control hr.cursor] at hd
  by_cases hn : nafDigits 8 b pos.val < 0
  · rw [if_pos hn] at hd
    have hf := dispatchB_negative_frame hr.control hr.cursor hn
    obtain ⟨E', s', hout⟩ := hc.subB _ s pos Q (hr.of_frame hs hf)
      ((hp.dispatchBResult db pos _).negative8Result _) hn
      (by simp [negative8Result, mlir_env])
    exact ⟨E', s', hd.trans hout.run, hout.ready, hout.point⟩
  · rw [if_neg hn] at hd
    by_cases hz : Execution.nafByte 8 b pos.val = 0#8
    · rw [if_pos hz] at hd
      have hzero : nafDigits 8 b pos.val = 0 := by
        have ht := Execution.nafByte_toInt 8 (Or.inr rfl) b pos.val
        rw [hz] at ht
        simpa using ht.symm
      refine ⟨_, s, hd, hr.of_frame hs (dispatchBZero_frame hr.control hr.cursor _), ?_⟩
      simpa [signedPoint, hzero, digitOps] using hp.dispatchBZero db pos (Execution.nafByte 8 b pos.val)
    · rw [if_neg hz] at hd
      have hnonzero : nafDigits 8 b pos.val ≠ 0 := by
        intro heq
        exact hz (by simp [Execution.nafByte, heq])
      have hpositive : 0 < nafDigits 8 b pos.val := by omega
      have hf := dispatchB_positive_frame hr.control hr.cursor (le_of_lt hpositive)
      obtain ⟨E', s', hout⟩ := hc.addB _ s pos Q (hr.of_frame hs hf)
        ((hp.dispatchBResult db pos _).positive8Result _) hpositive
        (by simp [positive8Result, mlir_env])
      exact ⟨E', s', hd.trans hout.run, hout.ready, hout.point⟩

/-- One full iteration is proved from the five local arithmetic-block
obligations and the real guards above. It is not an assumed loop contract. -/
theorem round_run (hc : ArithmeticBlocks p g ctx a b da db table)
    (hs : ContextStable ctx) (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState)
    (pos : Fin 256) (Q : Extended F) (hr : LadderReady ctx a b da db E s pos)
    (hp : PointAt .loop E Q) :
    ∃ E' s', (avx2Kernel p g).runFrom E 18 s = (avx2Kernel p g).runFrom E' 30 s' ∧
      LadderReady ctx a b da db E' s' pos ∧
      PointAt .afterB E' ((roundOps (nafDigits 5 a) (nafDigits 8 b) pos.val).foldl
        (avx2Step table) Q) := by
  obtain ⟨EA, sa, hA, hrA, hpA⟩ := double_and_A_run hc hs E s pos Q hr hp
  obtain ⟨EB, sb, hB, hrB, hpB⟩ := B_run hc hs EA sa pos _ hrA hpA
  refine ⟨EB, sb, hA.trans hB, hrB, ?_⟩
  simpa only [roundOps, List.foldl_append, List.foldl_cons, List.foldl_nil,
    avx2Step, signedPoint] using hpB

theorem backedgeResult_frame (hr : ControlReady E da db)
    (hc : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    RegisterFrame 427 avx2Kernel.Γ.n E (backedgeResult E pos) := by
  unfold backedgeResult
  rw [backedgeInput_of_ready E da db pos hr hc]
  iterate 2 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem backedgeNext_frame (hr : ControlReady E da db)
    (hc : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    RegisterFrame 421 avx2Kernel.Γ.n E (backedgeNext E pos) := by
  unfold backedgeNext
  iterate 6 apply RegisterFrame.write (hd := by decide)
  exact (backedgeResult_frame hr hc).weaken (by decide) (Nat.le_refl _)

/-- The inclusive descending loop executes the chosen highest digit through
zero, then reaches the real output block. Decrease and non-underflow of the
executed backedge are proved from the finite cursor, not assumed. -/
theorem ladder_run (hc : ArithmeticBlocks p g ctx a b da db table)
    (hs : ContextStable ctx) (n : Nat) (hn : n < 256)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (Q : Extended F)
    (hr : LadderReady ctx a b da db E s ⟨n, hn⟩) (hp : PointAt .loop E Q) :
    ∃ E' s', (avx2Kernel p g).runFrom E 18 s = (avx2Kernel p g).runFrom E' 34 s' ∧
      LadderReady ctx a b da db E' s' 0 ∧
      PointAt .afterB E' (run (avx2Step table) (nafDigits 5 a) (nafDigits 8 b) n Q) := by
  induction n generalizing E s Q with
  | zero =>
    obtain ⟨ER, sr, hround, hready, hpoint⟩ := round_run hc hs E s ⟨0, hn⟩ Q hr hp
    have hback := backedge_point_run p g ER sr da db ⟨0, hn⟩ _
      hready.control hpoint hready.cursor
    simp only [Fin.val_mk, if_pos rfl] at hback
    refine ⟨backedgeResult ER ⟨0, hn⟩, sr, hround.trans hback, ?_, ?_⟩
    · exact hready.of_frame hs (backedgeResult_frame hready.control hready.cursor)
    · exact hpoint.backedgeResult _
  | succ n ih =>
    obtain ⟨ER, sr, hround, hready, hpoint⟩ := round_run hc hs E s ⟨n + 1, hn⟩ Q hr hp
    have hback := backedge_point_run p g ER sr da db ⟨n + 1, hn⟩ _
      hready.control hpoint hready.cursor
    simp only [Fin.val_mk, Nat.succ_ne_zero, if_false] at hback
    have hnext : LadderReady ctx a b da db (backedgeNext ER ⟨n + 1, hn⟩) sr
        ⟨n, by omega⟩ :=
      ⟨hready.control.backedgeNext _, backedgeNext_cursor ER n hn, hready.digits,
        hs _ _ sr (backedgeNext_frame hready.control hready.cursor) hready.localContext⟩
    obtain ⟨E', s', hrest, hr', hp'⟩ := ih (by omega) _ sr _ hnext (hpoint.backedgeNext _)
    exact ⟨E', s', hround.trans (hback.trans hrest), hr', hp'⟩

/-- The separately proved per-operation group invariant applies to the
accumulator produced by the actual imported descending CFG. -/
theorem ladder_run_represents {A : Extended F} {V : GroupPoint}
    (hA : Represents A V)
    (hc : ArithmeticBlocks p g ctx a b da db (finiteTable (Tables.avx2DoubleBaseTable A)))
    (hs : ContextStable ctx) (n : Nat) (hn : n < 256)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (Q : Extended F) (X : GroupPoint)
    (hr : LadderReady ctx a b da db E s ⟨n, hn⟩) (hp : PointAt .loop E Q)
    (hQ : Represents Q X) :
    ∃ E' s' R,
      (avx2Kernel p g).runFrom E 18 s = (avx2Kernel p g).runFrom E' 34 s' ∧
      LadderReady ctx a b da db E' s' 0 ∧ PointAt .afterB E' R ∧
      Represents R (groupLadder V Tables.baseGroup X (nafDigits 5 a) (nafDigits 8 b) n) := by
  obtain ⟨E', s', hrun, hready, hpoint⟩ := ladder_run hc hs n hn E s Q hr hp
  exact ⟨E', s', _, hrun, hready, hpoint, represents_avx2_run_naf hA a b n hQ⟩

end Agave.Ed25519.DoubleBase.ExecutionAvx2
