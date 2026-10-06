import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionPoint
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionSuffix

/-! The actual Dalek body from R decompression through return, with arbitrary
R and S bytes. All assumptions describe primitive calls, layouts, or memory. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

structure BodyRegisters (q : TailPointers) (z : PointPointers) (scratch : Pointer)
    (E : Env program.Γ) : Prop where
  tail : TailRegisters q E
  point : PointRegisters z E
  scratch : E.read (%20) = .value scratch
  sixtyThree : E.read (%12) = .value 63#64
  thirtyThree : E.read (%15) = .value 33#64
  one : E.read (%16) = .value 1#64
  thirtyOne : E.read (%17) = .value 31#64

structure BodyMemory (q : TailPointers) (z : PointPointers) (scratch : Pointer)
    (state : GlobalState) (layout : Layout Point Scalar Result)
    (h : Scalar) (a : Point) (r bytes : Bytes32) : Prop where
  tail : TailBeforeCopy q state layout h a r
  signature : SmallRange state.mem q.signature 64
  scalarBytes : ReadBytes state (q.signature.add 32#64) 32 bytes
  scratch : SmallRange state.mem scratch 32
  cache : SmallRange state.mem q.cache 1
  option : SmallRange state.mem z.option 168
  slot29 : SmallRange state.mem z.slot29 166
  slot30 : SmallRange state.mem z.slot30 166
  point : SmallRange state.mem z.point 160
  cofactor : SmallRange state.mem z.cofactor 160
  identity : SmallRange state.mem z.identity 160
  one : ReadBytes state z.one 40 (1#320)

def bodyReaders (q : TailPointers) (z : PointPointers) : List Pointer :=
  [q.challenge, q.point, q.signature, q.signature.add 32#64, z.one]

def pointDestinations (z : PointPointers) : List Pointer :=
  [z.slot29, z.slot30, z.point, z.cofactor, z.identity]

/-- Explicit allocation separation for the body. It includes no validity
condition on R or S and no proposition about program execution. -/
structure BodyDisjoint (q : TailPointers) (z : PointPointers) (scratch : Pointer) : Prop where
  point : PointDisjoint z
  inputOutput : ∀ ptr ∈ bodyReaders q z, ∀ dst ∈ z.option :: pointDestinations z,
    ptr.id ≠ dst.id
  scratchSignature : scratch.id ≠ q.signature.id
  challengeScratch : q.challenge.id ≠ scratch.id
  pointScratch : q.point.id ≠ scratch.id
  signatureScalar : q.signature.id ≠ q.scalar.id
  cache : CacheDisjoint q

theorem BodyRegisters.decompress {q : TailPointers} {z : PointPointers}
    {scratch : Pointer} {E : Env program.Γ} (hr : BodyRegisters q z scratch E) (success : Bool) :
    BodyRegisters q z scratch
      (E[%39 := .value (if success then 1#64 else 0#64),
        %40 := .value (BitVec.ofBool success)]) := by
  rcases hr with ⟨ht, hp, hs, h63, h33, h1, h31⟩
  rcases ht with ⟨ho, hc, hh, ha, hsc, hsig, hk, hl, hz, hone, hok, he⟩
  change E.args 1 = .value q.signature at hsig
  rcases hp with ⟨hop, h29, h30, hrp, hco, hid, hglob, h3, h0, h40, h80, h120, herr, h8, h6, h160⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp [mlir_env, *]
  · constructor <;> simp [mlir_env, *]
  all_goals simp [mlir_env, *]

theorem BodyRegisters.pointCheck {q : TailPointers} {z : PointPointers}
    {scratch : Pointer} {E : Env program.Γ} (hr : BodyRegisters q z scratch E) (small : Bool) :
    BodyRegisters q z scratch (pointBlockEnv E z small) := by
  rcases hr with ⟨ht, hp, hs, h63, h33, h1, h31⟩
  rcases ht with ⟨ho, hc, hh, ha, hsc, hsig, hk, hl, hz, hone, hok, he⟩
  change E.args 1 = .value q.signature at hsig
  rcases hp with ⟨hop, h29, h30, hrp, hco, hid, hglob, h3, h0, h40, h80, h120, herr, h8, h6, h160⟩
  cases small <;> (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try { constructor <;> simp [pointBlockEnv, mlir_env, *] }
  all_goals simp [pointBlockEnv, mlir_env, *]

theorem BodyMemory.decompressFrame {Point Scalar Result : Type}
    {q : TailPointers} {z : PointPointers} {scratch : Pointer} {state after : GlobalState}
    {layout : Layout Point Scalar Result} {h : Scalar} {a : Point} {r bytes : Bytes32}
    (hm : BodyMemory q z scratch state layout h a r bytes)
    (hf : OutputFrame state after z.option 168) (hd : BodyDisjoint q z scratch) :
    BodyMemory q z scratch after layout h a r bytes := by
  have hread (ptr : Pointer) (hp : ptr ∈ bodyReaders q z) (w : Nat) :
      after.mem.readAt ptr w = state.mem.readAt ptr w :=
    hf.read ptr w (Range.disjoint_of_id_ne (hd.inputOutput ptr hp z.option (by simp)))
  refine ⟨hm.tail.frame hf ?_ ?_ ?_, hf.live _ _ hm.signature, ?_, hf.live _ _ hm.scratch,
    hf.live _ _ hm.cache, hf.live _ _ hm.option, hf.live _ _ hm.slot29,
    hf.live _ _ hm.slot30, hf.live _ _ hm.point, hf.live _ _ hm.cofactor,
    hf.live _ _ hm.identity, ?_⟩
  · exact Range.disjoint_of_id_ne (hd.inputOutput q.challenge (by simp [bodyReaders]) z.option (by simp))
  · exact Range.disjoint_of_id_ne (hd.inputOutput q.point (by simp [bodyReaders]) z.option (by simp))
  · exact Range.disjoint_of_id_ne (hd.inputOutput q.signature (by simp [bodyReaders]) z.option (by simp))
  · exact ⟨hf.live _ _ hm.scalarBytes.1,
      (hread _ (by simp [bodyReaders]) 256).trans hm.scalarBytes.2⟩
  · exact ⟨hf.live _ _ hm.one.1, (hread _ (by simp [bodyReaders]) 320).trans hm.one.2⟩

theorem BodyMemory.pointFrame {Point Scalar Result : Type}
    {q : TailPointers} {z : PointPointers} {scratch : Pointer} {state after : GlobalState}
    {layout : Layout Point Scalar Result} {h : Scalar} {a : Point} {r bytes : Bytes32}
    (hm : BodyMemory q z scratch state layout h a r bytes)
    (hf : PointCheckFrame state after z) (hd : BodyDisjoint q z scratch) :
    BodyMemory q z scratch after layout h a r bytes := by
  have hread (ptr : Pointer) (hp : ptr ∈ bodyReaders q z) (w : Nat) :
      after.mem.readAt ptr w = state.mem.readAt ptr w := by
    apply hf.read ptr w
    · exact Range.disjoint_of_id_ne (p := ptr) (q := z.slot29.add 6#64)
        (hd.inputOutput ptr hp z.slot29 (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (p := ptr) (q := z.slot30.add 6#64)
        (hd.inputOutput ptr hp z.slot30 (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd.inputOutput ptr hp z.point (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd.inputOutput ptr hp z.cofactor (by simp [pointDestinations]))
    · exact Range.disjoint_of_id_ne (hd.inputOutput ptr hp z.identity (by simp [pointDestinations]))
  refine ⟨?_, hf.live _ _ hm.signature, ?_, hf.live _ _ hm.scratch,
    hf.live _ _ hm.cache, hf.live _ _ hm.option, hf.live _ _ hm.slot29,
    hf.live _ _ hm.slot30, hf.live _ _ hm.point, hf.live _ _ hm.cofactor,
    hf.live _ _ hm.identity, ?_⟩
  · refine ⟨hf.wellFormed, hf.live _ _ hm.tail.output, hf.live _ _ hm.tail.compressed,
      ?_, ?_, hf.live _ _ hm.tail.scalar, ?_, hm.tail.outputChallenge, hm.tail.outputPoint,
      hm.tail.outputScalar, hm.tail.signatureOutput, hm.tail.compressedOutput,
      hm.tail.signatureCompressed, hm.tail.challengeScalar, hm.tail.pointScalar, hm.tail.signatureScalar⟩
    · exact ⟨hf.live _ _ hm.tail.challenge.1,
        (hread _ (by simp [bodyReaders]) 256).trans hm.tail.challenge.2⟩
    · exact ⟨hf.live _ _ hm.tail.point.1,
        (hread _ (by simp [bodyReaders]) 1280).trans hm.tail.point.2⟩
    · exact ⟨hf.live _ _ hm.tail.signature.1,
        (hread _ (by simp [bodyReaders]) 256).trans hm.tail.signature.2⟩
  · exact ⟨hf.live _ _ hm.scalarBytes.1,
      (hread _ (by simp [bodyReaders]) 256).trans hm.scalarBytes.2⟩
  · exact ⟨hf.live _ _ hm.one.1, (hread _ (by simp [bodyReaders]) 320).trans hm.one.2⟩

def bodySuffix (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (h : Scalar) (a : Point) (r bytes : Bytes32) : Bool :=
  match shared.decompress r with
  | none => false
  | some point => if shared.smallOrder point then false
      else scalarSuffix shared doubleBase compress h a r bytes

/-- Actual blocks 1–13 implement R decompression, both R outcomes, scalar
parsing, runtime backend dispatch and the final original-byte comparison. -/
theorem body_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : PrimitiveContracts p g layout shared doubleBase compress challenge)
    (hidentity : layout.identity = identityBytes)
    (q : TailPointers) (z : PointPointers) (scratch : Pointer) (hqcache : q.cache = g.address1)
    (E : Env program.Γ) (state : GlobalState)
    (h : Scalar) (a : Point) (r bytes : Bytes32)
    (hregs : BodyRegisters q z scratch E)
    (hmem : BodyMemory q z scratch state layout h a r bytes)
    (hd : BodyDisjoint q z scratch) :
    ∃ after, (program p g).runFrom E 1 state =
      .value (.cons (.value (code (bodySuffix shared doubleBase compress h a r bytes))) .nil, after) := by
  have hdsig : (Range.of z.option 1344).Disjoint (Range.of q.signature 256) :=
    (Range.disjoint_of_id_ne (hd.inputOutput q.signature (by simp [bodyReaders])
      z.option (by simp))).symm
  obtain ⟨decoded, hdcall, hdframe, htag⟩ := contracts.decompress z.option q.signature state r
    hmem.tail.wellFormed hmem.option hmem.tail.signature hdsig
  have hfits : Fits decoded.mem z.option 64 :=
    Fits.mono (by decide) (hdframe.live _ _ hmem.option).fits
  cases hdec : shared.decompress r with
  | none =>
    simp only [hdec] at htag
    refine ⟨decoded, ?_⟩
    rw [decompress_block p g E state decoded z.option q.signature false
      hregs.point.option hregs.tail.signature hdcall hfits htag]
    simpa [bodySuffix, hdec, code] using
      (decompression_rejection p g _ decoded (hregs.decompress false).tail.error)
  | some point =>
    simp only [hdec] at htag
    let decodedEnv := E[%39 := .value (1#64), %40 := .value (1#1)]
    have hrdec : BodyRegisters q z scratch decodedEnv := hregs.decompress true
    have hmdec := hmem.decompressFrame hdframe hd
    obtain ⟨checked, hpframe, hprun⟩ := point_check_of_contracts p g layout shared hidentity
      contracts.pointMulByPow2 contracts.pointConstantTimeEq z decodedEnv decoded point
      hrdec.point hmdec.tail.wellFormed hmdec.option hmdec.slot29 hmdec.slot30 hmdec.point
      hmdec.cofactor hmdec.identity htag.2 hmdec.one hd.point
    have hrpoint := hrdec.pointCheck (shared.smallOrder point)
    have hmpoint := hmdec.pointFrame hpframe hd
    by_cases hsmall : shared.smallOrder point = true
    · refine ⟨checked, ?_⟩
      rw [decompress_block p g E state decoded z.option q.signature true
        hregs.point.option hregs.tail.signature hdcall hfits htag.1]
      change (program p g).runFrom decodedEnv 2 decoded = _
      rw [hprun, hsmall]
      have hclean := cleanup_blocks p g (pointBlockEnv decodedEnv z true) checked 2#8
        (by simp [pointBlockEnv, mlir_env])
      simpa [bodySuffix, hdec, hsmall, code] using hclean
    · have hfalse : shared.smallOrder point = false := by
        cases hb : shared.smallOrder point with
        | false => rfl
        | true => exact False.elim (hsmall hb)
      obtain ⟨after, htail⟩ := scalar_tail_of_contracts p g layout shared doubleBase compress challenge
        contracts q hqcache _ checked h a r bytes scratch hrpoint.tail hmpoint.tail
        hrpoint.scratch hrpoint.sixtyThree hrpoint.thirtyThree hrpoint.one hrpoint.thirtyOne
        hmpoint.signature hmpoint.scalarBytes hmpoint.scratch
        (Range.disjoint_of_id_ne hd.scratchSignature) (Range.disjoint_of_id_ne hd.challengeScratch)
        (Range.disjoint_of_id_ne hd.pointScratch) (Range.disjoint_of_id_ne hd.signatureScalar)
        hmpoint.cache hd.cache
      refine ⟨after, ?_⟩
      rw [decompress_block p g E state decoded z.option q.signature true
        hregs.point.option hregs.tail.signature hdcall hfits htag.1]
      change (program p g).runFrom decodedEnv 2 decoded = _
      rw [hprun, hfalse]
      simpa [bodySuffix, hdec, hfalse] using htail

end Agave.Ed25519.Verifier.Execution.Dalek
