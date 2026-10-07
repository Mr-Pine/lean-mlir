import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Stores
import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Sign

/-! Exact store-suffix execution plus readback of all 32 bytes. These theorems
start after the inline canonicalizers. They do not assert that the compressor's
entry reaches that environment; that remaining prefix obligation is explicit. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000

/-- Execute the original store suffix and recover the shared compression bytes. -/
theorem store_compress_run (p : Primitives) (E : Env program.Γ) (out : Pointer)
    (x y : Field.Serial) (P : Bridge.CurvePoint) (s : GlobalState)
    (hr : SmallRange s.mem out 32) (hout : E.read (%arg0) = .value out)
    (hx : (Field.serialValue x : K) = P.x) (hy : (Field.serialValue y : K) = P.y) :
    ∃ finalState,
      (storeProgram p).runFrom (storeEnv E (encodedBytes x y)) 0 s =
        .value (.nil, finalState) ∧
      finalState.mem.readAt out 256 = Bridge.compress P := by
  refine ⟨{s with mem := storeBytes s.mem out (encodedBytes x y)},
    store_run p E out (encodedBytes x y) s hr hout, ?_⟩
  change (storeBytes s.mem out (encodedBytes x y)).readAt out 256 = _
  have hb : encodedBytes x y = fun i => (Bridge.compress P).extractLsb' (8 * i.val) 8 := by
    funext i
    exact encodedBytes_eq_compress x y P hx hy i
  rw [hb]
  exact storeBytes_read s.mem out (Bridge.compress P) hr

/-- Once lower pow22501, pow2k and multiplication calls establish their field
values, the output has the canonical projective-point encoding. The only
arithmetic premises are those individual products and the projective relation. -/
theorem store_projective_compress_run (p : Primitives) (E : Env program.Γ)
    (out : Pointer) (x y : Field.Serial) (X Y Z : K) (P : Bridge.CurvePoint)
    (s : GlobalState) (hr : SmallRange s.mem out 32)
    (hout : E.read (%arg0) = .value out)
    (hz : Z ≠ 0) (hx : X = P.x * Z) (hy : Y = P.y * Z)
    (hxm : (Field.serialValue x : K) = X * invertChain Z)
    (hym : (Field.serialValue y : K) = Y * invertChain Z) :
    ∃ finalState,
      (storeProgram p).runFrom (storeEnv E (encodedBytes x y)) 0 s =
        .value (.nil, finalState) ∧
      finalState.mem.readAt out 256 = Bridge.compress P := by
  obtain ⟨hxa, hya⟩ := affine_products X Y Z P hz hx hy
  exact store_compress_run p E out x y P s hr hout (hxm.trans hxa) (hym.trans hya)

end Agave.Ed25519.Encoding.Compress.Execution
