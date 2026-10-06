import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceSetup
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceTransport
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceMemory
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression
namespace PortableInPlace
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem round_denote (V : input.middle.Valuation) :
    input.tail.denote V = rounds.pre.denote V >>= rounds.tail.denote := by
  rw [← round_parts, BlockPrefix.denote_append]

/-- Recover the shared pure round results using the message region as a
hypothetical output witness. This auxiliary execution does not occur in the
in-place CFG and contributes no writes to its observable state. -/
theorem round_values (s : GlobalState) (cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : msg.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    ∃ Z : rounds.middle.Valuation,
      rounds.pre.denote (inputValuation cvp msg cv m counter len flags) = pure Z ∧
      TailEnv Z cvp ∧
      ∀ i, Z (resultVar i) = .value
        (scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32) i) := by
  obtain ⟨W, hpure, _, hx, _⟩ := PortableXof.round_values s msg cvp msg cv m counter len flags
    hmsg hcvp hmsg hwrap rcv rmsg
  obtain ⟨Z, hZ, hctx⟩ := rounds_pure.denote_exists
    (inputValuation cvp msg cv m counter len flags)
  have ht := round_certificate.denote_bind (inputValuation cvp msg cv m counter len flags)
    (fun U => pure U)
  rw [hZ, input_comap, hpure] at ht
  simp only [pure_bind] at ht
  have hv := congrArg (fun e => StateT.run e s) ht
  simp only [EffectM.run_pure] at hv
  have he : Z.comap finalMap = W := congrArg Prod.fst (PoisonOr.value_inj.mp hv)
  refine ⟨Z, hZ, tail_env_of_context cvp msg cv m counter len flags Z hctx, ?_⟩
  intro i
  have hw := congrArg (fun U : PortableXof.preRound.middle.Valuation => U (PortableXof.resultVar i)) he
  change Z (finalMap (PortableXof.resultVar i)) = W (PortableXof.resultVar i) at hw
  rw [result_mapped] at hw
  exact hw.trans (hx i)

end PortableInPlace
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

/-- Actual upstream compress_in_place changes exactly the compiler's eight CV
stores. Its input message region must not wrap; output readback additionally
requires the CV region not to wrap. -/
theorem portable_in_place_run (s : GlobalState) (cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : msg.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    StateT.run (agave_portable_compress_in_place.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp]ₕ)) s =
    .value ([]ₕ, {s with mem := PortableInPlace.cvMemory s.mem cvp (scalarCompress cv m counter (len.zeroExtend 32) (flags.zeroExtend 32))}) := by
  obtain ⟨W, hpure, env, hx⟩ := PortableInPlace.round_values s cvp msg cv m counter len flags
    hcvp hmsg hwrap rcv rmsg
  have hi := PortableInPlace.input_prefix_run s cvp msg cv m counter len flags hcvp hmsg rcv rmsg
  change StateT.run (Cfg.denote ⟨agave_portable_compress_in_place.cfgEntry, .nil⟩
    (Ctxt.Valuation.ofHVector [.value flags, .value counter, .value len, .value msg, .value cvp]ₕ)) s = _
  rw [PortableXof.denote_no_blocks, ← PortableInPlace.input_parts,
    BlockPrefix.denote_append, bind_assoc]
  rw [EffectM.run_bind_of_value hi, PortableInPlace.round_denote, bind_assoc, hpure, pure_bind]
  exact PortableInPlace.tail_run W cvp
    (scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32)) cv env hx s hcvp

end AgaveLatticeHash.MLIR
