/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofSetup
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofTailRun
import SSA.Projects.Agave.LatticeHash.MLIR.PortableXofXofTailRun
import SSA.Projects.Agave.LatticeHash.MLIR.PortableCompressionProof
namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression
namespace PortableXof
open LeanMLIR SLLVM Firedancer Blake3Compression
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem pre_round_denote (V : preInput.middle.Valuation) :
    preInput.tail.denote V = preRound.pre.denote V >>= preRound.tail.denote := by
  calc
    preInput.tail.denote V = (preRound.pre.append preRound.tail).denote V :=
      congrArg (fun b => b.denote V) pre_round_parts.symm
    _ = _ := BlockPrefix.denote_append preRound.pre preRound.tail V

theorem xof_round_denote (V : xofInput.middle.Valuation) :
    xofInput.tail.denote V = xofRound.pre.denote V >>= xofRound.tail.denote := by
  calc
    xofInput.tail.denote V = (xofRound.pre.append xofRound.tail).denote V :=
      congrArg (fun b => b.denote V) xof_round_parts.symm
    _ = _ := BlockPrefix.denote_append xofRound.pre xofRound.tail V

/-- Recover the actual round SSA results from the already-proved pre-compression
execution. Pure rounds preserve the input context; actual successful stores
establish definedness, and byte-backed readback identifies every result word. -/
theorem round_values (s : GlobalState) (out cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    ∃ W : preRound.middle.Valuation,
      preRound.pre.denote (inputValuation out cvp msg cv m counter len flags) = pure W ∧
      TailEnv W out ∧
      (∀ i, W (resultVar i) = .value
        (scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32) i)) ∧
      (∀ i, W (cvVar i) = .value (cv i)) := by
  obtain ⟨W, hpure, hctx⟩ := rounds_pure.denote_exists
    (inputValuation out cvp msg cv m counter len flags)
  have env := tail_env_of_context out cvp msg cv m counter len flags W hctx
  have hi := input_prefix_run s out cvp msg cv m counter len flags hcvp hmsg rcv rmsg
  have hp := portable_compression_run s out cvp msg cv m counter len flags hout hcvp hmsg rcv rmsg
  change StateT.run (Cfg.denote ⟨agave_portable_compress_pre.cfgEntry, .nil⟩
    (Ctxt.Valuation.ofHVector [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s = _ at hp
  rw [denote_no_blocks, ← pre_input_parts, BlockPrefix.denote_append, bind_assoc] at hp
  rw [EffectM.run_bind_of_value hi, pre_round_denote, bind_assoc, hpure, pure_bind] at hp
  have hdef (i : Fin 16) : ∃ x : Word, W (resultVar i) = .value x := by
    have hn := (stored_results i).defined W s (fun _ => pure ([]ₕ : HVector toType ([] : List SLLVM.Ty))) _ hp
    cases hwi : W (resultVar i) using PoisonOr.casesOn' with
    | poison => exact False.elim (hn hwi)
    | value x => exact ⟨x, rfl⟩
  choose x hx using hdef
  have ht := pre_tail_run W out x env hx s hout
  have hstates := PoisonOr.value_inj.mp (ht.symm.trans hp)
  have hmem := congrArg (fun z : HVector toType ([] : List SLLVM.Ty) × GlobalState => z.2.mem) hstates
  dsimp only at hmem
  have hwords (i : Fin 16) : x i = scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32) i := by
    have hread := portableCompressionMemory_read_word s.mem out x hout hwrap i
    rw [hmem] at hread
    have href := portableCompressionMemory_read_word s.mem out
      (scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32)) hout hwrap i
    exact Option.some.inj (hread.symm.trans href)
  refine ⟨W, hpure, env, ?_, cv_of_context out cvp msg cv m counter len flags W hctx⟩
  intro i
  rw [hx i, hwords i]

end PortableXof
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- Execute the exact upstream portable compress_xof body, including all sixteen
feed-forward XORs and compiler-emitted stores of the serialized result. -/
theorem portable_xof_run (s : GlobalState) (out cvp msg : Pointer)
    (cv : CV Word) (m : State Word) (counter : BitVec 64) (len flags : BitVec 8)
    (hout : Fits s.mem out 512) (hcvp : Fits s.mem cvp 256) (hmsg : Fits s.mem msg 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64)
    (rcv : ∀ i : Fin 8, readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (cv i))
    (rmsg : ∀ i : Fin 16, readWord? (msg.withOffset (BitVec.ofNat 64 (4*i.val))) 32 s.mem = some (m i)) :
    StateT.run (agave_portable_compress_xof.denote (Ctxt.Valuation.ofHVector
      [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s =
    .value ([]ₕ, {s with mem := portableCompressionMemory s.mem out (scalarCompress cv m counter (len.zeroExtend 32) (flags.zeroExtend 32))}) := by
  obtain ⟨W, hpure, env, hx, hcv⟩ := PortableXof.round_values s out cvp msg cv m counter len flags
    hout hcvp hmsg hwrap rcv rmsg
  have hi := PortableXof.input_prefix_run s out cvp msg cv m counter len flags hcvp hmsg rcv rmsg
  change StateT.run (Cfg.denote ⟨agave_portable_compress_xof.cfgEntry, .nil⟩
    (Ctxt.Valuation.ofHVector [.value flags, .value counter, .value len, .value msg, .value cvp, .value out]ₕ)) s = _
  rw [PortableXof.denote_no_blocks, ← PortableXof.xof_input_parts,
    BlockPrefix.denote_append, bind_assoc]
  rw [← PortableXof.inputs_same.denote_eq, EffectM.run_bind_of_value hi,
    PortableXof.xof_round_denote, bind_assoc, ← PortableXof.rounds_same, hpure, pure_bind]
  exact PortableXof.xof_tail_run W out
    (scalarCompressPre cv m counter (len.zeroExtend 32) (flags.zeroExtend 32)) cv env hx hcv s hout

end AgaveLatticeHash.MLIR
