import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialCacheAddresses
import SSA.Projects.Agave.Ed25519.Proof.Tables.SerialConstructorCallFrame

namespace Agave.Ed25519.Tables.SerialConstructorEntryStart
open LeanMLIR.RIR
open NAF.Memory (Buffer)
open DoubleBase.RIR (PrefixEq)
open DoubleBase.SerialContracts (readPoint readCached)
open SerialConstructorStack
open SerialConstructorCallFrame (slots)
open SerialConstructorState (Frame Ready)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem stack_ready (s : GlobalState) (g : SerialConstructor.Globals)
    (hwf : s.WF) (hg : SerialConstructorContext.GlobalsReady g s) :
    Ready g (slots s) (stackPtr s 7) (stack s 8) := by
  refine ⟨stack_wf hwf 8, ?_, stack_buffer hwf 7 8 (by decide) (by decide),
    stack_globals hg hwf 8, ?_, ?_⟩
  · intro i
    have hi : stackSize i.val = SerialConstructorState.bytes i := by
      fin_cases i <;> rfl
    rw [← hi]
    exact stack_buffer hwf i.val 8 (by have := i.isLt; omega)
      (by fin_cases i <;> decide)
  · intro i j hij
    exact stack_separate s i.val j.val (fun he => hij (Fin.ext he))
  · intro i
    exact stack_separate s i.val 7 (by have := i.isLt; omega)

theorem stack_readPoint (s : GlobalState) (input : Pointer) (hwf : s.WF)
    (hi : Buffer s.mem input 160) : readPoint (stack s 8) input = readPoint s input := by
  have hid := hwf.lt hi.fits.mem
  apply PointArithmetic.Extended.ext
  all_goals
    dsimp only [readPoint, DoubleBase.SerialContracts.readField, SerialFieldMul.unsigned, SerialFieldMul.readLimbs]
    funext i
    change ((stack s 8).mem.readAt _ 64).toNat = (s.mem.readAt _ 64).toNat
    rw [SerialConstructorCallFrame.stack_read_old
      (by simpa only [Pointer.add_id] using hid)]

def cacheState (s : GlobalState) (g : SerialConstructor.Globals) (input : Pointer) : GlobalState :=
  SerialCacheExecution.cacheState (stack s 8) (stackPtr s 6) input g.address0

/-- Exact original entry prefix through the first physical cached point. -/
theorem entry_cache (p : SerialConstructor.Primitives) (g : SerialConstructor.Globals)
    (E : ⟪SerialConstructor.kernel.Γ⟫) (s : GlobalState) (input : Pointer)
    (hwf : s.WF) (hg : SerialConstructorContext.GlobalsReady g s)
    (hi : Buffer s.mem input 160) (hA : SerialPoint.PointTight (readPoint s input))
    (harg : E.args 1 = .value input) :
    ∃ F,
      List.foldlM Instr.run E ((SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).body.take 117) s =
        .value (F, cacheState s g input) ∧
      PrefixEq (initial E g s) F 37 ∧
      Frame (slots s) (stackPtr s 7) (stack s 8) (cacheState s g input) ∧
      Ready g (slots s) (stackPtr s 7) (cacheState s g input) ∧
      readCached (cacheState s g input) (stackPtr s 6) =
        SerialConstructorArithmetic.cache (readPoint s input) ∧
      readPoint (cacheState s g input) input = readPoint s input ∧
      F.read (%37) = .value (input.add 40) ∧ F.read (%87) = .value (input.add 80) := by
  let I := initial E g s
  have hs := stack_ready s g hwf hg
  have hib := stack_existing hwf hi 8
  have hargI : I.args 1 = .value input := by
    simpa only [I, initial, constants, Env.write_args] using harg
  have hc : constants I g = I := constants_of_prefix E I g (initial_prefix E g s)
  have ho : I.read (%35) = .value (stackPtr s 6) := by simp [I,initial,mlir_env]
  obtain ⟨F,hr,hframe⟩ := SerialCacheExecution.firstBody_run p g I (stack s 8)
    (stackPtr s 6) input hs.wf (hs.point 6 (by decide)) hib hs.globalReady.buffer
    (stack_separate_caller hwf hi 6) (hs.globalSeparate 6) hargI ho hc
  have hf := SerialCacheExecution.cacheState_writesOnly (stack s 8) (stackPtr s 6)
    input g.address0 hs.wf (hs.point 6 (by decide))
  have hfs : Frame (slots s) (stackPtr s 7) (stack s 8) (cacheState s g input) := Frame.slot 6 hf
  have hstackA := stack_readPoint s input hwf hi
  have hbound : SerialPoint.PointTight (readPoint (stack s 8) input) := hstackA.symm ▸ hA
  refine ⟨F,?_,hframe,hfs,hs.preserve hfs,?_,?_,?_,?_⟩
  · have hb : (SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).body.take 117 =
        (SerialConstructor.kernel.bb0 (SerialCacheExecution.primitives p) g).body.take 37 ++
        SerialCacheExecution.firstBody p g := rfl
    rw [hb,List.foldlM_append,EffectM.bind_eq,initial_run,PoisonOr.value_bind]
    exact hr
  · rw [cacheState,SerialCacheExecution.cacheState_readCached g (stack s 8) (stackPtr s 6) input
      (hs.point 6 (by decide)) hib hs.globalReady hbound,hstackA]
  · exact (SerialConstructorState.point_read_ne hf (stack_separate_caller hwf hi 6)).trans hstackA
  · exact SerialCacheExecution.firstBody_source40 p g I F (stack s 8) _ input hib hargI
      (by simp [I,initial,constants,mlir_env]) hr
  · exact SerialCacheExecution.firstBody_source80 p g I F (stack s 8) _ input hib hargI
      (by simp [I,initial,constants,mlir_env]) hr

end Agave.Ed25519.Tables.SerialConstructorEntryStart
