import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairSecond

namespace Agave.Ed25519.SHA512.Execution.Avx2

open LeanMLIR.RIR
open Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

@[simp] theorem group_params4 : program.blockParams 4 =
    .cons (%155) (.cons (%156) (.cons (%157) (.cons (%158) (.cons (%159) (.cons (%160) (.cons (%161) (.cons (%162) (.cons (%163) (.cons (%164) (.cons (%165) (.cons (%166) (.cons (%167) (.cons (%168) (.cons (%169) (.cons (%170) (.cons (%171) (.cons (%172) (.nil)))))))))))))))))) := rfl

@[simp] theorem group_params5 : program.blockParams 5 =
    .cons (%173) (.cons (%174) (.cons (%175) (.cons (%176) (.cons (%177) (.cons (%178) (.cons (%179) (.cons (%180) (.cons (%181) (.cons (%182) (.cons (%183) (.cons (%184) (.cons (%185) (.cons (%186) (.cons (%187) (.cons (%188) (.cons (%189) (.cons (%190) (.nil)))))))))))))))))) := rfl

@[simp] theorem group_params6 : program.blockParams 6 =
    .cons (%272) (.cons (%273) (.cons (%274) (.cons (%275) (.cons (%276) (.cons (%277) (.cons (%278) (.cons (%279) (.cons (%280) (.nil))))))))) := rfl

structure GroupReady (E : Env program.Γ) (g : Nat) : Prop where
  counter : E.read (%156) = .value (BitVec.ofNat 32 g)
  one : E.read (%0) = .value 1#32
  limit : E.read (%43) = .value 4#32

def groupBodyEnv (E : Env program.Γ) (g : Nat) : Env program.Γ :=
  E[%153 := .value (BitVec.ofNat 32 (g + 1)),
    %154 := .value (BitVec.ofBool (decide (g + 1 = 4)))]

/-- The exact simultaneous bb3-to-bb4 argument assignment. -/
def groupNextEnv (E : Env program.Γ) : Env program.Γ :=
  E[%155 := E.read (%270), %156 := E.read (%153),
    %157 := E.read (%180), %158 := E.read (%175),
    %159 := E.read (%182), %160 := E.read (%177),
    %161 := E.read (%216), %162 := E.read (%181),
    %163 := E.read (%178), %164 := E.read (%179),
    %165 := E.read (%186), %166 := E.read (%268),
    %167 := E.read (%184), %168 := E.read (%243),
    %169 := E.read (%267), %170 := E.read (%242),
    %171 := E.read (%187), %172 := E.read (%188)]

/-- The exact simultaneous bb3-to-bb6 argument assignment. -/
def groupTailEnv (E : Env program.Γ) : Env program.Γ :=
  E[%272 := E.read (%15), %273 := E.read (%186),
    %274 := E.read (%268), %275 := E.read (%184),
    %276 := E.read (%243), %277 := E.read (%267),
    %278 := E.read (%242), %279 := E.read (%187), %280 := E.read (%188)]

/-- The exact bb4-to-bb5 argument assignment, including the slot reset. -/
def groupPairEnv (E : Env program.Γ) : Env program.Γ :=
  E[%173 := E.read (%155), %174 := E.read (%2),
    %175 := E.read (%157), %176 := E.read (%158),
    %177 := E.read (%159), %178 := E.read (%160),
    %179 := E.read (%161), %180 := E.read (%162),
    %181 := E.read (%163), %182 := E.read (%164),
    %183 := E.read (%165), %184 := E.read (%166),
    %185 := E.read (%167), %186 := E.read (%168),
    %187 := E.read (%169), %188 := E.read (%170),
    %189 := E.read (%171), %190 := E.read (%172)]

theorem group_body (E : Env program.Γ) (mem : GlobalState) (g : Nat)
    (hg : g < 4) (h : GroupReady E g) :
    List.foldlM Instr.run E program.bb3.body mem =
      .value (groupBodyEnv E g, mem) := by
  have hadd : Operation.add {nsw := true, nuw := true}
      (.value (BitVec.ofNat 32 g)) (.value 1#32) =
      .value (BitVec.ofNat 32 (g + 1)) := by
    interval_cases g <;> decide
  have heq : (BitVec.ofNat 32 (g + 1) == 4#32) = decide (g + 1 = 4) := by
    interval_cases g <;> decide
  simp [program.bb3, List.foldlM_cons, List.foldlM_nil, Instr.run,
    groupBodyEnv, h.counter, h.one, h.limit, hadd, heq, Operation.icmp,
    BinOp.compute, EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem group_backedge (E : Env program.Γ) (mem : GlobalState) (g : Nat)
    (hg : g < 3) (h : GroupReady E g) :
    program.bb3.run program.blockParams E mem =
      .value ((groupNextEnv (groupBodyEnv E g), .inr 4), mem) := by
  have hne : g + 1 ≠ 4 := by omega
  simp only [BasicBlock.run, EffectM.bind_eq,
    group_body E mem g (by omega) h, PoisonOr.value_bind]
  simp [program.bb3, Exit.run, Jump.run, groupBodyEnv, groupNextEnv, hne,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem group_exit (E : Env program.Γ) (mem : GlobalState)
    (h : GroupReady E 3) :
    program.bb3.run program.blockParams E mem =
      .value ((groupTailEnv (groupBodyEnv E 3), .inr 6), mem) := by
  simp only [BasicBlock.run, EffectM.bind_eq,
    group_body E mem 3 (by decide) h, PoisonOr.value_bind]
  simp [program.bb3, Exit.run, Jump.run, groupBodyEnv, groupTailEnv,
    Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.pure_eq, mlir_env, mlir_effect]

theorem group_pair_entry (E : Env program.Γ) (mem : GlobalState) :
    program.bb4.run program.blockParams E mem =
      .value ((groupPairEnv E, .inr 5), mem) := by
  simp [BasicBlock.run, program.bb4, List.foldlM_nil, Exit.run, Jump.run,
    groupPairEnv, Regs.read_cons, Regs.read_nil, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

theorem group_next_ready (E : Env program.Γ) (g : Nat) (h : GroupReady E g) :
    GroupReady (groupNextEnv (groupBodyEnv E g)) (g + 1) := by
  constructor <;> simp [groupNextEnv, groupBodyEnv, h.one, h.limit, mlir_env]

structure GroupTailConstants (E : Env program.Γ) (scratch : Pointer) : Prop where
  scratch : E.read (%81) = .value scratch
  one : E.read (%1) = .value 1#64
  limit : E.read (%17) = .value 80#64
  rot14 : E.read (%36) = .value 50#64
  rot18 : E.read (%37) = .value 46#64
  rot41 : E.read (%38) = .value 23#64
  rot28 : E.read (%39) = .value 36#64
  rot34 : E.read (%40) = .value 30#64
  rot39 : E.read (%41) = .value 25#64
  mask : E.read (%44) = .value 15#64

/-- All tail constants are inherited; the state is precisely the second round's result. -/
theorem group_tail_ready (E : Env program.Γ) (scratch : Pointer) (s : Spec.State)
    (h : PairSecondFinalReady E s)
    (hc : GroupTailConstants E scratch)
    (h64 : E.read (%15) = .value 64#64) :
    TailReady (groupTailEnv (groupBodyEnv E 3)) scratch 64 s := by
  constructor <;> simp [groupTailEnv, groupBodyEnv, mlir_env,
    h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h64,
    hc.scratch, hc.one, hc.limit, hc.rot14, hc.rot18, hc.rot41,
    hc.rot28, hc.rot34, hc.rot39, hc.mask]

theorem group_backedge_runFrom (glob : Globals) (E : Env program.Γ)
    (mem : GlobalState) (g : Nat) (hg : g < 3) (h : GroupReady E g) :
    (program glob).runFrom E 3 mem =
      (program glob).runFrom (groupNextEnv (groupBodyEnv E g)) 4 mem := by
  rw [Func.runFrom_eq]
  change (program.bb3.run program.blockParams E mem >>= fun x =>
    (program glob).continue x.1.1 x.1.2 x.2) = _
  rw [group_backedge E mem g hg h]
  rfl

theorem group_exit_runFrom (glob : Globals) (E : Env program.Γ)
    (mem : GlobalState) (h : GroupReady E 3) :
    (program glob).runFrom E 3 mem =
      (program glob).runFrom (groupTailEnv (groupBodyEnv E 3)) 6 mem := by
  rw [Func.runFrom_eq]
  change (program.bb3.run program.blockParams E mem >>= fun x =>
    (program glob).continue x.1.1 x.1.2 x.2) = _
  rw [group_exit E mem h]
  rfl

theorem group_pair_entry_runFrom (glob : Globals) (E : Env program.Γ)
    (mem : GlobalState) :
    (program glob).runFrom E 4 mem =
      (program glob).runFrom (groupPairEnv E) 5 mem := by
  rw [Func.runFrom_eq]
  change (program.bb4.run program.blockParams E mem >>= fun x =>
    (program glob).continue x.1.1 x.1.2 x.2) = _
  rw [group_pair_entry E mem]
  rfl

end Agave.Ed25519.SHA512.Execution.Avx2
