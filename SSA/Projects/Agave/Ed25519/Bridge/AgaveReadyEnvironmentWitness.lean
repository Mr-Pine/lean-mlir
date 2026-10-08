import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputPackage
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialBackendReady
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2ContractDefs
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.InitializerLink

/-! An explicit loader witness for the simultaneous global-memory premises of
`AgaveReady.call_strict`. Every installed immutable object uses its imported
literal initializer. K64 readiness is obtained through `extracted_k64_eq`.
No semantic table equality or readiness hypothesis is assumed. -/
namespace Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness
open LeanMLIR.RIR
open Verifier Verifier.Execution
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 1024

def ptr (n : Nat) : Pointer := ⟨⟨n⟩, 0⟩
def empty : GlobalState := ⟨⟨0⟩, ⟨∅⟩⟩
/-- A separate live mutable backend-cache byte. Only its allocation is required
by `InitializedGlobals`; choosing the cold sentinel is a concrete witness. -/
def dalekCacheObject : ByteGlobal :=
  ⟨"_RNvNtNvNtCsjK63O35OHGN_14solana_ed255197backend20get_selected_backend10cpuid_avx27STORAGE",
    1, 255, 1, by decide⟩

def loaded1 : GlobalState := identityOne.install empty
def loaded2 : GlobalState := dalekCacheObject.install loaded1
def loaded3 : GlobalState := sha512InitialState.install loaded2
def loaded4 : GlobalState := SHA512.InitializerData.k64Global.install loaded3
def loaded5 : GlobalState := SHA512.InitializerData.coldCacheGlobal.install loaded4
def loaded6 : GlobalState := ScalarWide.montgomeryR.install loaded5
def loaded7 : GlobalState := ScalarWide.montgomeryRR.install loaded6
def loaded8 : GlobalState := Encoding.Decompress.Execution.curveD.install loaded7
def loaded9 : GlobalState := Encoding.Decompress.Execution.sqrtM1.install loaded8
def loaded10 : GlobalState := Tables.serialBaseGlobal.install loaded9
def loaded11 : GlobalState := Tables.serialD2Global.install loaded10
def loaded12 : GlobalState := Tables.avx2BaseGlobal.install loaded11

abbrev initial := loaded12

def dg : Dalek.Globals := ⟨ptr 0, ptr 1⟩
def cg : Challenge.Globals := ⟨ptr 2⟩
def sg : ScalarWide.Globals := ⟨ptr 5, ptr 6⟩
def scg : SHA512Finalization.CompressionGlobals := ⟨⟨3⟩, ⟨4⟩⟩
def ddg : Encoding.Decompress.Execution.Decode.Globals := ⟨ptr 7⟩
def dsg : Encoding.Decompress.Execution.SqrtRatio.Globals := ⟨ptr 8⟩
/-- Panic-location pointers are unused by readiness. -/
def serial : DoubleBase.SerialCFG.Globals := ⟨ptr 0, ptr 13, ptr 14, ptr 9⟩
def d2 : Tables.SerialConstructor.Globals := ⟨ptr 10⟩
def avx : DoubleBase.Avx2CFG.Globals := ⟨ptr 13, ptr 14, ptr 11⟩

theorem initial_wf : initial.WF := by
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  apply ByteGlobal.wf_install
  intro k hk
  simp [empty] at hk

theorem present0 : identityOne.Present ⟨0⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present1 : dalekCacheObject.Present ⟨1⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present2 : sha512InitialState.Present ⟨2⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present3 : SHA512.InitializerData.k64Global.Present ⟨3⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present4 : SHA512.InitializerData.coldCacheGlobal.Present ⟨4⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present5 : ScalarWide.montgomeryR.Present ⟨5⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present6 : ScalarWide.montgomeryRR.Present ⟨6⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present7 : Encoding.Decompress.Execution.curveD.Present ⟨7⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present8 : Encoding.Decompress.Execution.sqrtM1.Present ⟨8⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present9 : Tables.serialBaseGlobal.Present ⟨9⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present10 : Tables.serialD2Global.Present ⟨10⟩ initial.mem := by
  simp [initial, loaded12, loaded11, loaded10, loaded9, loaded8, loaded7, loaded6, loaded5, loaded4, loaded3, loaded2, loaded1, empty, ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq, Std.ExtHashMap.getElem_insert]

theorem present11 : Tables.avx2BaseGlobal.Present ⟨11⟩ initial.mem :=
  ByteGlobal.present_install _ _

theorem readBytes_of_present (g : ByteGlobal) (id : BlockId)
    (h : g.Present id state.mem) (hlen : g.length < 2^63) :
    Dalek.ReadBytes state (g.address id) g.length g.bytes := by
  exact ⟨⟨⟨g.length, g.bytes⟩, h, hlen, by simp [ByteGlobal.address]⟩, h.readAt⟩

theorem initialized : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial (ptr 12) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  · exact readBytes_of_present identityOne ⟨0⟩ present0 (by decide)
  · exact (readBytes_of_present dalekCacheObject ⟨1⟩ present1 (by decide)).1
  · exact readBytes_of_present sha512InitialState ⟨2⟩ present2 (by decide)
  · exact SHA512Finalization.compressionReady_of_source_initializers scg initial present3 present4 (by decide)
  · exact ⟨rfl, rfl, present5, present6, by decide⟩
  · exact ⟨readBytes_of_present Encoding.Decompress.Execution.curveD ⟨7⟩ present7 (by decide),
      readBytes_of_present Encoding.Decompress.Execution.sqrtM1 ⟨8⟩ present8 (by decide)⟩

theorem serial_ready : Dalek.SerialBackendReadiness.Ready serial d2 initial :=
  ⟨⟨rfl, present0, rfl, present9⟩, ⟨rfl, present10⟩⟩

theorem avx_ready : DoubleBase.ExecutionAvx2.GlobalsReady avx initial := ⟨rfl, present11⟩

theorem serial_separate : Dalek.SerialBackendReadiness.Separate serial d2 dg.address1 := by
  unfold Dalek.SerialBackendReadiness.Separate
  decide

theorem avx_separate : avx.address2.id ≠ dg.address1.id := by decide

/-- A single explicitly constructed well-formed state satisfies every global
readiness and separation premise simultaneously. The message block is reserved
at id 12; no assertion about caller buffers is made here. -/
theorem globals_jointly_satisfiable :
    ∃ (state : GlobalState) (dg : Dalek.Globals) (cg : Challenge.Globals)
      (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
      (ddg : Encoding.Decompress.Execution.Decode.Globals)
      (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
      (serial : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
      (avx : DoubleBase.Avx2CFG.Globals) (message : Pointer),
      state.WF ∧ ColdInput.InitializedGlobals dg cg sg scg ddg dsg state message ∧
      Dalek.SerialBackendReadiness.Ready serial d2 state ∧
      DoubleBase.ExecutionAvx2.GlobalsReady avx state ∧
      Dalek.SerialBackendReadiness.Separate serial d2 dg.address1 ∧
      avx.address2.id ≠ dg.address1.id :=
  ⟨initial, dg, cg, sg, scg, ddg, dsg, serial, d2, avx, ptr 12,
    initial_wf, initialized, serial_ready, avx_ready, serial_separate, avx_separate⟩

end Agave.Ed25519.Bridge.AgaveReady.EnvironmentWitness
