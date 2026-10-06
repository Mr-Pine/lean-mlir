/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CallerMemory
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG8
import SSA.Projects.Agave.LatticeHash.MLIR.BatchCFG16
import SSA.Projects.Agave.LatticeHash.OutputLog

/-! Operational lifecycle with actual compiled full-batch leaves. Serial leaves
are explicitly separate: neither partial batches nor long-message execution
are supplied by the full-width compiler artifacts. These are execution relation
definitions, not correctness assumptions or claims of whole-Rust extraction. -/
namespace AgaveLatticeHash.MLIR.Execution
open LeanMLIR SLLVM Firedancer
open AgaveStaging AgavePhysicalStaging

inductive Architecture where
  | avx2
  | avx512

def Architecture.width : Architecture → Nat
  | .avx2 => 8
  | .avx512 => 16

def Architecture.perm : Architecture → AgaveLattice.Matrix
  | .avx2 => AgaveLattice.transpose8 AgaveLattice.labels
  | .avx512 => AgaveLattice.transpose16 AgaveLattice.labels

theorem Architecture.positive (arch : Architecture) : 0 < arch.width := by cases arch <;> decide

theorem Architecture.vector (arch : Architecture) : 1 < arch.width := by cases arch <;> decide

theorem Architecture.bounded (arch : Architecture) : arch.width ≤ 16 := by cases arch <;> decide

theorem Architecture.transpose (arch : Architecture) : AgaveLattice.IsTranspose arch.width arch.perm := by
  cases arch
  · exact AgaveLattice.avx2_isTranspose
  · exact AgaveLattice.avx512_isTranspose

/-- Actual CFG normal return; the output is observed independently below. -/
def BatchReturns (arch : Architecture) (src len out : Pointer) (before after : GlobalState) : Prop :=
  match arch with
  | .avx2 => StateT.run (agave_batch_8.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) before = .value ([]ₕ, after)
  | .avx512 => StateT.run (agave_batch_16.denote
      (Ctxt.Valuation.ofHVector [.value out, .value len, .value src]ₕ)) before = .value ([]ₕ, after)

/-- A compiled batch invocation on the actual retained bytes and current
accumulator. Its witnesses are a concrete caller image, normal CFG execution,
and successful reads of all 1024 result cells. No hash specification occurs. -/
def FullWidthRun (arch : Architecture) (p : Store) (a result : Value) : Prop :=
  ∃ base after : GlobalState, base.WF ∧
    BatchReturns arch (CallerMemory.ptr base 0) (CallerMemory.ptr base 1)
      (CallerMemory.ptr base 2) (CallerMemory.image base arch.width p a) after ∧
    ∀ i : Fin 1024,
      readWord? ((CallerMemory.ptr base 2).withOffset (BitVec.ofNat 64 (2*i.val))) 16 after.mem =
        some (result i)

/-- The external serial caller's operational relation. A refinement theorem
must separately connect these leaves to BLAKE3, including streaming long input. -/
abbrev SerialExecution := List Message → Value → Value → Prop

inductive Flush (serial : SerialExecution) (arch : Architecture) (p : Store) (s : Impl) : Impl → Prop
  | compiled (full : p.count = arch.width) (result : Value)
      (call : FullWidthRun arch p s.acc result) :
      Flush serial arch p s {s with acc := result, pending := []}
  | serial (notfull : p.count ≠ arch.width) (result : Value)
      (call : serial (readBatch p) s.acc result) :
      Flush serial arch p s {s with acc := result, pending := [], serial := (readBatch p).getLast?.getD s.serial}

inductive Commit (serial : SerialExecution) (arch : Architecture) (p : Store) (s : Impl) : Impl → Prop
  | spilled (spill : s.spilled = true) (result : Value)
      (call : serial [s.serial] s.acc result) :
      Commit serial arch p s {s with acc := result, spilled := false}
  | staged (spill : s.spilled = false) (notfull : (finishStore p).count ≠ arch.width) :
      Commit serial arch p s (finishLane s)
  | full (spill : s.spilled = false) (full : (finishStore p).count = arch.width) (t : Impl)
      (flush : Flush serial arch (finishStore p) (finishLane s) t) :
      Commit serial arch p s t

inductive Take (serial : SerialExecution) (arch : Architecture) (p : Store) (s : Impl) : Value → Impl → Prop
  | empty (empty : p.count = 0) : Take serial arch p s s.acc {s with acc := zero}
  | flush (nonempty : p.count ≠ 0) (t : Impl) (call : Flush serial arch p s t) :
      Take serial arch p s t.acc {t with acc := zero}

/-- Public source-shaped transitions whose full-width calls are actual MLIR
executions. The accumulator in the successor is the value read from memory,
not a value computed by the specification. -/
inductive Run (serial : SerialExecution) (arch : Architecture) :
    List AgaveOutputLog.Event → Store → Impl → AgaveMixed.Spec → List Value → Prop
  | initial : Run serial arch [] initialStore init AgaveMixed.specInit []
  | start {events p s r out} (run : Run serial arch events p s r out) (idle : r.active = none) :
      Run serial arch (events ++ [.start]) p s {r with active := some []} out
  | part {events p s r out} (run : Run serial arch events p s r out)
      (m part : Message) (active : r.active = some m) :
      Run serial arch (events ++ [.part part]) (appendStore s.spilled p part)
        (physicalAppend p s part) {r with active := some (m ++ part)} out
  | finish {events p s r out} (run : Run serial arch events p s r out)
      (m : Message) (active : r.active = some m) (t : Impl) (call : Commit serial arch p s t) :
      Run serial arch (events ++ [.finish]) (commitStore arch.width s.spilled p) t
        ⟨r.committed ++ [m], none, r.offset⟩ out
  | drop {events p s r out} (run : Run serial arch events p s r out)
      (m : Message) (active : r.active = some m) :
      Run serial arch (events ++ [.drop]) (discardStore p) (discard s) {r with active := none} out
  | whole {events p s r out} (run : Run serial arch events p s r out)
      (m : Message) (idle : r.active = none) (t : Impl)
      (call : Commit serial arch (appendStore s.spilled p m) (physicalAppend p s m) t) :
      Run serial arch (events ++ [.whole m])
        (commitStore arch.width (physicalAppend p s m).spilled (appendStore s.spilled p m)) t
        ⟨r.committed ++ [m], none, r.offset⟩ out
  | mix_in {events p s r out} (run : Run serial arch events p s r out)
      (x : Value) (idle : r.active = none) :
      Run serial arch (events ++ [.mix_in x]) p (AgaveMixed.mixIn s x)
        {r with offset := plus r.offset x} out
  | mix_out {events p s r out} (run : Run serial arch events p s r out)
      (x : Value) (idle : r.active = none) :
      Run serial arch (events ++ [.mix_out x]) p (AgaveMixed.mixOut s x)
        {r with offset := plus r.offset (AgaveMixed.neg x)} out
  | drain {events p s r out} (run : Run serial arch events p s r out)
      (idle : r.active = none) (value : Value) (t : Impl) (call : Take serial arch p s value t) :
      Run serial arch (events ++ [.drain]) (takeStore p) t AgaveMixed.specInit (out ++ [value])

end AgaveLatticeHash.MLIR.Execution
