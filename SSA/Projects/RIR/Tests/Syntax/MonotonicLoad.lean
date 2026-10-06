module

public import SSA.Projects.RIR.Syntax.Elab
import all SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func

/-! The exact monotonic byte-load form emitted for the CPUID cache. The atomic
marker is retained, while the value and UB behavior use RIR's sequential memory
model. Source refinement requires exclusive access to this byte during the run. -/

namespace LeanMLIR.RIR.Tests.Syntax.MonotonicLoad

@[expose] public section

mlir_def atomicByte := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{alignment = 1 : i64, ordering = 2 : i64}> : (!llvm.ptr) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

mlir_def ordinaryByte := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{alignment = 1 : i64, ordering = 0 : i64}> : (!llvm.ptr) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

example : atomicByte.entry.body = [.loadMonotonic ⟨0, rfl⟩ (.arg 0 rfl)] := rfl

/-- The actual parsed instructions have equal effects for arbitrary register
environments and memory, including poison pointers and invalid accesses. -/
theorem instruction_run_eq (env : ⟪atomicByte.Γ⟫) :
    Instr.run env (atomicByte.entry.body[0]'(by decide)) =
      Instr.run env (ordinaryByte.entry.body[0]'(by decide)) :=
  Instr.run_loadMonotonic env ⟨0, rfl⟩ (.arg 0 rfl)

private def initial : GlobalState :=
  ⟨⟨1⟩, ⟨Std.ExtHashMap.ofList [(⟨0⟩, ⟨1, 255#8⟩)]⟩⟩

private def readByte (p : PoisonOr Pointer) : Option (BitVec 8) :=
  match atomicByte.eval 1 (atomicByte.args p) initial with
  | .value (some (.cons (.value b) .nil), _) => some b
  | _ => none

#guard readByte (.value ⟨⟨0⟩, 0⟩) == some 255#8
#guard readByte (.value ⟨⟨0⟩, 1⟩) == none
#guard readByte (.value ⟨⟨1⟩, 0⟩) == none
#guard readByte .poison == none

/-- error: ^bb0: "llvm.store"(%arg1, %arg0) : (i8, !llvm.ptr) -> (): atomic accesses are not supported -/
#guard_msgs in
mlir_def atomicStore := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i8):
    "llvm.store"(%arg1, %arg0) <{ordering = 2 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
}

/-- error: ^bb0: %0 = "llvm.atomicrmw"(%arg0, %arg1) : (!llvm.ptr, i8) -> i8: atomic read-modify-write operations are not supported -/
#guard_msgs in
mlir_def atomicRmw := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i8):
    %0 = "llvm.atomicrmw"(%arg0, %arg1) <{ordering = 2 : i64}> : (!llvm.ptr, i8) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

/-- error: ^bb0: %0 = "llvm.load"(%arg0) : (!llvm.ptr) -> i64: monotonic atomic load requires an i8 result -/
#guard_msgs in
mlir_def unsupportedWidth := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.load"(%arg0) <{ordering = 2 : i64}> : (!llvm.ptr) -> i64
    "llvm.return"(%0) : (i64) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.MonotonicLoad
