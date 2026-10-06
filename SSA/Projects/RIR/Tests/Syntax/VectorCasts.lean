module

public import SSA.Projects.RIR.Syntax.Elab
public import SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func

/-! Integer vector casts keep lane count and apply scalar casts independently, including poison
and overflow flags. These tests exercise the parser, translator, elaborator and interpreter. -/
namespace LeanMLIR.RIR.Tests.Syntax.VectorCasts

@[expose] public section

mlir_def trunc4 := {
  ^bb0(%arg0: vector<4xi16>):
    %0 = "llvm.trunc"(%arg0) : (vector<4xi16>) -> vector<4xi8>
    "llvm.return"(%0) : (vector<4xi8>) -> ()
}

mlir_def zext4 := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.zext"(%arg0) : (vector<4xi8>) -> vector<4xi16>
    "llvm.return"(%0) : (vector<4xi16>) -> ()
}

mlir_def sext4 := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.sext"(%arg0) : (vector<4xi8>) -> vector<4xi16>
    "llvm.return"(%0) : (vector<4xi16>) -> ()
}

mlir_def zextNonNeg := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.zext"(%arg0) <{nonNeg}> : (vector<4xi8>) -> vector<4xi16>
    "llvm.return"(%0) : (vector<4xi16>) -> ()
}

mlir_def truncNuw := {
  ^bb0(%arg0: vector<4xi16>):
    %0 = "llvm.trunc"(%arg0) <{overflowFlags = #llvm.overflow<nuw>}> : (vector<4xi16>) -> vector<4xi8>
    "llvm.return"(%0) : (vector<4xi8>) -> ()
}

mlir_def truncNsw := {
  ^bb0(%arg0: vector<4xi16>):
    %0 = "llvm.trunc"(%arg0) <{overflowFlags = #llvm.overflow<nsw>}> : (vector<4xi16>) -> vector<4xi8>
    "llvm.return"(%0) : (vector<4xi8>) -> ()
}

private def runVec (f : Func) (a : Vals f.Γ.args) (l w : Nat)
    (h : f.tRets = [.vec l w]) : Option ⟦Ty.vec l w⟧ :=
  match f.eval 1 a ⟨default, default⟩ with
  | .value (some vs, _) => match h ▸ vs with
    | .cons v .nil => some v
  | _ => none

#guard runVec trunc4 (trunc4.args #v[.value 0x1234#16, .poison, .value 0xFF80#16, .value 0#16]) 4 8 rfl ==
  some #v[.value 0x34#8, .poison, .value 0x80#8, .value 0#8]
#guard runVec zext4 (zext4.args #v[.value 0x7F#8, .poison, .value 0x80#8, .value 0xFF#8]) 4 16 rfl ==
  some #v[.value 0x7F#16, .poison, .value 0x80#16, .value 0xFF#16]
#guard runVec sext4 (sext4.args #v[.value 0x7F#8, .poison, .value 0x80#8, .value 0xFF#8]) 4 16 rfl ==
  some #v[.value 0x7F#16, .poison, .value 0xFF80#16, .value 0xFFFF#16]
#guard runVec zextNonNeg (zextNonNeg.args #v[.value 0x7F#8, .poison, .value 0x80#8, .value 0#8]) 4 16 rfl ==
  some #v[.value 0x7F#16, .poison, .poison, .value 0#16]
#guard runVec truncNuw (truncNuw.args #v[.value 0xFF#16, .poison, .value 0x100#16, .value 0#16]) 4 8 rfl ==
  some #v[.value 0xFF#8, .poison, .poison, .value 0#8]
#guard runVec truncNsw (truncNsw.args #v[.value 0x7F#16, .poison, .value 0x80#16, .value 0xFF80#16]) 4 8 rfl ==
  some #v[.value 0x7F#8, .poison, .poison, .value 0x80#8]

/-- The lifting applies the scalar semantics to each lane for every input, including poison. -/
theorem vector_cast_lane (op : UnOp (.bv w) (.bv w')) (a : ⟦Ty.vec l w⟧) (i : Fin l) :
    ((UnOp.vector op).compute a)[i.val] = op.compute a[i.val] := by
  simp [UnOp.compute]

/-- info: 'LeanMLIR.RIR.Tests.Syntax.VectorCasts.vector_cast_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vector_cast_lane

/-- error: ^bb0: %0 = "llvm.trunc"(%arg0) : (vector<4xi8>) -> vector<4xi16>: the result must be narrower -/
#guard_msgs in
mlir_def wideningTrunc := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.trunc"(%arg0) : (vector<4xi8>) -> vector<4xi16>
    "llvm.return"(%0) : (vector<4xi16>) -> ()
}

/-- error: ^bb0: %0 = "llvm.zext"(%arg0) : (vector<4xi16>) -> vector<4xi8>: the result must be wider -/
#guard_msgs in
mlir_def narrowingZext := {
  ^bb0(%arg0: vector<4xi16>):
    %0 = "llvm.zext"(%arg0) : (vector<4xi16>) -> vector<4xi8>
    "llvm.return"(%0) : (vector<4xi8>) -> ()
}

/-- error: ^bb0: %0 = "llvm.sext"(%arg0) : (vector<4xi8>) -> vector<4xi8>: the result must be wider -/
#guard_msgs in
mlir_def sameWidthSext := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.sext"(%arg0) : (vector<4xi8>) -> vector<4xi8>
    "llvm.return"(%0) : (vector<4xi8>) -> ()
}

/-- error: ^bb0: %0 = "llvm.zext"(%arg0) : (vector<4xi8>) -> vector<2xi16>: the result has another lane count -/
#guard_msgs in
mlir_def wrongLaneCount := {
  ^bb0(%arg0: vector<4xi8>):
    %0 = "llvm.zext"(%arg0) : (vector<4xi8>) -> vector<2xi16>
    "llvm.return"(%0) : (vector<2xi16>) -> ()
}

/-- error: ^bb0: %0 = "llvm.zext"(%arg0) : (i8) -> vector<4xi16>: expected scalar integers or integer vectors with matching lane counts -/
#guard_msgs in
mlir_def scalarToVector := {
  ^bb0(%arg0: i8):
    %0 = "llvm.zext"(%arg0) : (i8) -> vector<4xi16>
    "llvm.return"(%0) : (vector<4xi16>) -> ()
}

/-- error: ^bb0: %0 = "llvm.trunc"(%arg0) : (vector<4xi16>) -> i8: expected scalar integers or integer vectors with matching lane counts -/
#guard_msgs in
mlir_def vectorToScalar := {
  ^bb0(%arg0: vector<4xi16>):
    %0 = "llvm.trunc"(%arg0) : (vector<4xi16>) -> i8
    "llvm.return"(%0) : (i8) -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.VectorCasts
