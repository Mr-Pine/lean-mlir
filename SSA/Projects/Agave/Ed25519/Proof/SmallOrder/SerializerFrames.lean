import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerXL
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerXR
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerYL
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.SerializerYR
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EnvironmentFrame

namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR
open Verifier.Execution.PointConstantTimeEq
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

namespace SerializerXL

theorem writesWithin (p : Primitives) :
    ∀ i ∈ inlineBody p, EnvironmentFrame.WritesWithin 57 208 i := by
  simp (maxSteps := 1000000) [inlineBody, program.entry, EnvironmentFrame.WritesWithin]

/-- Hoisted constants, pointer registers, other copies' fresh locals, and
comparison results outside this exact interval survive the serializer. -/
theorem frame (p : Primitives) (r : Reg program.Γ t)
    (hr : EnvironmentFrame.Outside 57 208 r)
    (E F : Env program.Γ) (s z : GlobalState)
    (h : (inlineBody p).foldlM Instr.run E s = .value (F, z)) : F.read r = E.read r :=
  EnvironmentFrame.fold_of_outside 57 208 r (inlineBody p)
    (writesWithin p) hr E F s z h

end SerializerXL

namespace SerializerXR

theorem writesWithin (p : Primitives) :
    ∀ i ∈ inlineBody p, EnvironmentFrame.WritesWithin 209 360 i := by
  simp (maxSteps := 1000000) [inlineBody, program.entry, EnvironmentFrame.WritesWithin]

/-- Hoisted constants, pointer registers, other copies' fresh locals, and
comparison results outside this exact interval survive the serializer. -/
theorem frame (p : Primitives) (r : Reg program.Γ t)
    (hr : EnvironmentFrame.Outside 209 360 r)
    (E F : Env program.Γ) (s z : GlobalState)
    (h : (inlineBody p).foldlM Instr.run E s = .value (F, z)) : F.read r = E.read r :=
  EnvironmentFrame.fold_of_outside 209 360 r (inlineBody p)
    (writesWithin p) hr E F s z h

end SerializerXR

namespace SerializerYL

theorem writesWithin (p : Primitives) :
    ∀ i ∈ inlineBody p, EnvironmentFrame.WritesWithin 364 515 i := by
  simp (maxSteps := 1000000) [inlineBody, program.entry, EnvironmentFrame.WritesWithin]

/-- Hoisted constants, pointer registers, other copies' fresh locals, and
comparison results outside this exact interval survive the serializer. -/
theorem frame (p : Primitives) (r : Reg program.Γ t)
    (hr : EnvironmentFrame.Outside 364 515 r)
    (E F : Env program.Γ) (s z : GlobalState)
    (h : (inlineBody p).foldlM Instr.run E s = .value (F, z)) : F.read r = E.read r :=
  EnvironmentFrame.fold_of_outside 364 515 r (inlineBody p)
    (writesWithin p) hr E F s z h

end SerializerYL

namespace SerializerYR

theorem writesWithin (p : Primitives) :
    ∀ i ∈ inlineBody p, EnvironmentFrame.WritesWithin 516 667 i := by
  simp (maxSteps := 1000000) [inlineBody, program.entry, EnvironmentFrame.WritesWithin]

/-- Hoisted constants, pointer registers, other copies' fresh locals, and
comparison results outside this exact interval survive the serializer. -/
theorem frame (p : Primitives) (r : Reg program.Γ t)
    (hr : EnvironmentFrame.Outside 516 667 r)
    (E F : Env program.Γ) (s z : GlobalState)
    (h : (inlineBody p).foldlM Instr.run E s = .value (F, z)) : F.read r = E.read r :=
  EnvironmentFrame.fold_of_outside 516 667 r (inlineBody p)
    (writesWithin p) hr E F s z h

end SerializerYR

end Agave.Ed25519.SmallOrder.Execution
