module

public meta import Lean.Util.Trace

/-! Registration of the `rir` trace class. A trace class has to be registered in a module of its
own, and inside a `meta section`, or importers cannot see the `trace.rir` option. -/

open Lean

meta section

initialize
  registerTraceClass `rir

end

public meta section

/-- The depth past which a call's state is cut (`0`: never): before the call, the state `S` becomes
a bare base, `hS` reversed, and the later states are built on it, so state terms, and instantiating
the proof, stay small along a long chain of calls. Reads then stop at the base. -/
register_option rir.stateDepth : Nat := {
  defValue := 0
  descr := "the depth of a state's term past which a call keeps the state as a bare base \
    (0: never)" }

end
