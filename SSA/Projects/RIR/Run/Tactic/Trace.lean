module

public meta import Lean.Util.Trace

/-! Registration of the `rir` trace class. A trace class has to be registered in a module of its
own, and inside a `meta section`, or importers cannot see the `trace.rir` option. -/

open Lean

meta section

initialize
  registerTraceClass `rir

end
