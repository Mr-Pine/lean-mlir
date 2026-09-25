module

public import SSA.Projects.RIR.Semantics.Func

namespace LeanMLIR.RIR

public section

theorem ofBool_eq_one_iff (b : Bool) : BitVec.ofBool b = 1#1 ↔ b = true := by cases b <;> decide

end

end LeanMLIR.RIR
