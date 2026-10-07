import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInit
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceAppend
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceFinish
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram

/-! The existing verifier's three SHA slots now have source-corresponding SLLVM
CFG values. This definition supplies programs, not their execution contracts. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource

def programs : FiredancerShaPrograms := ⟨init, append, finish⟩

theorem programs_init : programs.init = init := rfl
theorem programs_append : programs.append = append := rfl
theorem programs_finish : programs.finish = finish := rfl

end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
