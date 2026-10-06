module

import SSA.Projects.RIR.Semantics.Operations.InboundsGep

/-! Guard the logical dependencies of every public inbounds GEP proof. -/

/-- info: 'LeanMLIR.RIR.Operation.gepInboundsOffsets_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanMLIR.RIR.Operation.gepInboundsOffsets_singleton

/-- info: 'LeanMLIR.RIR.Operation.gepInboundsIndex_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanMLIR.RIR.Operation.gepInboundsIndex_eq

/-- info: 'LeanMLIR.RIR.Operation.gepInboundsLive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanMLIR.RIR.Operation.gepInboundsLive_eq

/-- info: 'LeanMLIR.RIR.Operation.gepInboundsLive_poison_of_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanMLIR.RIR.Operation.gepInboundsLive_poison_of_invalid

/-- info: 'LeanMLIR.RIR.Operation.gepInbounds_address_no_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanMLIR.RIR.Operation.gepInbounds_address_no_wrap

/-- info: 'LeanMLIR.RIR.Operation.gepInbounds_negative_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanMLIR.RIR.Operation.gepInbounds_negative_wrap

