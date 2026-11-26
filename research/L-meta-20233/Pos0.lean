import UpperCore
namespace PlaneMask
def wits0 : List Witness := [⟨0,0,0⟩, ⟨1,0,255⟩, ⟨2,0,65280⟩, ⟨4,0,16711680⟩, ⟨8,0,4278190080⟩, ⟨16,0,1095216660480⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work0 : wits0.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work0
