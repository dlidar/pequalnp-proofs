import UpperCore
namespace PlaneMask
def wits7 : List Witness := [⟨32,32,2315130721911447584⟩, ⟨64,32,2377654450624929824⟩, ⟨128,32,18383729001276383264⟩, ⟨0,64,4629771061636907072⟩, ⟨2,64,4629771061636955968⟩, ⟨4,64,4629771061649424448⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work7 : wits7.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work7
