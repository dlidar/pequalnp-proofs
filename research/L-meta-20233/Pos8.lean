import UpperCore
namespace PlaneMask
def wits8 : List Witness := [⟨8,64,4629771064841355328⟩, ⟨16,64,4629771881975660608⟩, ⟨32,64,4629981068357812288⟩, ⟨0,128,9259542123273814144⟩, ⟨1,128,9259542123273814271⟩, ⟨2,128,9259542123273846656⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work8 : wits8.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work8
