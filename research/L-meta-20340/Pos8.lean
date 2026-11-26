import UpperCore
namespace PlaneMask
def wits8 : List Witness := [⟨16,64,4629771881975660608⟩, ⟨64,64,4683532782188642368⟩, ⟨128,64,18392771522881142848⟩, ⟨0,128,9259542123273814144⟩, ⟨4,128,9259542123282137216⟩, ⟨8,128,9259542125404520576⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work8 : wits8.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work8
