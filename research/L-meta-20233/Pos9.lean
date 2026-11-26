import UpperCore
namespace PlaneMask
def wits9 : List Witness := [⟨8,128,9259542125404520576⟩, ⟨16,128,9259542668734660736⟩, ⟨32,128,9259681761250541696⟩, ⟨255,255,14466700110149527140⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work9 : wits9.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work9
