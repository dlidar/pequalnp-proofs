import UpperCore
namespace PlaneMask
def wits6 : List Witness := [⟨32,16,1157705548688265232⟩, ⟨64,16,1224715284843073552⟩, ⟨128,16,18379207740474003472⟩, ⟨0,32,2314885530818453536⟩, ⟨4,32,2314885530833068064⟩, ⟨16,32,2314886488596160544⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work6 : wits6.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work6
