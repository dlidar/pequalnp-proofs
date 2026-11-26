import UpperCore
namespace PlaneMask
def wits6 : List Witness := [⟨16,16,1157443791906410512⟩, ⟨32,16,1157705548688265232⟩, ⟨64,16,1224715284843073552⟩, ⟨0,32,2314885530818453536⟩, ⟨1,32,2314885530818453759⟩, ⟨2,32,2314885530818510624⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work6 : wits6.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work6
