import UpperCore
namespace PlaneMask
def wits4 : List Witness := [⟨32,4,289636668770878468⟩, ⟨64,4,360010910506681348⟩, ⟨128,4,18375816794872218628⟩, ⟨0,8,578721382704613384⟩, ⟨1,8,578721382704613631⟩, ⟨2,8,578721382704676616⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work4 : wits4.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work4
