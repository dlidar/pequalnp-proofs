import UpperCore
namespace PlaneMask
def wits1 : List Witness := [⟨32,0,280375465082880⟩, ⟨64,0,71776119061217280⟩, ⟨128,0,18374686479671623680⟩, ⟨0,1,72340172838076673⟩, ⟨1,1,72340172838076927⟩, ⟨2,1,72340172838141697⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work1 : wits1.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work1
