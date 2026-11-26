import UpperCore
namespace PlaneMask
def wits3 : List Witness := [⟨8,2,144680349920788994⟩, ⟨64,2,215893514783949314⟩, ⟨128,2,18375251637271921154⟩, ⟨0,4,289360691352306692⟩, ⟨4,4,289360691368756228⟩, ⟨8,4,289360695563387908⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work3 : wits3.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work3
