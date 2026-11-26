import UpperCore
namespace PlaneMask
def wits5 : List Witness := [⟨8,8,578721386848585736⟩, ⟨16,8,578722443561535496⟩, ⟨32,8,578992962076674056⟩, ⟨0,16,1157442765409226768⟩, ⟨2,16,1157442765409287952⟩, ⟨8,16,1157442769418981392⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work5 : wits5.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work5
