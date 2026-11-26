import UpperCore
namespace PlaneMask
def wits5 : List Witness := [⟨4,8,578721382720800776⟩, ⟨8,8,578721386848585736⟩, ⟨64,8,648245701952145416⟩, ⟨0,16,1157442765409226768⟩, ⟨1,16,1157442765409227007⟩, ⟨2,16,1157442765409287952⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work5 : wits5.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work5
