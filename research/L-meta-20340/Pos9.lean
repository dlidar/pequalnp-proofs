import UpperCore
namespace PlaneMask
def wits9 : List Witness := [⟨32,128,9259681761250541696⟩, ⟨64,128,9295289445316067456⟩, ⟨128,128,18410856566090662016⟩, ⟨255,255,1885146376704737940⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work9 : wits9.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work9
