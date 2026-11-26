import UpperCore
namespace PlaneMask
def wits2 : List Witness := [⟨16,1,72341263759769857⟩, ⟨32,1,72619448791531777⟩, ⟨128,1,18374969058471772417⟩, ⟨0,2,144680345676153346⟩, ⟨1,2,144680345676153599⟩, ⟨4,2,144680345692733954⟩]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 50000000 in
theorem work2 : wits2.all (fun w => decide (Works w)) = true := by decide +kernel
end PlaneMask
#print axioms PlaneMask.work2
