import Mathlib
import PEqualNP.Library.Helpers.Replay
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace PEqualNP.Research.Gate26392
def witness : Circuit := ⟨[⟨.not,[5]⟩,⟨.and,[3,5]⟩,⟨.and,[4,10]⟩,⟨.or,[11,12]⟩],13⟩
theorem four : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 4 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 0, 1, 30] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨witness, PEqualNP.Library.Helpers.Replay.fanInTwoB_sound (by decide +kernel), rfl, ?_⟩
  decide +kernel
theorem negation : ¬ (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 0, 1, 30] : List ℕ).getD u.val 0).testBit v.val) C)) := by
  intro claim
  obtain ⟨C,h,m,v⟩ := four
  exact claim ⟨C,h,by omega,v⟩
#print axioms four
#print axioms negation
end PEqualNP.Research.Gate26392
