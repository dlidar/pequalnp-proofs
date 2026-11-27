import Structural
import Upper
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Mask114591Family Mask114591CloneCosts

namespace Mask114591CloneFinal
theorem monotone_minimum (k : Nat) :
    RepSizeAtMost (clone k) (10+k) ∧ ¬ RepSizeAtMost (clone k) (9+k) := by
  rw [cloned_budget,cloned_budget]
  exact ⟨PEqualNP.Outside.Mask114591Upper,Mask114591Structural.exact_negation⟩

end Mask114591CloneFinal
#print axioms Mask114591CloneFinal.monotone_minimum
