import Restrict
import CloneUpper
import Lower
open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Mask114591Family Mask114591Restrict
namespace Mask114591CloneExact
theorem cloned_minimum (k : Nat) :
    (∃ C : Circuit, FanInTwo C ∧ C.size = 8 ∧
       (C.gates.filter (fun g => match g.op with | .not => true | _ => false)).length = 1 ∧
       Represents (clone k) C) ∧
    (∀ C : Circuit, FanInTwo C → Represents (clone k) C → 8 ≤ C.size) := by
  refine ⟨Mask114591CloneUpper.cloned_upper k, ?_⟩
  intro C hc hr
  by_contra small
  apply exact_negation
  refine ⟨trim 9 k C, trim_fanin _ _ hc, ?_, ?_⟩
  · rw [trim_size]; omega
  · apply trim_rep hr
    intro u v
    simp [clone,project,base,v.isLt]
end Mask114591CloneExact
#print axioms Mask114591CloneExact.cloned_minimum
