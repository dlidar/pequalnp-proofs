import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask100287Witness
def circuit : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 8]⟩], 11⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100287 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask100287Witness
#print axioms Mask100287Witness.upper
