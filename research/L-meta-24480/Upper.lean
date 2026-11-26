import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask2113947Witness
def circuit : Circuit := ⟨[⟨.not, [0]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 8]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [12, 11]⟩, ⟨.not, [13]⟩], 14⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113947 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask2113947Witness
#print axioms Mask2113947Witness.upper
