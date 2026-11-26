import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask4500Witness
def circuit : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 2]⟩, ⟨.or, [7, 10]⟩], 11⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4500 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask4500Witness
#print axioms Mask4500Witness.upper
