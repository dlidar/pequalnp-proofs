import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask4296639Witness
def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [8, 10]⟩], 11⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4296639 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask4296639Witness
#print axioms Mask4296639Witness.upper
