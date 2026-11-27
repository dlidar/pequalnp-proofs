import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask4294973Witness
def circuit : Circuit := ⟨[⟨.and, [1, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.not, [1]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294973 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask4294973Witness
#print axioms Mask4294973Witness.upper
