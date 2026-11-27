import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask4294973Witness
def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.not, [1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [14, 11]⟩], 15⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294973 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask4294973Witness
#print axioms Mask4294973Witness.upper
