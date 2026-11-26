import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask270649255Witness
def circuit : Circuit := ⟨[⟨.not, [0]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [9, 8]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649255 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask270649255Witness
#print axioms Mask270649255Witness.upper
