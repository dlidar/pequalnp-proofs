import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask114591Witness
def circuit : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [13, 14]⟩, ⟨.not, [15]⟩], 16⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (114591 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask114591Witness
#print axioms Mask114591Witness.upper
