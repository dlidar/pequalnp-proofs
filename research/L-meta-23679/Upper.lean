import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask815999Witness
def circuit : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [14, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [5, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩
theorem upper : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815999 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask815999Witness
#print axioms Mask815999Witness.upper
