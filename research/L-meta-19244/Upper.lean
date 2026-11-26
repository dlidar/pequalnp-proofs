import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask828Witness
def circuit : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [11, 12]⟩], 13⟩
theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents
    (fun u v : Fin 4 => (828 : ℕ).testBit (4*u.val+v.val)) C := by
  refine ⟨circuit,?_,by decide,by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask828Witness
#print axioms Mask828Witness.upper
