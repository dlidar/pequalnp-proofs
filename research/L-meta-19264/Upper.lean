-- Explicit witness from the merged monotone result L_meta_6085.
import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask5087Witness
def circuit : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩,
    ⟨.and, [1, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
theorem upper : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents
    (fun u v : Fin 4 => (5087 : ℕ).testBit (4*u.val+v.val)) C := by
  refine ⟨circuit,?_,by decide,by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask5087Witness
#print axioms Mask5087Witness.upper
