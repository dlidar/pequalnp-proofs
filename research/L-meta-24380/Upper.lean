import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask34630321039Witness
def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [11, 10]⟩, ⟨.not, [12]⟩], 13⟩
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321039 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask34630321039Witness
#print axioms Mask34630321039Witness.upper
