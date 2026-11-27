import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask114591OneNot
def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [15, 14]⟩], 16⟩
theorem exactly_one_inverter : (circuit.gates.filter fun g => match g.op with | .not => true | _ => false).length = 1 := by decide
#print axioms exactly_one_inverter
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (114591 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [circuit] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end Mask114591OneNot
#print axioms Mask114591OneNot.upper
