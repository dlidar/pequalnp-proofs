import Mathlib
import PEqualNP.Defs.Represents
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Mask114591Profiles
def A (u : Fin 4) (v : Fin 5) := (114591 : Nat).testBit (5*u.val+v.val)
def nNot (c : Circuit) : Nat := (c.gates.filter (fun g => match g.op with | .not => true | _ => false)).length
def uses (c : Circuit) : List Nat := (List.range 9).filter fun i => c.gates.any fun g => g.inputs.contains i
def c0 : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [15, 14]⟩], 16⟩
theorem c0_exact : FanInTwo c0 ∧ c0.size = 8 ∧ nNot c0 = 1 ∧ uses c0 = [0, 1, 2, 4, 5, 8] ∧ PEqualNP.Represents.Represents A c0 := by
  refine ⟨?_, by decide, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp [c0] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
#print axioms c0_exact
def c1 : Circuit := ⟨[⟨.or, [8, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [12, 3]⟩, ⟨.not, [13]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [14, 15]⟩], 16⟩
theorem c1_exact : FanInTwo c1 ∧ c1.size = 8 ∧ nNot c1 = 1 ∧ uses c1 = [1, 2, 3, 4, 5, 8] ∧ PEqualNP.Represents.Represents A c1 := by
  refine ⟨?_, by decide, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp [c1] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
#print axioms c1_exact
def c2 : Circuit := ⟨[⟨.not, [1]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 9]⟩, ⟨.or, [14, 15]⟩], 16⟩
theorem c2_exact : FanInTwo c2 ∧ c2.size = 8 ∧ nNot c2 = 2 ∧ uses c2 = [1, 2, 3, 4, 5, 8] ∧ PEqualNP.Represents.Represents A c2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp [c2] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
#print axioms c2_exact
end Mask114591Profiles
