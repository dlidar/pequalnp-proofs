import PEqualNP.Defs.MetaComplexity

namespace Comparator9929
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def reference : Circuit := ⟨[⟨.not, [3]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [9, 11]⟩, ⟨.not, [5]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [15, 12]⟩, ⟨.or, [14, 16]⟩], 17⟩
theorem twelve : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide ((1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat) < (1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat))) 12 := by
  refine ⟨reference, ?_, by decide, ?_⟩
  · intro g hg
    simp [reference] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide
#print axioms twelve
end Comparator9929
