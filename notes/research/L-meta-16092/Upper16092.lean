import Samples
namespace PEqualNP.Research.Signed16092
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def nine : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [12, 13]⟩], 14⟩
theorem nine_monotone : Monotone2 nine := by simp [nine,Monotone2]
theorem nine_size : nine.size=9 := rfl
theorem nine_eval : ∀ x : Fin 6 → Bool,nine.eval (List.ofFn x)=F5 x := by decide +kernel
#print axioms nine_monotone
#print axioms nine_size
#print axioms nine_eval
end PEqualNP.Research.Signed16092
