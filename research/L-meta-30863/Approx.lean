import Reference
namespace Graph30863
open PEqualNP.CircuitLowerBounds
def small : Circuit := ⟨[⟨.or,[0,7]⟩,
⟨.or,[3,5]⟩,
⟨.or,[6,9]⟩,
⟨.and,[8,10]⟩,
⟨.and,[1,4]⟩,
⟨.or,[1,2]⟩,
⟨.or,[5,7]⟩,
⟨.and,[13,14]⟩,
⟨.or,[2,3]⟩,
⟨.and,[6,16]⟩,
⟨.or,[11,12]⟩,
⟨.or,[15,18]⟩,
⟨.or,[17,19]⟩],20⟩
theorem small_size : small.size=13 := rfl
theorem small_errors : ∀ x : Fin 8 → Bool,small.eval (List.ofFn x)=(target x && decide (x≠(fun i : Fin 8 => (129:Nat).testBit i.val) ∧ x≠(fun i : Fin 8 => (145:Nat).testBit i.val))) := by decide +kernel
end Graph30863
