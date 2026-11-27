import Reference
namespace Graph30863
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
def candidate0 : Circuit := ⟨[⟨.or,[0,6]⟩,
⟨.or,[7,8]⟩,
⟨.and,[3,9]⟩,
⟨.or,[0,1]⟩,
⟨.or,[2,11]⟩,
⟨.or,[5,6]⟩,
⟨.or,[7,13]⟩,
⟨.and,[12,14]⟩,
⟨.and,[1,4]⟩,
⟨.and,[7,13]⟩,
⟨.or,[10,15]⟩,
⟨.or,[16,18]⟩,
⟨.or,[17,19]⟩],20⟩
theorem gates0 : candidate0.size=13 := rfl
theorem one_error0 : ∀ x : Fin 8 → Bool,candidate0.eval (List.ofFn x)=(target x || decide (x = fun j : Fin 8 => (66:Nat).testBit j.val)) := by decide +kernel
def candidate1 : Circuit := ⟨[⟨.and,[0,3]⟩,
⟨.or,[0,2]⟩,
⟨.or,[7,9]⟩,
⟨.or,[5,6]⟩,
⟨.and,[10,11]⟩,
⟨.or,[3,9]⟩,
⟨.or,[6,7]⟩,
⟨.and,[13,14]⟩,
⟨.or,[4,5]⟩,
⟨.and,[1,16]⟩,
⟨.or,[8,12]⟩,
⟨.or,[15,18]⟩,
⟨.or,[17,19]⟩],20⟩
theorem gates1 : candidate1.size=13 := rfl
theorem one_error1 : ∀ x : Fin 8 → Bool,candidate1.eval (List.ofFn x)=(target x && !decide (x = fun j : Fin 8 => (130:Nat).testBit j.val)) := by decide +kernel
end Graph30863
