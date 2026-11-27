import Mathlib
import PEqualNP.Defs
namespace Graph32249
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def candidate : Circuit := ⟨[⟨.and,[0,3]⟩,
⟨.or,[0,1]⟩,
⟨.or,[4,6]⟩,
⟨.and,[9,10]⟩,
⟨.or,[0,2]⟩,
⟨.or,[3,12]⟩,
⟨.or,[5,7]⟩,
⟨.and,[13,14]⟩,
⟨.or,[2,4]⟩,
⟨.and,[6,16]⟩,
⟨.and,[5,7]⟩,
⟨.or,[8,11]⟩,
⟨.or,[15,19]⟩,
⟨.or,[17,20]⟩,
⟨.or,[18,21]⟩], 22⟩
def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
theorem exact15 : candidate.size = 15 := rfl
theorem monotone_gates : ∀ g∈candidate.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g h; simp only [candidate,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
theorem computes : ∀ x : Fin 8 → Bool, candidate.eval (List.ofFn x) = target x := by decide +kernel
end Graph32249
