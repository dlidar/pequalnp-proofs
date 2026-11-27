import Mathlib
import PEqualNP.Defs
namespace Graph29313
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def candidate : Circuit := ⟨[⟨.or,[0,6]⟩,
⟨.and,[4,8]⟩,
⟨.or,[0,1]⟩,
⟨.or,[5,6]⟩,
⟨.and,[10,11]⟩,
⟨.or,[2,6]⟩,
⟨.or,[5,7]⟩,
⟨.and,[13,14]⟩,
⟨.or,[1,3]⟩,
⟨.or,[4,16]⟩,
⟨.and,[7,17]⟩,
⟨.or,[9,12]⟩,
⟨.or,[15,19]⟩,
⟨.or,[18,20]⟩],21⟩
def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
theorem exact14 : candidate.size = 14 := rfl
theorem monotone_gates : ∀ g∈candidate.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g h; simp only [candidate,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
theorem computes : ∀ x : Fin 8 → Bool, candidate.eval (List.ofFn x) = target x := by decide +kernel
end Graph29313
