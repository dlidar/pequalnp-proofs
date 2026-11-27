import Mathlib
import PEqualNP.Defs
namespace Graph29707
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
def candidate : Circuit := ⟨[⟨.or,[0,7]⟩,
⟨.and,[4,8]⟩,
⟨.or,[0,2]⟩,
⟨.or,[5,7]⟩,
⟨.and,[10,11]⟩,
⟨.or,[1,7]⟩,
⟨.and,[5,13]⟩,
⟨.or,[0,1]⟩,
⟨.or,[3,15]⟩,
⟨.or,[4,16]⟩,
⟨.and,[6,17]⟩,
⟨.or,[9,12]⟩,
⟨.or,[14,19]⟩,
⟨.or,[18,20]⟩],21⟩

def target (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
theorem exact14 : candidate.size = 14 := rfl
theorem monotone_gates : ∀ g∈candidate.gates, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g h; simp only [candidate,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
theorem computes : ∀ x : Fin 8 → Bool, candidate.eval (List.ofFn x) = target x := by decide +kernel
end Graph29707
