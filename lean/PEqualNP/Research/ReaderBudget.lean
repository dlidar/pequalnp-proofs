import Mathlib
import PEqualNP.Defs.MetaComplexity
namespace PEqualNP.Research.ReaderBudget
open Finset PEqualNP.CircuitLowerBounds
def used (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def readers (gs : List Gate) (i : ℕ) := (gs.filter (fun g => (used g).contains i)).length
theorem used_le_two (g : Gate) : (used g).length ≤ 2 := by
  cases h : g.op.eval [false] <;> simp [used,h,List.length_take] <;> omega
theorem one_gate (g : Gate) (m : ℕ) : (∑ i ∈ range m, if i∈used g then 1 else 0) ≤ 2 := by
  rw [← card_filter]
  have sub : (range m).filter (fun i => i∈used g) ⊆ (used g).toFinset := by simp [subset_iff]
  exact (card_le_card sub).trans ((List.toFinset_card_le _).trans (used_le_two g))
theorem all_slots (gs : List Gate) (m : ℕ) : (∑ i ∈ range m, readers gs i) ≤ 2*gs.length := by
  induction gs with
  | nil => simp [readers]
  | cons g gs ih =>
    have h (i) : readers (g::gs) i = (if i∈used g then 1 else 0) + readers gs i := by
      by_cases hi : i∈used g <;> simp [readers,hi,List.filter_cons,Nat.add_comm]
    simp only [h,sum_add_distrib,List.length_cons]
    have := one_gate g m;omega
theorem raw_slots (C : Circuit) (n : ℕ)
    (live : C.size ≤ 1 + ∑ j ∈ range C.size,readers C.gates (n+j)) :
    (∑ i ∈ range n,readers C.gates i) ≤ C.size+1 := by
  have h := all_slots C.gates (n+C.size)
  rw [sum_range_add] at h
  change _ ≤ 2*C.size at h;omega
theorem budget_of_cover (C : Circuit) (n edges cover : ℕ)
    (live : C.size ≤ 1 + ∑ j ∈ range C.size,readers C.gates (n+j))
    (benchmark : C.size+1 ≤ edges+cover) (regular : 2*edges = 3*n) (cheap : 14*cover ≤ 9*n) :
    7*(∑ i : Fin n, readers C.gates i.val) ≤ 15*n := by
  rw [Fin.sum_univ_eq_sum_range]
  have := raw_slots C n live;omega
end PEqualNP.Research.ReaderBudget
