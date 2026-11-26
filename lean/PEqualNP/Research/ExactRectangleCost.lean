import PEqualNP.Research.IntegralCover
namespace PEqualNP.Research.ExactRectangleCost
open Finset PEqualNP.Research.CapBoundary PEqualNP.Research.IntegralCover
open PEqualNP.Research.StarDesign

def chosen : List Block := [
  .point 0,
  .rectangle {1, 3} {0, 5},
  .rectangle {6} {6, 10},
  .rectangle {3, 5, 6, 8} {2, 5, 7},
  .rectangle {5, 9} {0, 4, 9},
  .rectangle {2, 4, 7, 9} {1, 4, 6, 8},
  .rectangle {2, 8, 11} {2, 8, 12},
  .rectangle {7, 10, 11} {7, 10, 11},
  .rectangle {12} {12},
  .line 3,
  .rectangle {1, 10, 12} {1, 9, 11}]

instance (P L : Finset V) : Decidable (safe P L) := by unfold safe; infer_instance
instance (b : Block) : Decidable b.valid := by cases b <;> unfold Block.valid <;> infer_instance
instance (b : Block) (p l : V) : Decidable (b.hits p l) := by cases b <;> unfold Block.hits <;> infer_instance

theorem same_six : ∀ i : Fin 6, ∀ v : V,
    (testP i).getLsbD v.val = (design.getD i.val 0).getLsbD v.val ∧
    (testL i).getLsbD v.val = (design.getD i.val 0).getLsbD (13+v.val) := by decide +kernel

theorem feasible : ∀ i : Fin chosen.length,(chosen[i.val]).valid := by decide +kernel
theorem flags : ∀ p l : V, inc p l → ∃ j : Fin chosen.length, (chosen[j.val]).hits p l := by decide +kernel
theorem budget : (∑ j : Fin chosen.length,(chosen[j.val]).leaves)-1=48 := by decide +kernel

theorem exact_cost : IsLeast {k : ℕ | ∃ (m : ℕ) (blocks : Fin m → Block),
    (∀ j,(blocks j).valid) ∧ (∀ p l : V, inc p l → ∃ j,(blocks j).hits p l) ∧
    (∑ j,(blocks j).leaves)-1=k} 48 := by
  refine ⟨⟨chosen.length,(fun j => chosen[j.val]),feasible,flags,budget⟩,?_⟩
  rintro k ⟨m,blocks,safe,cover,rfl⟩
  exact restricted_lower blocks safe cover

end PEqualNP.Research.ExactRectangleCost
