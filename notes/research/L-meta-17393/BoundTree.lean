import FormulaMass
namespace PEqualNP.Research.BoundTree17393
open Finset PEqualNP.Research.TripleFormulaMass
variable {R C : Type} [DecidableEq R] [DecidableEq C]
inductive Tree (R : Type) where
  | leaf
  | fork (r : R) (off on : Tree R)
def ceiling (w : R → C → Int) (taken undec : Finset R) (cols : Finset C) : Int :=
  ∑ c ∈ cols,max 0 ((∑ r ∈ taken,w r c)+(∑ r ∈ undec,max 0 (w r c)))
def check (w : R → C → Int) (cols : Finset C) (cap : Int) :
    Tree R → Finset R → Finset R → Bool
  | .leaf,A,B => decide (ceiling w A B cols ≤ cap)
  | .fork t l h,A,B => decide (t∈B) && check w cols cap l A (B.erase t) &&
      check w cols cap h (insert t A) (B.erase t)
theorem envelope (w : R → C → Int) (A B rs : Finset R) (D cs : Finset C)
    (sub : A ⊆ rs) (within : rs ⊆ A ∪ B) (cols : cs ⊆ D) : mass w rs cs ≤ ceiling w A B D := by
  have each (c : C) : (∑ r ∈ rs,w r c) ≤ (∑ r ∈ A,w r c)+(∑ r ∈ B,max 0 (w r c)) := by
    have inc : rs \ A ⊆ B := by
      intro r hr
      exact (mem_union.mp (within (mem_sdiff.mp hr).1)).resolve_left (mem_sdiff.mp hr).2
    have le : (∑ r ∈ rs \ A,w r c) ≤ ∑ r ∈ B,max 0 (w r c) := calc
      _ ≤ ∑ r ∈ rs \ A,max 0 (w r c) := sum_le_sum (fun _ _ => le_max_right _ _)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inc (fun _ _ _ => le_max_left _ _)
    have eq := sum_sdiff (f:=fun r => w r c) sub
    omega
  unfold mass ceiling
  exact (sum_le_sum (fun c _ => (each c).trans (le_max_right _ _))).trans
    (sum_le_sum_of_subset_of_nonneg cols (fun _ _ _ => le_max_left _ _))
theorem checked (w : R → C → Int) (D : Finset C) (cap : Int) (tree : Tree R) (A B rs : Finset R) (cs : Finset C)
    (sub : A ⊆ rs) (within : rs ⊆ A∪B) (cols : cs⊆D) (ok : check w D cap tree A B) :
    mass w rs cs ≤ cap := by
  induction tree generalizing A B with
  | leaf => exact (envelope w A B rs D cs sub within cols).trans (of_decide_eq_true ok)
  | fork t off on ih jh =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at ok
    by_cases ht : t∈rs
    · apply jh (insert t A) (B.erase t) (insert_subset ht sub) _ ok.2
      intro r hr
      rcases mem_union.mp (within hr) with h|h
      · exact mem_union_left _ (mem_insert_of_mem h)
      · by_cases e : r=t
        · exact mem_union_left _ (mem_insert.mpr (Or.inl e))
        · exact mem_union_right _ (mem_erase.mpr ⟨e,h⟩)
    · apply ih A (B.erase t) sub _ ok.1.2
      intro r hr
      rcases mem_union.mp (within hr) with h|h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_erase.mpr ⟨fun e=>ht (e ▸ hr),h⟩)
end PEqualNP.Research.BoundTree17393
