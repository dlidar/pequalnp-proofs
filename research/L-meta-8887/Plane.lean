import Packing
namespace PEqualNP.Research.Packing8887
open Finset
theorem other_rows {E : Finset (Fin 7 × Fin 7)} (h : Sparse E) (a : Fin 7)
    (ha : 3 ≤ (row E a).card) (hc : ∀ b ∈ row E a, 3 ≤ (col E b).card) :
    (row E a).biUnion (fun b => (col E b).erase a) = univ.erase a := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro d hd
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hd
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1,Finset.mem_univ _⟩
  have hd : (row E a : Set (Fin 7)).PairwiseDisjoint (fun b => (col E b).erase a) := by
    intro b hb c hc' hbc
    apply Finset.disjoint_left.mpr
    intro d hdb hdc
    simp only [Finset.mem_erase,col,Finset.mem_filter,Finset.mem_univ,true_and] at hdb hdc
    exact h a d b c hdb.1.symm hbc ⟨(Finset.mem_filter.mp hb).2,(Finset.mem_filter.mp hc').2,hdb.2,hdc.2⟩
  rw [Finset.card_biUnion hd, Finset.card_erase_of_mem (Finset.mem_univ _)]
  have he := extremal_row E h a ha hc
  calc
    _ = ∑ _b ∈ row E a, 2 := by simp [he]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro b hb
      have hm : a ∈ col E b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
      have eq : ((col E b).erase a).card = (col E b).card - 1 := Finset.card_erase_of_mem hm
      rw [eq]
      have := hc b hb
      omega

theorem common_column {E : Finset (Fin 7 × Fin 7)} (h : Sparse E) (a d : Fin 7)
    (had : a ≠ d) (ha : 3 ≤ (row E a).card) (hc : ∀ b ∈ row E a, 3 ≤ (col E b).card) :
    ∃! b, (a,b) ∈ E ∧ (d,b) ∈ E := by
  have hd : d ∈ (univ : Finset (Fin 7)).erase a := by simp [had.symm]
  rw [← other_rows h a ha hc] at hd
  obtain ⟨b, hba, hbd⟩ := Finset.mem_biUnion.mp hd
  have hab := (Finset.mem_filter.mp hba).2
  have hdb := (Finset.mem_filter.mp (Finset.mem_erase.mp hbd).2).2
  refine ⟨b,⟨hab,hdb⟩,?_⟩
  intro c hc'
  by_contra hn
  exact h a d c b had hn ⟨hc'.1,hab,hc'.2,hdb⟩
#print axioms common_column
end PEqualNP.Research.Packing8887
