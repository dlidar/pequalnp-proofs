import Mathlib
namespace PEqualNP.Research.Packing8887
open Finset
variable {n : ℕ}
def row (E : Finset (Fin n × Fin n)) (a : Fin n) := univ.filter fun b => (a,b) ∈ E
def col (E : Finset (Fin n × Fin n)) (b : Fin n) := univ.filter fun a => (a,b) ∈ E
def Sparse (E : Finset (Fin n × Fin n)) := ∀ a a' b b', a ≠ a' → b ≠ b' →
  ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E)

theorem radial_bound (E : Finset (Fin n × Fin n)) (h : Sparse E) (a : Fin n) :
    ∑ b ∈ row E a, ((col E b).card-1) ≤ n-1 := by
  classical
  let neighbor := fun b => (col E b).erase a
  have hd : (row E a : Set (Fin n)).PairwiseDisjoint neighbor := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro d hdb hdc
    simp only [neighbor,Finset.mem_erase,col,Finset.mem_filter,Finset.mem_univ,true_and] at hdb hdc
    have hab : (a,b) ∈ E := (Finset.mem_filter.mp hb).2
    have hac : (a,c) ∈ E := (Finset.mem_filter.mp hc).2
    exact h a d b c hdb.1.symm hbc ⟨hab,hac,hdb.2,hdc.2⟩
  have hs : (row E a).biUnion neighbor ⊆ univ.erase a := by
    intro d hd
    obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hd
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1,Finset.mem_univ _⟩
  have hcard := Finset.card_le_card hs
  rw [Finset.card_biUnion hd,Finset.card_erase_of_mem (Finset.mem_univ a)] at hcard
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  calc
    _ = ∑ b ∈ row E a, (neighbor b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hb).2⟩ : a ∈ col E b)).symm
    _ ≤ _ := hcard

theorem contrast (E : Finset (Fin n × Fin n)) (h : Sparse E)
    (a : Fin n) (k : ℕ) (hk : ∀ b ∈ row E a, k+1 ≤ (col E b).card) :
    (row E a).card * k ≤ n-1 := by
  calc
    _ = ∑ _b ∈ row E a, k := by simp
    _ ≤ _ := Finset.sum_le_sum fun b hb => Nat.le_sub_one_of_lt (hk b hb)
    _ ≤ _ := radial_bound E h a

theorem minimum_seven (E : Finset (Fin n × Fin n)) (h : Sparse E) (a : Fin n)
    (ha : 3 ≤ (row E a).card) (hc : ∀ b ∈ row E a, 3 ≤ (col E b).card) :
    7 ≤ n := by
  have := contrast E h a 2 hc
  omega

theorem extremal_row (E : Finset (Fin 7 × Fin 7)) (h : Sparse E) (a : Fin 7)
    (ha : 3 ≤ (row E a).card) (hc : ∀ b ∈ row E a, 3 ≤ (col E b).card) :
    (row E a).card = 3 := by
  have := contrast E h a 2 hc
  omega
#print axioms radial_bound
#print axioms minimum_seven
end PEqualNP.Research.Packing8887
