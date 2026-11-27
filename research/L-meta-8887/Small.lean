import Packing
import PEqualNP.Defs
namespace PEqualNP.Research.Packing8887
open Finset
theorem row_count {n : ℕ} (E : Finset (Fin n × Fin n)) (a : Fin n) :
    (row E a).card = (E.filter fun z => z.1 = a).card := by
  let f : Fin n ↪ Fin n × Fin n := ⟨Prod.mk a, fun _ _ h => congrArg Prod.snd h⟩
  have eq : (row E a).map f = E.filter fun z => z.1 = a := by
    ext ⟨x,y⟩
    constructor
    · intro h
      obtain ⟨i,hi,he⟩ := Finset.mem_map.mp h
      change (a,i) = (x,y) at he
      cases he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2,rfl⟩
    · intro h
      obtain ⟨he,hh⟩ := Finset.mem_filter.mp h
      change x = a at hh
      subst x
      exact Finset.mem_map.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  rw [← eq,Finset.card_map]
theorem col_count {n : ℕ} (E : Finset (Fin n × Fin n)) (b : Fin n) :
    (col E b).card = (E.filter fun z => z.2 = b).card := by
  let f : Fin n ↪ Fin n × Fin n := ⟨fun a => (a,b), fun _ _ h => congrArg Prod.fst h⟩
  have eq : (col E b).map f = E.filter fun z => z.2 = b := by
    ext ⟨x,y⟩
    constructor
    · intro h
      obtain ⟨i,hi,he⟩ := Finset.mem_map.mp h
      change (i,b) = (x,y) at he
      cases he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2,rfl⟩
    · intro h
      obtain ⟨he,hh⟩ := Finset.mem_filter.mp h
      change y = b at hh
      subst y
      exact Finset.mem_map.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,rfl⟩
  rw [← eq,Finset.card_map]
theorem small_order : have x1 : (x1 : ℕ) → Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 x5 x6 x7 : Fin x1), x4 ≠ x5 → x6 ≠ x7 → ¬((x4, x6) ∈ x2 ∧ (x4, x7) ∈ x2 ∧ (x5, x6) ∈ x2 ∧ (x5, x7) ∈ x2)) ∧ (∃ (x4 : Equiv.Perm (Fin x1)), ∀ (x5 : Fin x1), (x5, x4 x5) ∈ x2) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ ∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), (x5, x6) ∈ x2 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true); ∀ (x2 : ℕ) (x3 : Finset (Fin x2 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≤ 6 → x1 x2 x3 x4 → (∀ (x6 : Fin x2), (3 : ℕ) ≤ {x7 ∈ x3 | x7.1 = x6}.card ∧ (3 : ℕ) ≤ {x7 ∈ x3 | x7.2 = x6}.card) → x3.card + x2 ≤ x4.size + (1 : ℕ) := by
  intro _ n E C hn h hd
  by_cases hz : n = 0
  · subst n
    have hem : E = ∅ := by ext p; exact Fin.elim0 p.1
    simp [hem]
  · let a : Fin n := ⟨0,by omega⟩
    have ha : 3 ≤ (row E a).card := by rw [row_count]; exact (hd a).1
    have hc : ∀ b ∈ row E a, 3 ≤ (col E b).card := by
      intro b _
      rw [col_count]
      exact (hd b).2
    have := minimum_seven E h.1 a ha hc
    omega
#print axioms small_order
end PEqualNP.Research.Packing8887
