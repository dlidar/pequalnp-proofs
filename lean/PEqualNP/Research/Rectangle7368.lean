import PEqualNP.Defs

namespace PEqualNP.Research.Rectangle7368

abbrev Side := Fin 12
def edge (p l : Side) : Prop :=
  (9 : Fin 13).succAbove p + (0 : Fin 13).succAbove l ∈ ({0,1,3,9} : Finset (Fin 13))
instance (p l : Side) : Decidable (edge p l) := inferInstanceAs (Decidable (_ ∈ _))
def graph : Finset (Side × Side) := Finset.univ.filter fun e => edge e.1 e.2

def partner : Side → Side := ![2,1,11,10,8,7,9,6,5,3,4,0]
theorem perfect_matching : (∀ i, edge i (partner i)) ∧ Function.Injective partner := by
  change (∀ i, edge i (partner i)) ∧ (∀ ⦃i j⦄, partner i = partner j → i = j)
  decide +kernel
theorem graph_card : graph.card = 45 := by decide +kernel
set_option maxRecDepth 30000
set_option maxHeartbeats 2500000

theorem no_square : ∀ p q l k, edge p l → edge p k → edge q l → edge q k → p = q ∨ l = k := by
  decide +kernel

theorem monitor_pairs : (∀ p q l : Side, p ∈ ({0,1,3} : Finset Side) →
    q ∈ ({0,1,3} : Finset Side) → edge p l → edge q l → p = q) ∧
    (∀ l k p : Side, l ∈ ({3,4,6} : Finset Side) →
    k ∈ ({3,4,6} : Finset Side) → edge p l → edge p k → l = k) := by
  decide +kernel

theorem star (A B : Finset Side) (h : ∀ p ∈ A, ∀ l ∈ B, edge p l) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra! bad
  obtain ⟨p,hp,q,hq,pq⟩ := Finset.one_lt_card.mp bad.1
  obtain ⟨l,hl,k,hk,lk⟩ := Finset.one_lt_card.mp bad.2
  exact (no_square p q l k (h p hp l hl) (h p hp k hk) (h q hq l hl) (h q hq k hk)).elim pq lk

theorem rectangle_count {r : ℕ} (A B : Fin r → Finset Side)
    (sound : ∀ i, ∀ p ∈ A i, ∀ l ∈ B i, edge p l)
    (complete : ∀ p l, edge p l → ∃ i, p ∈ A i ∧ l ∈ B i) : 12 ≤ r := by
  choose f hf using fun p => complete p (partner p) (perfect_matching.1 p)
  have inj : Function.Injective f := by
    intro p q eq
    have hp := hf p
    have hq := hf q
    rw [← eq] at hq
    exact (no_square p q (partner p) (partner q)
      (sound _ _ hp.1 _ hp.2) (sound _ _ hp.1 _ hq.2)
      (sound _ _ hq.1 _ hp.2) (sound _ _ hq.1 _ hq.2)).elim id (fun h => perfect_matching.2 h)
  simpa using Fintype.card_le_of_injective f inj

theorem operand_leaves {r : ℕ} (A B : Fin r → Finset Side)
    (nonempty : ∀ i, (A i).Nonempty ∧ (B i).Nonempty)
    (sound : ∀ i, ∀ p ∈ A i, ∀ l ∈ B i, edge p l)
    (complete : ∀ p l, edge p l → ∃ i, p ∈ A i ∧ l ∈ B i) :
    57 ≤ ∑ i, ((A i).card + (B i).card) := by
  have cover : graph ⊆ Finset.univ.biUnion (fun i => (A i).product (B i)) := by
    rintro ⟨p,l⟩ h
    obtain ⟨i,hp,hl⟩ := complete p l (Finset.mem_filter.mp h).2
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_product.mpr ⟨hp,hl⟩⟩
  have hc := (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have htotal : 45 ≤ ∑ i, (A i).card * (B i).card := calc
    _ = graph.card := graph_card.symm
    _ ≤ ∑ i, ((A i).product (B i)).card := hc
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.card_product _ _
  have per (i : Fin r) : (A i).card * (B i).card + 1 ≤ (A i).card + (B i).card := by
    obtain ⟨hp,hl⟩ := nonempty i
    have pp := Finset.card_pos.mpr hp
    have pl := Finset.card_pos.mpr hl
    rcases star _ _ (sound i) with h|h
    · have hh : (A i).card = 1 := by omega
      simp [hh,Nat.add_comm]
    · have hh : (B i).card = 1 := by omega
      simp [hh]
  have hsum : (∑ i, ((A i).card * (B i).card + 1)) ≤ ∑ i, ((A i).card + (B i).card) := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => per i
  have hh : (∑ i, ((A i).card * (B i).card)) + r ≤ ∑ i, ((A i).card + (B i).card) := calc
    _ = ∑ i, ((A i).card * (B i).card + 1) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := hsum
  exact (Nat.add_le_add htotal (rectangle_count A B sound complete)).trans hh

theorem separate_gate_count {r : ℕ} (A B : Fin r → Finset Side)
    (nonempty : ∀ i, (A i).Nonempty ∧ (B i).Nonempty)
    (sound : ∀ i, ∀ p ∈ A i, ∀ l ∈ B i, edge p l)
    (complete : ∀ p l, edge p l → ∃ i, p ∈ A i ∧ l ∈ B i) :
    60 ≤ ((∑ i, ((A i).card + (B i).card)) - 1) + 4 := by
  have h := operand_leaves A B nonempty sound complete
  omega

#print axioms perfect_matching
#print axioms graph_card
#print axioms no_square
#print axioms monitor_pairs
#print axioms star
#print axioms rectangle_count
#print axioms operand_leaves
#print axioms separate_gate_count
end PEqualNP.Research.Rectangle7368
