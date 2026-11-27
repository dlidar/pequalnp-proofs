import Dictionary

namespace PinStates
open Finset PEqualNP.Outside.L_pcx_375_aux
abbrev Entry (m : ℕ) := Fin 4 × Fin m
abbrev Inv (m : ℕ) := Entry m → Fin (m+1)
def weight {m : ℕ} (c : Inv m) : ℕ := ∑ j, (j.2.val+1)*(c j).val
def partials (m : ℕ) : Finset (Inv m) := univ.filter (fun c => weight c ≤ m)
def pad {m : ℕ} (hm : 0 < m) (c : Inv m) : Inv m :=
  let z : Entry m := (0,⟨0,hm⟩)
  fun j => if j=z then ⟨min m ((c j).val + (m-weight c)),by omega⟩ else c j
theorem coord_le {m : ℕ} (c : Inv m) (j : Entry m) : (c j).val ≤ weight c :=
  calc (c j).val ≤ (j.2.val+1)*(c j).val := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
       _ ≤ weight c := Finset.single_le_sum (f := fun k : Entry m => (k.2.val+1)*(c k).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
theorem pad_val {m : ℕ} (hm : 0 < m) (c : Inv m) (hc : weight c ≤ m) (j : Entry m) :
    (pad hm c j).val = (c j).val + if j=(0,⟨0,hm⟩) then m-weight c else 0 := by
  have h := coord_le c j
  by_cases eq : j=(0,⟨0,hm⟩)
  · subst j; simp [pad]; omega
  · simp [pad,eq]
theorem weight_pad {m : ℕ} (hm : 0 < m) (c : Inv m) (hc : weight c ≤ m) :
    weight (pad hm c) = m := by
  classical
  let z : Entry m := (0,⟨0,hm⟩)
  unfold weight
  simp_rw [pad_val hm c hc, Nat.mul_add, mul_ite, mul_zero]
  rw [sum_add_distrib]
  change weight c + (∑ j : Entry m, if j=z then (j.2.val+1)*(m-weight c) else 0) = m
  simp [z, Nat.add_sub_of_le hc]
theorem partials_card {m : ℕ} (hm : 0 < m) :
    (partials m).card ≤ (m+1)*2^(70*(Nat.sqrt m+1)) := by
  classical
  let encode := fun c : Inv m => (weight c,pad hm c)
  have hmap : ∀ c ∈ partials m, encode c ∈ (range (m+1)) ×ˢ Part4 m := by
    intro c hc
    have small := (mem_filter.mp hc).2
    exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le small), mem_filter.mpr ⟨mem_univ _,weight_pad hm c small⟩⟩
  have inj : ∀ a ∈ partials m, ∀ b ∈ partials m, encode a = encode b → a=b := by
    intro a ha b hb eq
    have same : weight a = weight b := congrArg Prod.fst eq
    have sameP : pad hm a = pad hm b := congrArg Prod.snd eq
    funext j
    apply Fin.ext
    have e := congrArg Fin.val (congrFun sameP j)
    rwa [pad_val hm a (mem_filter.mp ha).2, pad_val hm b (mem_filter.mp hb).2, same, Nat.add_left_inj] at e
  calc (partials m).card ≤ ((range (m+1)) ×ˢ Part4 m).card := card_le_card_of_injOn encode hmap inj
       _ ≤ _ := by rw [card_product,card_range]; exact Nat.mul_le_mul_left _ (part4_card_le m)

def states (m : ℕ) := (partials m) ×ˢ (range (m+1) ×ˢ (range (m+1) ×ˢ (range 3 ×ˢ (range (m+1) ×ˢ range 3))))
theorem state_count {m : ℕ} (hm : 0 < m) :
    (states m).card ≤ (9*(m+1)^4) * 2^(70*(Nat.sqrt m+1)) := by
  simp only [states, card_product,card_range]
  calc _ ≤ ((m+1)*2^(70*(Nat.sqrt m+1))) * ((m+1)*((m+1)*(3*((m+1)*3)))) :=
          Nat.mul_le_mul_right _ (partials_card hm)
       _ = _ := by ring
end PinStates
