import Boxes

namespace FieldCoverage
open Module LinearMap
noncomputable section
def levelSize (q a b i : ℕ) := if i<a then q-1 else if i=a then b else 0

theorem level_totals (q b : ℕ) (hq : 1 < q) (hb : b < q) (m a : ℕ)
    (ha : a ≤ m) (hend : a=m → b=0) :
    (∑ i : Fin m, levelSize q a b i) = a*(q-1)+b ∧
    (∏ i : Fin m, (q-levelSize q a b i)) =
      q^(m-a)-b*q^(m-a-1) := by
  induction m generalizing a with
  | zero =>
    have : a=0 := by omega
    subst a
    simp [hend rfl]
  | succ m ih =>
    cases a with
    | zero =>
      rw [Fin.sum_univ_succ,Fin.prod_univ_succ]
      have rest (i : Fin m) : levelSize q 0 b i.succ.val = 0 := by simp [levelSize]
      simp only [rest,Nat.sub_zero,Finset.sum_const_zero,add_zero,Finset.prod_const,
        Finset.card_univ,Fintype.card_fin,Nat.zero_mul,zero_add,Nat.add_one_sub_one]
      simp [levelSize,Nat.sub_mul,pow_succ']
    | succ a =>
      have r := ih a (by omega) (by intro e; exact hend (by omega))
      have step (i : Fin m) : levelSize q (a+1) b i.succ.val = levelSize q a b i.val := by
        simp [levelSize]
      have head : levelSize q (a+1) b 0 = q-1 := by simp [levelSize]
      rw [Fin.sum_univ_succ,Fin.prod_univ_succ]
      simp only [Fin.val_zero,head,step,r.1,r.2,Nat.succ_sub_succ_eq_sub]
      have one : q-(q-1)=1 := by omega
      rw [one,one_mul,Nat.succ_mul]
      omega

theorem allocate {E : Type} [Field E] [Fintype E] [DecidableEq E]
    (m c : ℕ) (hc : c ≤ m*(Fintype.card E-1)) :
    let q := Fintype.card E
    let a := c/(q-1)
    let b := c%(q-1)
    ∃ L : Fin m → Finset E, (∀ i, 0 ∉ L i) ∧
      (∑ i, (L i).card) = c ∧
      (∏ i, (q-(L i).card)) = q^(m-a)-b*q^(m-a-1) := by
  classical
  intro q a b
  have hq : 1 < q := Fintype.one_lt_card
  have hp : 0 < q-1 := by omega
  have hsplit : (q-1)*a+b=c := Nat.div_add_mod c (q-1)
  have hb : b < q-1 := Nat.mod_lt c hp
  have ha : a ≤ m := by
    by_contra! hx
    have hm := Nat.mul_lt_mul_of_pos_left hx hp
    change c ≤ m*(q-1) at hc
    rw [Nat.mul_comm m] at hc
    omega
  have hend : a=m → b=0 := by
    rintro rfl
    change c ≤ a*(q-1) at hc
    rw [Nat.mul_comm a] at hc
    omega
  let D : Finset E := Finset.univ.erase 0
  have cd : D.card=q-1 := by simp [D,q]
  have e (i : Fin m) : ∃ T ⊆ D, T.card = levelSize q a b i := by
    apply Finset.exists_subset_card_eq
    rw [cd]
    unfold levelSize
    split_ifs <;> omega
  choose L sub card using e
  have totals := level_totals q b hq (by omega) m a ha hend
  refine ⟨L,?_,?_,?_⟩
  · intro i hi
    have := sub i hi
    simpa [D] using this
  · simp only [card,totals.1]
    rwa [Nat.mul_comm]
  · simpa only [card] using totals.2

end
end FieldCoverage
