import Residual
import Mathlib.Combinatorics.Hall.Finite

open Finset

namespace PEqualNP.Research.PlaneMatching

private theorem regularMatching {N d : ℕ} (S : Fin N → Finset (Fin N)) (hd : 0 < d)
    (row : ∀ l, (S l).card = d) (col : ∀ p, (univ.filter fun l => p ∈ S l).card = d) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ ∀ l, f l ∈ S l := by
  classical
  apply (all_card_le_biUnion_card_iff_existsInjective' S).mp
  intro A
  let U := A.biUnion S
  have eq1 (l) (hl : l ∈ A) : (U.filter (· ∈ S l)).card = d := by
    have he : U.filter (· ∈ S l) = S l := by
      ext p
      exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_biUnion.mpr ⟨l,hl,h⟩,h⟩⟩
    rw [he,row]
  have le1 (p : Fin N) : (A.filter fun l => p ∈ S l).card ≤ d := by
    rw [← col p]
    exact card_le_card fun l hl => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hl).2⟩
  have eqsum : (∑ l ∈ A, (U.filter (· ∈ S l)).card) = ∑ p ∈ U, (A.filter fun l => p ∈ S l).card := by
    simp only [card_filter]
    rw [sum_comm]
  have le : A.card*d ≤ U.card*d := calc
    _ = ∑ l ∈ A, (U.filter (· ∈ S l)).card := by simp [sum_congr rfl eq1]
    _ = _ := eqsum
    _ ≤ ∑ _p ∈ U, d := sum_le_sum fun p _ => le1 p
    _ = _ := by simp
  exact Nat.le_of_mul_le_mul_right le hd

/-- Some perfect matching of a regular bipartite graph attains at least its average edge weight. -/
theorem matchingWeight {N : ℕ} (d : ℕ) (S : Fin N → Finset (Fin N)) (w : Fin N → Fin N → ℕ)
    (hd : 0 < d) (row : ∀ l, (S l).card = d)
    (col : ∀ p, (univ.filter fun l => p ∈ S l).card = d) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ (∀ l, f l ∈ S l) ∧
      (∑ l, ∑ p ∈ S l, w l p) ≤ d * ∑ l, w l (f l) := by
  classical
  induction d generalizing S with
  | zero => omega
  | succ k ih =>
    obtain ⟨f,hfi,hf⟩ := regularMatching S hd row col
    let T := fun l => (S l).erase (f l)
    have tr (l) : (T l).card = k := by simp [T,card_erase_of_mem (hf l),row]
    have tc (p) : (univ.filter fun l => p ∈ T l).card = k := by
      obtain ⟨i,rfl⟩ := (Finite.injective_iff_surjective.mp hfi) p
      have e : (univ.filter fun l => f i ∈ T l) = (univ.filter fun l => f i ∈ S l).erase i := by
        ext l
        simp [T,hfi.eq_iff,ne_comm]
      rw [e,card_erase_of_mem (by simp [hf]),col]; omega
    have total : (∑ l, ∑ p ∈ S l, w l p) = (∑ l, ∑ p ∈ T l, w l p) + ∑ l, w l (f l) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun l _ => (sum_erase_add _ _ (hf l)).symm
    cases k with
    | zero =>
      refine ⟨f,hfi,hf,?_⟩
      have et (l) : T l = ∅ := card_eq_zero.mp (tr l)
      simp [total,et]
    | succ k =>
      obtain ⟨g,hgi,hg,wt⟩ := ih T (by omega) tr tc
      by_cases larger : (∑ l, w l (f l)) ≤ ∑ l, w l (g l)
      · refine ⟨g,hgi,fun l => (mem_erase.mp (hg l)).2,?_⟩
        rw [total,Nat.succ_mul]
        exact Nat.add_le_add wt larger
      · refine ⟨f,hfi,hf,?_⟩
        rw [total,Nat.succ_mul]
        exact Nat.add_le_add_right (wt.trans (Nat.mul_le_mul_left _ (by omega))) _

end PEqualNP.Research.PlaneMatching
