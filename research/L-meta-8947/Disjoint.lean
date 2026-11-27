import Matching

open Finset PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
open PEqualNP.Research.ReadTwoDensity PEqualNP.Research.PlaneResidual PEqualNP.Research.PlaneMatching

namespace PEqualNP.Research.HardMatching

theorem countAsWeights {N : ℕ} (S : Fin N → Finset (Fin N)) (C : Circuit) :
    (hardFlags S C).card = ∑ l, ∑ p ∈ S l, if (p,l) ∈ hardFlags S C then 1 else 0 := by
  classical
  have eq1 (l : Fin N) : (∑ p ∈ S l, if (p,l) ∈ hardFlags S C then 1 else 0) =
      ∑ p : Fin N, if (p,l) ∈ hardFlags S C then 1 else 0 := by
    apply sum_subset (subset_univ _) 
    intro p _ hp
    have : (p,l) ∉ hardFlags S C := fun he => hp (mem_filter.mp he).2.1
    simp [this]
  simp_rw [eq1]
  rw [sum_comm,← sum_product']
  simp [univ_product_univ]

theorem disjointHardFlags (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card = q+1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (ho : C.output < N+N+C.size) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (short : 100*C.size < N*q) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ (∀ l, f l ∈ S l) ∧
       467*N < 1000*(univ.filter fun l => (f l,l) ∈ hardFlags S C).card ∧
       (422 ≤ q → N < 2*(univ.filter fun l => (f l,l) ∈ hardFlags S C).card) := by
  classical
  obtain ⟨f,hi,hm,wt⟩ := matchingWeight (q+1) S (fun l p => if (p,l) ∈ hardFlags S C then 1 else 0)
    (by omega) hc (PEqualNP.Outside.L_meta_5351.linesThrough_card S (by omega) hN hc hu)
  rw [← countAsWeights,← card_filter] at wt
  refine ⟨f,hi,hm,?_,?_⟩
  · have fraction := (residual q N S C hq hN hc hu h ho hr hf short).2
    have bound := fraction.trans_le (Nat.mul_le_mul_left 1000 wt)
    rw [← Nat.mul_assoc, Nat.mul_left_comm 1000, ← Nat.mul_comm (1000*_)] at bound
    exact Nat.lt_of_mul_lt_mul_right bound
  · intro large
    have fraction := halfHardFlags q N S C large hN hc hu h ho hr hf short
    have bound := fraction.trans_le (Nat.mul_le_mul_left 2 wt)
    simp only [one_mul] at bound
    rw [Nat.mul_left_comm 2, Nat.mul_comm (q+1)] at bound
    exact Nat.lt_of_mul_lt_mul_right bound

end PEqualNP.Research.HardMatching
