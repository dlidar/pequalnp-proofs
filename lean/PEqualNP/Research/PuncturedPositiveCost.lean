import PEqualNP.Research.PuncturedPlaneRank

namespace PEqualNP.Research.PuncturedPlaneCut
open Finset

def oneRow (K : Type*) [Field K] (x y : Side) : K := if posted (input 21 [] x y) then 1 else 0

theorem positive_products_lower (K : Type*) [Field K] {k : Nat}
    (A B : Fin k → Side → K)
    (compute : ∀ x y, oneRow K x y = ∑ i, A i x * B i y) : 24924 ≤ k := by
  let a : Fin (k+1) → Side → K := Fin.cons (fun _ => 1) (fun i x => -(A i x))
  let b : Fin (k+1) → Side → K := Fin.cons (fun _ => 1) B
  have lower := separated_products_lower K a b (by
    intro x y
    rw [Fin.sum_univ_succ]
    simp only [a,b,Fin.cons_zero,Fin.cons_succ,one_mul,neg_mul,Finset.sum_neg_distrib,←compute]
    cases h : posted (input 21 [] x y) <;> simp [zeroRow,oneRow,h])
  omega

end PEqualNP.Research.PuncturedPlaneCut
