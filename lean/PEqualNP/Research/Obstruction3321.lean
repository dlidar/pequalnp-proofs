import PEqualNP.Research.SparseNormal3321

namespace PEqualNP.Research.Obstruction3321

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ForestCase6390 PEqualNP.Research.ForestNormal3321
open PEqualNP.Research.SparseNormal3321

def HasNormal {p l : ℕ} (E : Finset (Fin p × Fin l)) (s : ℕ) : Prop :=
  ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧ D.size ≤ s ∧
    (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ Below E D

theorem necessary {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (fan : FanInTwo C) (ev : ∀ z, circuitFun (p+l) C z = true ↔ Target E z)
    (bad : ¬ HasNormal E C.size) :
    (∀ (P : Finset (Fin p)) (L : Finset (Fin l)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) →
      C.size + 1 < E.card + P.card + L.card) ∧
    (∃ v, ∃ c : (graph E).Walk v v, c.IsCycle) ∧
    ((∃ v, ∃ c : (graph E).Walk v v, c.IsCycle ∧ c.length ≤ 6) ∨
      ∃ u v, u ≠ v ∧ 3 ≤ ((graph E).neighborSet u).ncard ∧
        3 ≤ ((graph E).neighborSet v).ncard ∧ ∃ w : (graph E).Walk u v, w.length ≤ 6) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro P L cov
    by_contra! low
    obtain ⟨D,ao,sz,out,good⟩ := compile_cover E P L cov
    exact bad ⟨D,ao,by omega,out,good⟩
  · by_contra h
    exact bad (forest_normal E C (fun v c hc => h ⟨v,c,hc⟩) fan ev)
  · by_contra h
    apply bad
    apply long_threads E C _ _ fan ev
    · intro v c hc
      by_contra! short
      exact h (Or.inl ⟨v,c,hc,by omega⟩)
    · intro u v diff du dv w
      by_contra! short
      exact h (Or.inr ⟨u,v,diff,du,dv,w,by omega⟩)

end PEqualNP.Research.Obstruction3321
