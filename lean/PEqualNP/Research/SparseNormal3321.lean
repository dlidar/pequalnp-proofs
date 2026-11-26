import PEqualNP.Research.ExactForest3321
import PEqualNP.MetaComplexity.L204

namespace PEqualNP.Research.SparseNormal3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset
open PEqualNP.Research.ForestCase6390 PEqualNP.Research.ForestNormal3321

theorem target_graph {p l} (E : Finset (Fin p × Fin l)) (z : Fin (p+l) → Bool) :
    Target E z ↔ ∃ i j, (graph E).Adj i j ∧ z i = true ∧ z j = true := by
  rw [← edge_on]
  constructor
  · rintro ⟨i,j,h,a,b⟩; exact ⟨(i,j),h,a,b⟩
  · rintro ⟨⟨i,j⟩,h,a,b⟩; exact ⟨i,j,h,a,b⟩

theorem long_threads {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (cycles : ∀ v (c : (graph E).Walk v v), c.IsCycle → 7 ≤ c.length)
    (branches : ∀ u v, u ≠ v → 3 ≤ ((graph E).neighborSet u).ncard →
      3 ≤ ((graph E).neighborSet v).ncard → ∀ w : (graph E).Walk u v, 7 ≤ w.length)
    (fan : FanInTwo C) (eval : ∀ z, circuitFun (p+l) C z = true ↔ Target E z) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (p+l) D ∧ D.size ≤ C.size ∧
      (∀ z, circuitFun (p+l) D z = true ↔ Target E z) ∧ Below E D := by
  classical
  by_cases emp : E = ∅
  · obtain ⟨D,ao,bound,h1,h2⟩ := compile_cover E ∅ ∅ (by simp [emp])
    exact ⟨D,ao,by simp [emp] at bound; omega,h1,h2⟩
  let G := graph E
  let covers := (univ : Finset (Fin (p+l))).powerset.filter (fun T => ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
  have nonempty : covers.Nonempty := ⟨univ,by simp [covers]⟩
  obtain ⟨T,hT,hmin⟩ := covers.exists_min_image Finset.card nonempty
  have cov := (mem_filter.mp hT).2
  have opt (T' : Finset (Fin (p+l))) (ok : ∀ i j, G.Adj i j → i ∈ T' ∨ j ∈ T') :
      T.card ≤ T'.card := hmin T' (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),ok⟩)
  obtain ⟨e,he⟩ := nonempty_iff_ne_empty.mpr emp
  obtain ⟨i,j,adj,_⟩ := (target_graph E (fun _ => true)).mp ⟨e.1,e.2,he,rfl,rfl⟩
  have lower := L204 (p+l) T.card C.size G ∅ cycles branches (by simp) (Or.inr ⟨i,j,adj⟩) opt
    ⟨C,fan,le_rfl,fun z => by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,notMem_empty,false_and,exists_false, false_or]
      exact (eval z).trans (target_graph E z)⟩
  have bound : E.card + T.card ≤ C.size + 1 := by simpa [G,edge_count] using lower
  obtain ⟨P,L,coverage,k⟩ := split_cover E T cov
  obtain ⟨D,ao,sz,h1,h2⟩ := compile_cover E P L coverage
  exact ⟨D,ao,by omega,h1,h2⟩

end PEqualNP.Research.SparseNormal3321
