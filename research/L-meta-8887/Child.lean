import Essential
namespace PEqualNP.Research.Live8887
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
theorem minUse : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
        PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
        (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ x4.size ∧
          PEqualNP.TopForm.IsAO2 (x1 + x1) D ∧
          (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) D x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧
          ∀ w < x1 + x1 + D.size, w ∈ D.output :: List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) D.gates := by
  intro n E π C hπ hao he
  obtain ⟨D,hs,hD,hfun,hused⟩ := prune C hao
  have he' : ∀ x, circuitFun (n+n) D x = incidence E x := fun x => (congrFun hfun x).trans (he x)
  refine ⟨D,hs,hD,he',?_⟩
  intro w hw
  change w ∈ uses D
  by_cases hleft : w < n
  · let a : Fin n := ⟨w,hleft⟩
    exact (endpoints_used (hπ a) D hD he').1
  by_cases hraw : w < n+n
  · let b : Fin n := ⟨w-n,by omega⟩
    have hb := (endpoints_used (hπ (π.symm b)) D hD he').2
    rw [Equiv.apply_symm_apply] at hb
    change n + (w-n) ∈ uses D at hb
    simpa [show n + (w-n) = w by omega] using hb
  · change w < n+n+D.gates.length at hw
    have hg : w-(n+n) < D.gates.length := by omega
    have h := hused ⟨w-(n+n),hg⟩
    change n+n+(w-(n+n)) ∈ uses D at h
    simpa [show n+n+(w-(n+n)) = w by omega] using h
#print axioms minUse
end PEqualNP.Research.Live8887
