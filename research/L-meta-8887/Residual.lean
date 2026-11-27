import Child
import Reduction
namespace PEqualNP.Research.Live8887

-- Discharge the first hypothesis of the merged reduction verbatim.
theorem remaining (hSurplus :       ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (0 : ℕ) < x1 →
        (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →
        (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →
        PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
        (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →
        have x10 : List ℕ := x4.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x4.gates;
        x2.card ≤ x1 + (x10.length - x10.toFinset.card)) :
  have x1 : (x1 : ℕ) → Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 x5 x6 x7 : Fin x1), x4 ≠ x5 → x6 ≠ x7 → ¬((x4, x6) ∈ x2 ∧ (x4, x7) ∈ x2 ∧ (x5, x6) ∈ x2 ∧ (x5, x7) ∈ x2)) ∧ (∃ (x4 : Equiv.Perm (Fin x1)), ∀ (x5 : Fin x1), (x5, x4 x5) ∈ x2) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ ∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), (x5, x6) ∈ x2 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true); ∀ (x2 : ℕ) (x3 : Finset (Fin x2 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 x2 x3 x4 → (∀ (x6 : Fin x2), (3 : ℕ) ≤ {x7 ∈ x3 | x7.1 = x6}.card ∧ (3 : ℕ) ≤ {x7 ∈ x3 | x7.2 = x6}.card) → x3.card + x2 ≤ x4.size + (1 : ℕ) :=
  PEqualNP.Outside.R_meta_8887_4 minUse hSurplus
#print axioms remaining
end PEqualNP.Research.Live8887
