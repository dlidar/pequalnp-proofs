import PEqualNP.Research.ForestNormal3321

namespace PEqualNP.Research.ForestNormal3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem point_one_rejects {N : ℕ} (E : Finset (Fin N × Fin N)) (p : Fin N) :
    ¬ Target E (fun k => decide (k = Fin.castAdd N p)) := by
  rintro ⟨_,b,_,_,eq⟩
  exact PEqualNP.Research.ForestCase6390.different p b (of_decide_eq_true eq).symm

theorem line_one_rejects {N : ℕ} (E : Finset (Fin N × Fin N)) (l : Fin N) :
    ¬ Target E (fun k => decide (k = Fin.natAdd N l)) := by
  rintro ⟨a,_,_,eq,_⟩
  exact PEqualNP.Research.ForestCase6390.different a l (of_decide_eq_true eq)

theorem assigned_forest : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v (c : (PEqualNP.Research.ForestCase6390.graph (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2))).Walk v v), ¬ c.IsCycle) → (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + j) false = true → (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C forest _ mono _ computes
  classical
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  have target (z : Fin (N+N) → Bool) :
      Target E z ↔ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by simp [Target,E]
  have fan : FanInTwo C := by
    intro g hg
    obtain ⟨op,sz⟩ := mono g hg
    refine ⟨?_,sz⟩
    rcases op with h|h
    · simp [h]
    · have e : g.op = .or := h; simp [e]
  obtain ⟨D,ao,size,ev,below⟩ := forest_normal E C forest fan (fun z => (computes z).trans (target z).symm)
  refine ⟨D,?_,ao.2.1,size,fun z => (ev z).trans (target z),?_,?_⟩
  · intro g hg;exact ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  · intro j hj op z val; exact Or.inr (Or.inr ((target z).mp (below j hj op z val)))
  · intro j hj op
    exact ⟨fun p => Bool.eq_false_iff.mpr (fun h => point_one_rejects E p (below j hj op _ h)),
           fun l => Bool.eq_false_iff.mpr (fun h => line_one_rejects E l (below j hj op _ h))⟩

#print axioms assigned_forest
end PEqualNP.Research.ForestNormal3321
