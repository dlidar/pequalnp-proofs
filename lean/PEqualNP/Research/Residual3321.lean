import PEqualNP.Research.Obstruction3321
import PEqualNP.Research.Girth3321
import PEqualNP.Research.PaddedCycle3321
namespace PEqualNP.Research.Residual3321
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ForestCase6390 PEqualNP.Research.ForestNormal3321 PEqualNP.Research.Girth3321
open PEqualNP.Research.Obstruction3321

def Posted {N} (E : Finset (Fin N × Fin N)) (s : ℕ) : Prop := ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ s ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, (p,l) ∈ E ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + j) false = true → (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, (p,l) ∈ E ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)

theorem strong_to_posted {N} (E : Finset (Fin N × Fin N)) (s : ℕ) : HasNormal E s → Posted E s := by
  rintro ⟨D,ao,sz,out,below⟩
  refine ⟨D,?_,ao.2.1,sz,out,?_,?_⟩
  · intro g hg;exact ⟨ao.1 g hg,(ao.2.2 g hg).le⟩
  · intro j hj op z val; exact Or.inr (Or.inr (below j hj op z val))
  · intro j hj op
    exact ⟨fun p => Bool.eq_false_iff.mpr (fun h => point_one_rejects E p (below j hj op _ h)),
           fun l => Bool.eq_false_iff.mpr (fun h => line_one_rejects E l (below j hj op _ h))⟩

theorem residual {N} (E : Finset (Fin N × Fin N)) (C : Circuit) (sq : SquareFree E)
    (fan : FanInTwo C) (ev : ∀ z, circuitFun (N+N) C z = true ↔ Target E z)
    (failure : ¬ Posted E C.size) :
    (∀ (P L : Finset (Fin N)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) →
      C.size + 1 < E.card + P.card + L.card) ∧
    (∃ v, ∃ c : (graph E).Walk v v, c.IsCycle) ∧
    ((∃ v, ∃ c : (graph E).Walk v v, c.IsCycle ∧ c.length = 6) ∨
      ∃ u v, u ≠ v ∧ 3 ≤ ((graph E).neighborSet u).ncard ∧
        3 ≤ ((graph E).neighborSet v).ncard ∧ ∃ w : (graph E).Walk u v, w.length ≤ 6) := by
  obtain ⟨budget,cycle,short|branches⟩ := necessary E C fan ev (fun h => failure (strong_to_posted _ _ h))
  · obtain ⟨v,c,hc,len⟩ := short
    exact ⟨budget,cycle,Or.inl ⟨v,c,hc,Nat.le_antisymm len (six_or_more E sq v c hc)⟩⟩
  · exact ⟨budget,cycle,Or.inr branches⟩

theorem small_edges {N} (E : Finset (Fin N × Fin N)) (C : Circuit) (sq : SquareFree E)
    (few : E.card ≤ 5) (fan : FanInTwo C) (ev : ∀ z, circuitFun (N+N) C z = true ↔ Target E z) :
    Posted E C.size := by
  by_contra fail
  obtain ⟨_,⟨v,c,hc⟩,_⟩ := residual E C sq fan ev fail
  have low := six_or_more E sq v c hc
  have high := hc.isTrail.length_le_ncard_edgeSet
  rw [edge_count] at high
  omega

theorem isolated_cycle {N k} (hk : 3 ≤ k) (left right : Fin k ↪ Fin N) (C : Circuit) (fan : FanInTwo C) :
    let E := (PEqualNP.Research.CycleNormal3321.edges k).image fun e => (left e.1,right e.2)
    (∀ z, circuitFun (N+N) C z = true ↔ Target E z) → Posted E C.size := by
  intro E ev
  exact strong_to_posted _ _ (PEqualNP.Research.PaddedCycle3321.padded_cycle hk left right C fan ev)
end PEqualNP.Research.Residual3321
