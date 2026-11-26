import PEqualNP.Research.Residual3321
namespace PEqualNP.Research.Three3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset
open PEqualNP.Research.Residual3321 PEqualNP.Research.ForestNormal3321 PEqualNP.Research.Girth3321
open PEqualNP.Research.CycleNormal3321

def perm : Fin 6 → Fin 3 → Fin 3 := ![![0,1,2],![0,2,1],![1,0,2],![1,2,0],![2,0,1],![2,1,0]]
theorem perm_inj (t : Fin 6) : Function.Injective (perm t) := by
  have all : ∀ (r : Fin 6) (i j : Fin 3), perm r i = perm r j → i = j := by decide +kernel
  exact fun _ _ h => all t _ _ h

def imageCycle (t : Fin 6) := (edges 3).image fun e => (e.1,perm t e.2)
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

theorem classify : ∀ E : Finset (Fin 3 × Fin 3),
    (∀ a b c d : Fin 3, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) →
    E.card ≤ 5 ∨ ∃ t : Fin 6, E = imageCycle t := by decide +kernel

theorem three_by_three (E : Finset (Fin 3 × Fin 3)) (C : Circuit) (sq : SquareFree E) (fan : FanInTwo C)
    (ev : ∀ z, circuitFun (3+3) C z = true ↔ Target E z) : Posted E C.size := by
  rcases classify E sq with short|⟨t,rfl⟩
  · exact small_edges E C sq short fan ev
  · exact isolated_cycle (N:=3) (k:=3) (by decide) (Function.Embedding.refl _) ⟨perm t,perm_inj t⟩ C fan ev
theorem at_most_three {N : ℕ} (hn : N ≤ 3) (E : Finset (Fin N × Fin N)) (C : Circuit)
    (sq : SquareFree E) (fan : FanInTwo C) (ev : ∀ z, circuitFun (N+N) C z = true ↔ Target E z) :
    Posted E C.size := by
  by_cases eq : N = 3
  · subst N;exact three_by_three E C sq fan ev
  · apply small_edges E C sq _ fan ev
    have h := E.card_le_univ
    simp only [Fintype.card_prod,Fintype.card_fin] at h
    interval_cases N <;> omega

end PEqualNP.Research.Three3321
