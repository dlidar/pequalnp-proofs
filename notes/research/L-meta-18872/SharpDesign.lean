import FactoredCost
namespace PEqualNP.Research.TripleOwners
def center (t : Fin 6) : Fin 15 := ([0, 1, 5, 12, 13, 14] : List (Fin 15)).getD t.val 0
def which (t : Fin 20) : Fin 6 := ([0, 0, 0, 0, 1, 1, 1, 3, 4, 5, 2, 2, 2, 3, 4, 5, 3, 4, 5, 3] : List (Fin 6)).getD t.val 0
def leftEdge (t : Fin 20) : Fin 15 := ([1, 2, 3, 4, 2, 3, 4, 2, 2, 3, 6, 7, 8, 6, 6, 7, 9, 9, 10, 13] : List (Fin 15)).getD t.val 0
def rightEdge (t : Fin 20) : Fin 15 := ([5, 6, 7, 8, 9, 10, 11, 3, 4, 4, 9, 10, 11, 7, 8, 8, 10, 11, 11, 14] : List (Fin 15)).getD t.val 0

theorem assignment : ∀ t,forms (center (which t)) (leftEdge t) (rightEdge t) t := by decide +kernel
def realizable (g d : Nat) := ∃ (group : Fin d → Fin g)
    (A : Fin g → Finset Edge) (B C : Fin d → Finset Edge),
    (∀ i,(A i).Nonempty) ∧ (∀ i,(B i).Nonempty) ∧ (∀ i,(C i).Nonempty) ∧
    (∀ i,∀ x∈A (group i),∀ y∈B i,∀ z∈C i,∃ t,forms x y z t) ∧
    (∀ t : Triangle,∃ i,∃ x∈A (group i),∃ y∈B i,∃ z∈C i,forms x y z t)
theorem sharp_design : realizable 6 20 := by
  refine ⟨which,(fun g => {center g}),(fun t => {leftEdge t}),(fun t => {rightEdge t}),
    (fun _ => Finset.singleton_nonempty _),(fun _ => Finset.singleton_nonempty _),
    (fun _ => Finset.singleton_nonempty _),?_,?_⟩
  · intro i x hx y hy z hz
    simp only [Finset.mem_singleton] at hx hy hz
    subst x;subst y;subst z
    exact ⟨i,assignment i⟩
  · intro t
    exact ⟨t,_,Finset.mem_singleton_self _,_,Finset.mem_singleton_self _,_,Finset.mem_singleton_self _,assignment t⟩
theorem design_minimum (limit : Nat) : (∃ g d,realizable g d ∧ g+2*d ≤ limit) ↔ 46 ≤ limit := by
  constructor
  · rintro ⟨g,d,⟨group,A,B,C,ha,hb,hc,hs,cover⟩,le⟩
    have bound := (factored_cost group A B C ha hb hc hs cover).2.2
    simp only [Fintype.card_fin] at bound
    exact bound.trans le
  · intro h
    exact ⟨6,20,sharp_design,h⟩
end PEqualNP.Research.TripleOwners
