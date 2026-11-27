import Prune
namespace PEqualNP.Research.Live8887
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
theorem insensitivity {m : ℕ} (C : Circuit) (ha : IsAO2 m C) (u : Fin m)
    (hu : u.val ∉ uses C) (x y : Fin m → Bool) (hxy : ∀ v ≠ u, x v = y v) :
    circuitFun m C x = circuitFun m C y := by
  have hw : ∀ a : ℕ, a ≠ u.val →
      (C.wires (List.ofFn x)).getD a false = (C.wires (List.ofFn y)).getD a false := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a ih =>
      intro hne
      by_cases h : a < m
      · rw [wires_low _ _ _ (by simpa using h), wires_low _ _ _ (by simpa using h)]
        simpa [List.getD_eq_getElem, h] using hxy ⟨a,h⟩ (fun h => hne (congrArg Fin.val h))
      by_cases hp : m + C.gates.length ≤ a
      · rw [wires_past _ _ _ (by simpa using hp),wires_past _ _ _ (by simpa using hp)]
      let j := a-m
      have hj : j < C.gates.length := by dsimp [j]; omega
      have eq : a = m+j := by dsimp [j]; omega
      rw [eq,wires_gate _ _ _ (List.length_ofFn ..) ha.2.1 j hj,wires_gate _ _ _ (List.length_ofFn ..) ha.2.1 j hj]
      congr 1
      apply List.map_congr_left
      intro b hb
      have back := ha.2.1 j hj b
      rw [gateAt,List.getD_eq_getElem _ _ hj] at back
      apply ih b (eq ▸ back hb)
      intro e
      apply hu
      exact e ▸ List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem .., hb⟩)
  exact hw _ (fun h => hu (by simp [uses,h]))

def incidence {n : ℕ} (E : Finset (Fin n × Fin n)) (x : Fin (n+n) → Bool) :=
  decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)
def leftOnly {n : ℕ} (a : Fin n) (k : Fin (n+n)) := decide (k = Fin.castAdd n a)
def rightOnly {n : ℕ} (b : Fin n) (k : Fin (n+n)) := decide (k = Fin.natAdd n b)
def paired {n : ℕ} (a b : Fin n) (k : Fin (n+n)) := leftOnly a k || rightOnly b k
theorem sides_ne {n : ℕ} (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
  intro h
  have e := congrArg Fin.val h
  simp at e
  omega
theorem edge_on {n : ℕ} {E : Finset (Fin n × Fin n)} {a b : Fin n} (h : (a,b) ∈ E) :
    incidence E (paired a b) = true := by
  apply decide_eq_true
  exact ⟨a,b,h,by simp [paired,leftOnly],by simp [paired,rightOnly]⟩
theorem single_left {n : ℕ} (E : Finset (Fin n × Fin n)) (a : Fin n) :
    incidence E (leftOnly a) = false := by
  apply decide_eq_false
  rintro ⟨u,v,_,_,hv⟩
  exact (sides_ne a v).symm (of_decide_eq_true hv)
theorem single_right {n : ℕ} (E : Finset (Fin n × Fin n)) (b : Fin n) :
    incidence E (rightOnly b) = false := by
  apply decide_eq_false
  rintro ⟨u,v,_,hu,_⟩
  exact (sides_ne u b) (of_decide_eq_true hu)
theorem endpoints_used {n : ℕ} {E : Finset (Fin n × Fin n)} {a b : Fin n} (edge : (a,b) ∈ E)
    (C : Circuit) (ha : IsAO2 (n+n) C) (he : ∀ x, circuitFun (n+n) C x = incidence E x) :
    (Fin.castAdd n a).val ∈ uses C ∧ (Fin.natAdd n b).val ∈ uses C := by
  constructor
  · by_contra h
    have z := insensitivity C ha _ h (paired a b) (rightOnly b) (by
      intro v hv
      simp [paired,leftOnly,hv])
    rw [he,he,edge_on edge,single_right] at z
    contradiction
  · by_contra h
    have z := insensitivity C ha _ h (paired a b) (leftOnly a) (by
      intro v hv
      simp only [paired,rightOnly,decide_eq_false hv,Bool.or_false])
    rw [he,he,edge_on edge,single_left] at z
    contradiction
#print axioms endpoints_used
end PEqualNP.Research.Live8887
