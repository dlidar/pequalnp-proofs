import PEqualNP.Defs

namespace PEqualNP.Research.DisjointAnd

-- The two types label the disjoint input sets of an AND, in either order.
-- Allow edges inside each side to avoid presupposing that the cut is a bipartition.
theorem classify {U V : Type} (P : Set U → Prop) (Q : Set V → Prop)
    (left : U → U → Prop) (cross : U → V → Prop) (right : V → V → Prop)
    (zeroP : ¬ P ∅) (zeroQ : ¬ Q ∅)
    (exactly : ∀ s t, (P s ∧ Q t) ↔
      (∃ a ∈ s, ∃ b ∈ s, left a b) ∨ (∃ a ∈ s, ∃ b ∈ t, cross a b) ∨
      (∃ a ∈ t, ∃ b ∈ t, right a b))
    (edge : ∃ a b, cross a b) :
    (∀ a b, ¬ left a b) ∧ (∀ a b, ¬ right a b) ∧
    (∀ a b, cross a b ↔ (∃ j, cross a j) ∧ (∃ i, cross i b)) ∧
    (∀ s, P s ↔ ∃ a ∈ s, ∃ b, cross a b) ∧
    (∀ t, Q t ↔ ∃ b ∈ t, ∃ a, cross a b) := by
  classical
  have noLeft (a b) (h : left a b) : False :=
    zeroQ ((exactly Set.univ ∅).mpr (Or.inl ⟨a,Set.mem_univ _,b,Set.mem_univ _,h⟩)).2
  have noRight (a b) (h : right a b) : False :=
    zeroP ((exactly ∅ Set.univ).mpr (Or.inr (Or.inr ⟨a,Set.mem_univ _,b,Set.mem_univ _,h⟩))).1
  have clean (s t) : (P s ∧ Q t) ↔ ∃ a ∈ s, ∃ b ∈ t, cross a b := by
    rw [exactly]
    constructor
    · rintro (⟨a,_,b,_,h⟩ | h | ⟨a,_,b,_,h⟩)
      · exact (noLeft a b h).elim
      · exact h
      · exact (noRight a b h).elim
    · exact fun h => Or.inr (Or.inl h)
  obtain ⟨a₀,b₀,inc⟩ := edge
  obtain ⟨pAll,qAll⟩ := (clean Set.univ Set.univ).mpr
    ⟨a₀,Set.mem_univ _,b₀,Set.mem_univ _,inc⟩
  have sideP (s) : P s ↔ ∃ a ∈ s, ∃ b, cross a b := by
    simpa [qAll] using clean s Set.univ
  have sideQ (t) : Q t ↔ ∃ b ∈ t, ∃ a, cross a b := by
    have h := clean Set.univ t
    simp only [pAll,true_and,Set.mem_univ,true_and] at h
    rw [h]
    constructor
    · rintro ⟨a,b,hb,hab⟩; exact ⟨b,hb,a,hab⟩
    · rintro ⟨b,hb,a,hab⟩; exact ⟨a,b,hb,hab⟩
  refine ⟨noLeft,noRight,?_,sideP,sideQ⟩
  intro a b
  simpa [sideP,sideQ] using (clean ({a} : Set U) ({b} : Set V)).symm

-- The rectangle collapses to a star if it has no four-cycle.
theorem star {U V : Type} (E : U → V → Prop)
    (rectangle : ∀ a b, E a b ↔ (∃ j, E a j) ∧ (∃ i, E i b))
    (noFour : ∀ a c b d, a ≠ c → b ≠ d → ¬ (E a b ∧ E a d ∧ E c b ∧ E c d))
    (edge : ∃ a b, E a b) :
    (∃ c, ∀ a b, E a b → a=c) ∨ (∃ d, ∀ a b, E a b → b=d) := by
  classical
  obtain ⟨c,d,cd⟩ := edge
  by_cases allRows : ∀ a b, E a b → a=c
  · exact Or.inl ⟨c,allRows⟩
  push Not at allRows
  obtain ⟨a,b,ab,ac⟩ := allRows
  refine Or.inr ⟨d,?_⟩
  intro i j ij
  by_contra jd
  have four := noFour a c j d ac jd
  exact four ⟨(rectangle a j).mpr ⟨⟨b,ab⟩,⟨i,ij⟩⟩,
    (rectangle a d).mpr ⟨⟨b,ab⟩,⟨c,cd⟩⟩,
    (rectangle c j).mpr ⟨⟨d,cd⟩,⟨i,ij⟩⟩,cd⟩

end PEqualNP.Research.DisjointAnd
