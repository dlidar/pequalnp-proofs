import Core
namespace PEqualNP.Outside.Mask114591
theorem split_node (k e : Nat) (ws : List W) (d : List (Nat × List W))
    (cert : ∀ p ∈ d, optimized k p.1 p.2 = false)
    (h0 : (ws == [goal]) = false)
    (covered : (pairs ws).all (fun (a,b,r) => !(dispatch e (fun j l => !d.contains (j,l)) a b r)) = true) :
    optimized (k+1) e ws = false := by
  have place (j : Nat) (l : List W) : optimized k j l = true → !d.contains (j,l) = true := by
    intro h
    by_contra! hn
    have hm : (j,l) ∈ d := by simpa using hn
    have := cert (j,l) hm
    simp_all
  apply Bool.eq_false_iff.mpr
  intro h
  change (ws == [goal] || (pairs ws).any _) = true at h
  simp only [h0, Bool.false_or, List.any_eq_true] at h
  obtain ⟨⟨a,b,r⟩, hm, hh⟩ := h
  have hn := List.all_eq_true.mp covered (a,b,r) hm
  change (!dispatch e _ a b r) = true at hn
  simp only [dispatch, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true] at hh
  have go : dispatch e (fun j l => !d.contains (j,l)) a b r = true := by
    simp only [dispatch, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true]
    obtain ⟨w, hw, h⟩ := hh
    refine ⟨w,hw,?_⟩
    rcases h with ((⟨x,y⟩ | ⟨x, (⟨a1,b1⟩ | ⟨a2,b2⟩)⟩) | ⟨⟨x,y⟩,z⟩)
    · exact Or.inl (Or.inl ⟨x,place _ _ y⟩)
    · exact Or.inl (Or.inr ⟨x,Or.inl ⟨a1,place _ _ b1⟩⟩)
    · exact Or.inl (Or.inr ⟨x,Or.inr ⟨a2,place _ _ b2⟩⟩)
    · exact Or.inr ⟨⟨x,y⟩,place _ _ z⟩
  simp_all
end PEqualNP.Outside.Mask114591
#print axioms PEqualNP.Outside.Mask114591.split_node
