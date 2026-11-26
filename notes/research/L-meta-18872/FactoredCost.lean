import TriangleOwners
namespace PEqualNP.Research.TripleOwners
open Finset
/-- If every tuple from a product of three nonempty edge sets is a triangle,
    then each coordinate is fixed. -/
theorem box_rigid (A B C : Finset Edge) (sound : ∀ i∈A,∀ j∈B,∀ k∈C,∃ t,forms i j k t)
    {i i' j j' k k' : Edge} (hi : i∈A) (hi' : i'∈A) (hj : j∈B) (hj' : j'∈B)
    (hk : k∈C) (hk' : k'∈C) : i=i' ∧ j=j' ∧ k=k' := by
  obtain ⟨_,u⟩ := sound i hi j hj k hk
  obtain ⟨_,v⟩ := sound i' hi' j hj k hk
  obtain ⟨_,y⟩ := sound i hi j' hj' k hk
  obtain ⟨_,z⟩ := sound i hi j hj k' hk'
  exact ⟨Fin.ext ((unique_edges u).2.1.symm.trans (unique_edges v).2.1),
         Fin.ext ((unique_edges u).2.2.symm.trans (unique_edges y).2.2),
         Fin.ext ((unique_edges u).1.symm.trans (unique_edges z).1)⟩

/-- Each outer product multiplies a linear factor by a sum of quadratic products.
    A quadratic product multiplies two linear factors. Every generated monomial
    must be a triangle, and all twenty triangles must occur. -/
theorem factored_cost {G D : Type} [Fintype G] [Fintype D]
    (group : D → G) (A : G → Finset Edge) (B C : D → Finset Edge)
    (ha : ∀ g,(A g).Nonempty) (hb : ∀ d,(B d).Nonempty) (hc : ∀ d,(C d).Nonempty)
    (sound : ∀ d,∀ i∈A (group d),∀ j∈B d,∀ k∈C d,∃ t,forms i j k t)
    (covers : ∀ t : Triangle,∃ d,∃ i∈A (group d),∃ j∈B d,∃ k∈C d,forms i j k t) :
    6 ≤ Fintype.card G ∧ 20 ≤ Fintype.card D ∧ 46 ≤ Fintype.card G + 2*Fintype.card D := by
  classical
  choose a ma using ha
  choose b mb using hb
  choose c mc using hc
  choose label ml using fun d => sound d (a _) (ma _) (b d) (mb d) (c d) (mc d)
  have covered (t : Triangle) : ∃ d,label d=t ∧ a (group d)∈verts t := by
    obtain ⟨d,i,hi,j,hj,k,hk,ht⟩ := covers t
    obtain ⟨rfl,rfl,rfl⟩ := box_rigid _ _ _ (sound d) hi (ma _) hj (mb _) hk (mc _)
    refine ⟨d,distinct_triangles ((ml d).symm.trans ht),?_⟩
    rw [← ht];simp
  have hit : Hit (univ.image a) := by
    apply (hit_spec _).mpr
    intro t
    obtain ⟨d,_,h⟩ := covered t
    exact ⟨_,h,mem_image.mpr ⟨_,mem_univ _,rfl⟩⟩
  have groups : 6 ≤ Fintype.card G := (owner_bound _ hit).trans (card_image_le.trans (by simp))
  have surj : Function.Surjective label := fun t => by
    obtain ⟨d,h,_⟩ := covered t
    exact ⟨d,h⟩
  have terms : 20 ≤ Fintype.card D := by simpa using Fintype.card_le_of_surjective label surj
  exact ⟨groups,terms,by omega⟩
end PEqualNP.Research.TripleOwners
