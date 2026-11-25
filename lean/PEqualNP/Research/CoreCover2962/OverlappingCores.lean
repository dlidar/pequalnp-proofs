import PEqualNP.Research.CoreCover2962.SparseCores

/-! The union of any subfamily of maximal-core cones has at least as many
gates as distinct raw inputs. Each new root introduces a new collision: either
a collision in its disjoint cone, or a fresh operand reading the last gate it
shares with the old union. -/
namespace PEqualNP.Research.ConeWires
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.LeafBound PEqualNP.Core PEqualNP.TopForm

theorem image_increase {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    {A B : Finset α} (sub : A ⊆ B) {x y : α} (hx : x ∈ B) (fresh : x ∉ A)
    (hy : y ∈ B) (ne : x ≠ y) (eq : f x = f y) :
    (B.image f).card + A.card + 1 ≤ (A.image f).card + B.card := by
  have inc : A ⊆ B.erase x := fun z hz => mem_erase.mpr ⟨fun e => fresh (e ▸ hz),sub hz⟩
  have same : (B.erase x).image f = B.image f := by
    apply Subset.antisymm (image_subset_image (erase_subset ..))
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hw
    by_cases e : v = x
    · subst v
      exact mem_image.mpr ⟨y,mem_erase.mpr ⟨ne.symm,hy⟩,eq.symm⟩
    · exact mem_image_of_mem _ (mem_erase.mpr ⟨e,hv⟩)
  have part : A ∪ (B.erase x \ A) = B.erase x := by
    ext z; simp only [mem_union,mem_sdiff]; grind
  have images := card_union_le (A.image f) ((B.erase x \ A).image f)
  rw [← image_union,part,same] at images
  have small := card_image_le (s := B.erase x \ A) (f := f)
  rw [card_sdiff_of_subset inc] at small
  have := card_le_card inc
  have := card_erase_of_mem hx
  have := card_pos.mpr ⟨x,hx⟩
  omega

def unionSlots (n : Nat) (C : Circuit) (J : Finset Nat) :=
  conesOf n C J ×ˢ (univ : Finset (Fin 2))

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem root_antichain {J : Finset Nat} (sub : J ⊆ maximalCores G C) :
    ∀ i ∈ J, ∀ j ∈ J, ¬ PEqualNP.EdgeOwnership.InCone n C i j := by
  intro i hi j hj
  exact (mem_filter.mp (sub hi)).2.2 j (mem_range.mp (mem_filter.mp (sub hj)).1)
    (mem_filter.mp (sub hj)).2.1

theorem new_collision (ao : IsAO2 n C) {J : Finset Nat} {j : Nat} (new : j ∉ J)
    (sub : insert j J ⊆ maximalCores G C) :
    ∃ x ∈ unionSlots n C (insert j J), x ∉ unionSlots n C J ∧
      ∃ y ∈ unionSlots n C (insert j J), x ≠ y ∧ slotW C x = slotW C y := by
  classical
  let U := conesOf n C J
  let K := coneSet n C j
  have jj : j ∈ insert j J := mem_insert_self _ _
  have core : IsCore G C j := (mem_filter.mp (sub jj)).2.1
  have inc : J ⊆ insert j J := subset_insert _ _
  have anti := root_antichain sub
  have oldValid : ∀ i ∈ J, i < C.gates.length := fun i m => mem_range.mp (mem_filter.mp (sub (inc m))).1
  have kk : K ⊆ conesOf n C (insert j J) := fun _ h => mem_biUnion.mpr ⟨j,jj,h⟩
  have oo : U ⊆ conesOf n C (insert j J) := by
    intro i m
    obtain ⟨g,hg,hi⟩ := mem_biUnion.mp m
    exact mem_biUnion.mpr ⟨g,inc hg,hi⟩
  have notOld : j ∉ U := by
    intro m
    obtain ⟨i,hi,e | ⟨_,cone⟩⟩ := mem_conesOf.mp m
    · exact new (e ▸ hi)
    · exact anti j jj i (inc hi) cone
  by_cases inter : (K ∩ U).Nonempty
  · let a := (K ∩ U).max' inter
    have ha : a ∈ K ∩ U := max'_mem _ _
    obtain ⟨ak,au⟩ := mem_inter.mp ha
    have aj : a ≠ j := fun e => notOld (e ▸ au)
    have ar : a ∉ J := by
      intro m
      rcases mem_insert.mp ak with e | q
      · exact aj e
      · exact anti a (inc m) j jj (mem_filter.mp q).2
    obtain ⟨h,hk,b,read⟩ := K_cover ao core.1 ak aj
    have l := opnd_lt ao (K_lt ao core.1 hk) b
    have gt : a < h := by omega
    have fresh : h ∉ U := by
      intro hh
      have : h ≤ a := le_max' _ _ (mem_inter.mpr ⟨hk,hh⟩)
      omega
    have used := (internally_read ao.2.1 oldValid (root_antichain (inc.trans sub)) a).mpr
      (mem_sdiff.mpr ⟨au,ar⟩)
    rw [operands_as_image ao (valid_union oldValid)] at used
    obtain ⟨y,hy,hyv⟩ := mem_image.mp used
    refine ⟨(h,b),mem_product.mpr ⟨kk hk,mem_univ _⟩,fun m => fresh (mem_product.mp m).1,
      y,mem_product.mpr ⟨oo (mem_product.mp hy).1,mem_univ _⟩,?_,read.trans hyv.symm⟩
    intro e
    apply fresh
    simpa only [← e] using (show y.1 ∈ U from (mem_product.mp hy).1)
  · have collision := colliding_core ao core
    simp only [Set.InjOn,not_forall] at collision
    push Not at collision
    obtain ⟨x,hx,y,hy,eq,ne⟩ := collision
    refine ⟨x,mem_product.mpr ⟨kk (mem_product.mp hx).1,mem_univ _⟩,?_,
      y,mem_product.mpr ⟨kk (mem_product.mp hy).1,mem_univ _⟩,ne,eq⟩
    intro old
    exact inter ⟨x.1,mem_inter.mpr ⟨(mem_product.mp hx).1,(mem_product.mp old).1⟩⟩

theorem all_root_collisions (ao : IsAO2 n C) (J : Finset Nat) (sub : J ⊆ maximalCores G C) :
    J.card + ((unionSlots n C J).image (slotW C)).card ≤ (unionSlots n C J).card := by
  induction J using Finset.induction_on with
  | empty => simp [unionSlots,conesOf]
  | @insert j J hj ih =>
    have inc : J ⊆ insert j J := subset_insert _ _
    have base := ih (inc.trans sub)
    obtain ⟨x,hx,fresh,y,hy,ne,eq⟩ := new_collision ao hj sub
    have sc : unionSlots n C J ⊆ unionSlots n C (insert j J) := by
      intro q hq
      obtain ⟨m,hb⟩ := mem_product.mp hq
      obtain ⟨i,hi,h⟩ := mem_biUnion.mp m
      exact mem_product.mpr ⟨mem_biUnion.mpr ⟨i,inc hi,h⟩,hb⟩
    have delta := image_increase _ sc hx fresh hy ne eq
    rw [card_insert_of_notMem hj]
    omega

theorem pooled_leaf_bound (ao : IsAO2 n C) {J : Finset Nat} (sub : J ⊆ maximalCores G C) :
    (raw n C (conesOf n C J)).card ≤ (conesOf n C J).card := by
  let U := conesOf n C J
  have valid : ∀ i ∈ J, i < C.gates.length := fun i hi => mem_range.mp (mem_filter.mp (sub hi)).1
  have tot : (∑ g ∈ U, (gateAt C g).inputs.length) = (unionSlots n C J).card := by
    have len (g) (h : g ∈ U) : (gateAt C g).inputs.length = 2 := by
      rw [ao_inputs ao (valid_union valid g h)]; rfl
    rw [sum_congr rfl len]; simp [unionSlots,U]
  have reps := all_root_collisions ao J sub
  have cnt := count_wires ao valid (root_antichain sub)
  change U.card + J.card = (raw n C U).card + ((∑ g ∈ U, (gateAt C g).inputs.length) - (operands C U).card) at cnt
  rw [tot, operands_as_image ao (valid_union valid)] at cnt
  change U.card + J.card = (raw n C U).card + ((unionSlots n C J).card -
    ((unionSlots n C J).image (slotW C)).card) at cnt
  change (raw n C U).card ≤ U.card
  omega

theorem core_bound_by_edge_excess (ao : IsAO2 n C) {S T T' : Finset (Fin n)}
    (t : IsMinCover G T) (ht : IsMinCover (G.deleteEdges (deleted G C : Set _)) T')
    (hits : Hits (deleted G C) S)
    (small : (deleted G C).card + S.card ≤ (ends (deleted G C)).card + (maximalCores G C).card) :
    (deleted G C).card + T.card ≤
      (conesOf n C (maximalCores G C)).card + (maximalCores G C).card + T'.card := by
  have rawBound := pooled_leaf_bound ao (G := G) (J := maximalCores G C) (by rfl)
  have support := card_le_card (deleted_ends_raw (G := G) ao)
  rw [card_image_of_injective _ Fin.val_injective] at support
  have delta := cover_extension hits t ht.1
  omega

end PEqualNP.Research.ConeWires

namespace PEqualNP.Research.ConeWires
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Core PEqualNP.TopForm
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- One center per maximal core is enough whenever the accepted edges
collectively number at most their incident vertices (in particular for a
pseudoforest). Neither the cones nor the stars have to be disjoint. -/
theorem overlapping_stars_bound (ao : IsAO2 n C) {T T' : Finset (Fin n)}
    (t : IsMinCover G T) (ht : IsMinCover (G.deleteEdges (deleted G C : Set _)) T')
    (stars : ∀ j ∈ maximalCores G C, ∃ v : Fin n, ∀ e ∈ gammaE G C j, v ∈ e)
    (sparse : (deleted G C).card ≤ (ends (deleted G C)).card) :
    (deleted G C).card + T.card ≤
      (conesOf n C (maximalCores G C)).card + (maximalCores G C).card + T'.card := by
  classical
  let M := maximalCores G C
  let center (j : ↥M) := Classical.choose (stars j.val j.property)
  let S := univ.image center
  have bound : S.card ≤ M.card := by
    simpa only [card_univ,Fintype.card_coe] using (card_image_le (s := univ) (f := center))
  apply core_bound_by_edge_excess ao (S := S) t ht
  · intro u v he
    obtain ⟨j,hj,acc⟩ := mem_biUnion.mp he
    let k : ↥M := ⟨j,hj⟩
    have m : center k ∈ s(u,v) := Classical.choose_spec (stars j hj) _ acc
    have has : center k ∈ S := mem_image_of_mem _ (mem_univ k)
    rcases Sym2.mem_iff.mp m with e | e
    · exact Or.inl (e ▸ has)
    · exact Or.inr (e ▸ has)
  · exact Nat.add_le_add sparse bound

end PEqualNP.Research.ConeWires
