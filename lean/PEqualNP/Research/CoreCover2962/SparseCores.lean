import PEqualNP.Research.CoreCover2962.ConeWires
import PEqualNP.Research.CoreCover2962.MatchingLoss
import PEqualNP.MetaComplexity.Helpers.LeafBound

/-! The core-cover target holds when the accepted edge count plus a cover
of those edges exceeds their vertex count by at most one. Maximal cores may
overlap arbitrarily. The source of the unit of slack is a repeated operand
position forced by the project's joint READ-1 definition. -/
namespace PEqualNP.Research.ConeWires
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.LeafBound PEqualNP.Core PEqualNP.EdgeOwnership PEqualNP.TopForm
  PEqualNP.ReadK PEqualNP.Research.CoreCoverCuts
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem operands_as_image {U : Finset Nat} (ao : IsAO2 n C) (valid : ∀ j ∈ U, j < C.gates.length) :
    operands C U = (U ×ˢ (univ : Finset (Fin 2))).image (slotW C) := by
  ext w
  rw [mem_operands, mem_image]
  constructor
  · rintro ⟨g,m,h⟩
    rw [ao_inputs ao (valid g m)] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · exact ⟨(g,0),mem_product.mpr ⟨m,mem_univ _⟩,rfl⟩
    · exact ⟨(g,1),mem_product.mpr ⟨m,mem_univ _⟩,rfl⟩
  · rintro ⟨⟨g,b⟩,m,rfl⟩
    refine ⟨g,(mem_product.mp m).1,?_⟩
    rw [ao_inputs ao (valid g (mem_product.mp m).1)]
    fin_cases b <;> simp [slotW]

/-- The argument for non-injectivity is extracted from the upstream
single-core leaf bound, so the same collision can be used in a union. -/
theorem colliding_core {j : Nat} (ao : IsAO2 n C) (core : IsCore G C j) :
    ¬ Set.InjOn (slotW C) (slots n C j) := by
  obtain ⟨hj,_,_,u,v,_,hh,hrt⟩ := core
  intro inj
  have hjK : j ∈ coneSet n C j := mem_insert_self _ _
  obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ (vec_ne ao u v (n+j) (by omega) hh)
  have bound := vec_le_one ao hj inj u.val v.val u.isLt v.isLt j hjK w hw
  apply absurd hrt
  unfold ReadTwiceAt readsAtMost
  simp only [Bool.not_eq_false]
  rw [List.any_eq_true]
  refine ⟨w,hw,?_⟩
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
  have q := bound i
  rw [List.getD_eq_getElem _ _ hi] at q
  simpa using q

theorem valid_union {M : Finset Nat} (valid : ∀ j ∈ M, j < C.gates.length) :
    ∀ g ∈ conesOf n C M, g < C.gates.length := by
  intro g hg
  obtain ⟨j,m,e | ⟨h,_⟩⟩ := mem_conesOf.mp hg
  · exact e ▸ valid j m
  · exact h

theorem repeat_positive {M : Finset Nat} (ao : IsAO2 n C) (valid : ∀ j ∈ M, j < C.gates.length)
    {j : Nat} (m : j ∈ M) (hj : IsCore G C j) : 1 ≤ repeated C (conesOf n C M) := by
  let U := conesOf n C M
  let S := U ×ˢ (univ : Finset (Fin 2))
  have sub : slots n C j ⊆ S := by
    intro v hv
    obtain ⟨a,b⟩ := mem_product.mp hv
    exact mem_product.mpr ⟨mem_biUnion.mpr ⟨j,m,a⟩,b⟩
  have collision : ¬ Set.InjOn (slotW C) S :=
    fun h => colliding_core ao hj (h.mono sub)
  have strict : (S.image (slotW C)).card < S.card :=
    lt_of_le_of_ne card_image_le (fun eq => collision (card_image_iff.mp eq))
  have len (g) (mg : g ∈ U) : (gateAt C g).inputs.length = 2 := by
    rw [ao_inputs ao (valid_union valid g mg)]
    rfl
  have total : (∑ g ∈ U, (gateAt C g).inputs.length) = S.card := by
    rw [sum_congr rfl len]
    simp [S]
  change 1 ≤ (∑ g ∈ U, (gateAt C g).inputs.length) - (operands C U).card
  rw [total,operands_as_image ao (valid_union valid)]
  change 1 ≤ S.card - (S.image (slotW C)).card
  omega

def deleted (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  (maximalCores G C).biUnion (gammaE G C)
def ends (D : Finset (Sym2 (Fin n))) := D.biUnion Sym2.toFinset

theorem deleted_ends_raw (ao : IsAO2 n C) :
    ((ends (deleted G C)).image Fin.val) ⊆ raw n C (conesOf n C (maximalCores G C)) := by
  intro w hw
  obtain ⟨x,m,rfl⟩ := mem_image.mp hw
  obtain ⟨e,he,hx⟩ := mem_biUnion.mp m
  obtain ⟨j,hj,he⟩ := mem_biUnion.mp he
  obtain ⟨heg,u,v,rfl,acc⟩ := mem_filter.mp he
  have adj : G.Adj u v := by simpa using heg
  have core : IsCore G C j := (mem_filter.mp hj).2.1
  have hs : x.val ∈ (slots n C j).image (slotW C) := by
    rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hx) with rfl | rfl
    · exact end_mem G ao core.1 core.2.1.1 adj acc
    · exact end_mem G ao core.1 core.2.1.1 adj.symm (by rw [pairInput_comm]; exact acc)
  refine mem_filter.mpr ⟨?_,x.isLt⟩
  rw [operands_as_image ao (valid_union (n := n) (fun g (h : g ∈ maximalCores G C) => mem_range.mp (mem_filter.mp h).1))]
  obtain ⟨q,hq,eq⟩ := mem_image.mp hs
  obtain ⟨mk,mu⟩ := mem_product.mp hq
  exact mem_image.mpr ⟨q,mem_product.mpr ⟨mem_biUnion.mpr ⟨j,hj,mk⟩,mu⟩,eq⟩

def Hits (D : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ u v, s(u,v) ∈ D → u ∈ S ∨ v ∈ S

theorem cover_extension {D : Finset (Sym2 (Fin n))} {S T T' : Finset (Fin n)}
    (hits : Hits D S) (t : IsMinCover G T)
    (ht : (G.deleteEdges (D : Set _)).IsVertexCover (T' : Set _)) :
    T.card ≤ T'.card + S.card := by
  have h : G.IsVertexCover ((T' ∪ S : Finset _) : Set _) := by
    intro u v adj
    by_cases e : s(u,v) ∈ D
    · exact (hits _ _ e).imp (mem_union_right _) (mem_union_right _)
    · exact (ht (SimpleGraph.deleteEdges_adj.mpr ⟨adj,e⟩)).imp (mem_union_left _) (mem_union_left _)
  exact (t.2 _ h).trans (card_union_le ..)

theorem sparse_core_bound (ao : IsAO2 n C) {S T T' : Finset (Fin n)}
    (t : IsMinCover G T) (ht : IsMinCover (G.deleteEdges (deleted G C : Set _)) T')
    (hits : Hits (deleted G C) S)
    (small : (deleted G C).card + S.card ≤ (ends (deleted G C)).card + 1) :
    (deleted G C).card + T.card ≤
      (conesOf n C (maximalCores G C)).card + (maximalCores G C).card + T'.card := by
  by_cases m : (maximalCores G C).Nonempty
  · obtain ⟨j,hj⟩ := m
    have extra := repeat_positive ao (fun g (h : g ∈ maximalCores G C) => mem_range.mp (mem_filter.mp h).1)
      hj (show IsCore G C j from (mem_filter.mp hj).2.1)
    have count := maximal_core_wires n G C ao
    have support := card_le_card (deleted_ends_raw (G := G) ao)
    rw [card_image_of_injective _ Fin.val_injective] at support
    have delta := cover_extension hits t ht.1
    dsimp only at count
    omega
  · have em := not_nonempty_iff_eq_empty.mp m
    have d : deleted G C = ∅ := by simp [deleted,em]
    have q : IsMinCover G T' := by simpa [d] using ht
    have low := t.2 T' q.1
    simp [em,d,conesOf,low]

end PEqualNP.Research.ConeWires

namespace PEqualNP.Research.ConeWires
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.LeafBound PEqualNP.Core PEqualNP.TopForm
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Collisions in disjoint sets of slots still give additive savings when
their images overlap: they may even witness repetitions of the same wire. -/
theorem disjoint_collision_count {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (f : α → β) (groups : ι → Finset α) (J : Finset ι) (U : Finset α)
    (sub : ∀ j ∈ J, groups j ⊆ U)
    (dis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (groups i) (groups j))
    (bad : ∀ j ∈ J, ¬ Set.InjOn f (groups j)) :
    J.card + (U.image f).card ≤ U.card := by
  induction J using Finset.induction_on generalizing U with
  | empty => simpa using (Finset.card_image_le (s := U) (f := f))
  | @insert i J hi ih =>
    let X := groups i
    have start := mem_insert_self i J
    have inc : X ⊆ U := sub i start
    have sx : (X.image f).card < X.card := lt_of_le_of_ne card_image_le
      (fun eq => bad i start (card_image_iff.mp eq))
    have js : ∀ j ∈ J, groups j ⊆ U \ X := by
      intro j hj x hx
      have m : j ∈ insert i J := mem_insert_of_mem hj
      exact mem_sdiff.mpr ⟨sub j m hx, fun h => disjoint_left.mp
        (dis j m i start (fun e => hi (e ▸ hj))) hx h⟩
    have rest := ih (U \ X) js (fun a ha b hb => dis a (mem_insert_of_mem ha) b (mem_insert_of_mem hb))
      (fun j hj => bad j (mem_insert_of_mem hj))
    have parts : X ∪ (U \ X) = U := by ext x; simp only [mem_union,mem_sdiff]; grind
    have img : X.image f ∪ (U \ X).image f = U.image f := by rw [← image_union,parts]
    have c := card_union_le (X.image f) ((U \ X).image f)
    rw [img] at c
    rw [card_sdiff_of_subset inc] at rest
    rw [card_insert_of_notMem hi]
    have := card_le_card inc
    omega

/-- Any pairwise gate-disjoint subfamily of maximal cores forces that many
extra operand occurrences in the entire union. Other cores remain unrestricted. -/
theorem repeats_of_packing (ao : IsAO2 n C) {J : Finset Nat}
    (sub : J ⊆ maximalCores G C)
    (dis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (coneSet n C i) (coneSet n C j)) :
    J.card ≤ repeated C (conesOf n C (maximalCores G C)) := by
  let U := conesOf n C (maximalCores G C)
  let S := U ×ˢ (univ : Finset (Fin 2))
  have domain : ∀ j ∈ J, slots n C j ⊆ S := by
    intro j m q hq
    obtain ⟨a,b⟩ := mem_product.mp hq
    exact mem_product.mpr ⟨mem_biUnion.mpr ⟨j,sub m,a⟩,b⟩
  have bound := disjoint_collision_count (slotW C) (slots n C) J S domain
    (fun i hi j hj ne => disjoint_left.mpr (fun _ h m =>
      disjoint_left.mp (dis i hi j hj ne) (mem_product.mp h).1 (mem_product.mp m).1))
    (fun j m => colliding_core ao (show IsCore G C j from (mem_filter.mp (sub m)).2.1))
  have valid : ∀ j ∈ U, j < C.gates.length := valid_union (fun j (h : j ∈ maximalCores G C) =>
    mem_range.mp (mem_filter.mp h).1)
  have total : (∑ j ∈ U, (gateAt C j).inputs.length) = S.card := by
    have len (j) (h : j ∈ U) : (gateAt C j).inputs.length = 2 := by rw [ao_inputs ao (valid j h)]; rfl
    rw [sum_congr rfl len]
    simp [S]
  change J.card ≤ (∑ j ∈ U, (gateAt C j).inputs.length) - (operands C U).card
  rw [total,operands_as_image ao valid]
  change J.card ≤ S.card - (S.image (slotW C)).card
  omega

theorem packed_core_bound (ao : IsAO2 n C) {J : Finset Nat} {S T T' : Finset (Fin n)}
    (sub : J ⊆ maximalCores G C)
    (dis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (coneSet n C i) (coneSet n C j))
    (t : IsMinCover G T) (ht : IsMinCover (G.deleteEdges (deleted G C : Set _)) T')
    (hits : Hits (deleted G C) S)
    (small : (deleted G C).card + S.card ≤ (ends (deleted G C)).card + J.card) :
    (deleted G C).card + T.card ≤
      (conesOf n C (maximalCores G C)).card + (maximalCores G C).card + T'.card := by
  have r := repeats_of_packing ao sub dis
  have count := maximal_core_wires n G C ao
  have support := card_le_card (deleted_ends_raw (G := G) ao)
  rw [card_image_of_injective _ Fin.val_injective] at support
  have delta := cover_extension hits t ht.1
  dsimp only at count
  omega

end PEqualNP.Research.ConeWires

namespace PEqualNP.Research.ConeWires
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Core PEqualNP.TopForm PEqualNP.Research.CoreCoverCuts
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- A star forest (with its centers as S) qualifies even after adding one
edge incident to a center: use the old distinct leaves as representatives.
The conclusion is for the original union of cones, with arbitrary overlaps. -/
theorem distinct_leaves_bound (ao : IsAO2 n C) {S T T' : Finset (Fin n)}
    (t : IsMinCover G T) (ht : IsMinCover (G.deleteEdges (deleted G C : Set _)) T')
    (hits : Hits (deleted G C) S) (active : S ⊆ ends (deleted G C))
    (exception : Sym2 (Fin n)) (leaf : Sym2 (Fin n) → Fin n)
    (mem : ∀ e ∈ (deleted G C).erase exception, leaf e ∈ e ∧ leaf e ∉ S)
    (inj : Set.InjOn leaf ((deleted G C).erase exception : Finset _)) :
    (deleted G C).card + T.card ≤
      (conesOf n C (maximalCores G C)).card + (maximalCores G C).card + T'.card := by
  apply sparse_core_bound ao t ht hits
  have sub : ((deleted G C).erase exception).image leaf ⊆ ends (deleted G C) \ S := by
    intro x hx
    obtain ⟨e,he,rfl⟩ := mem_image.mp hx
    obtain ⟨m,ns⟩ := mem e he
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨e,mem_of_mem_erase he,Sym2.mem_toFinset.mpr m⟩,ns⟩
  have c := card_le_card sub
  rw [card_image_of_injOn inj,card_sdiff_of_subset active] at c
  have hm := card_le_card active
  by_cases em : exception ∈ deleted G C
  · have l := card_erase_of_mem em
    have pos := card_pos.mpr ⟨exception,em⟩
    omega
  · rw [erase_eq_of_notMem em] at c
    omega

/-- Exact residual matching criterion for the posted conclusion. Ends outside
the matching and double hits supply precisely the credits that a simple
charge for every missed edge would discard. -/
theorem core_matching_criterion (ao : IsAO2 n C) {L T T' : Finset (Fin n)}
    (p : Parts G L) (t : IsMinCover G T) (ht : IsMinCover (G.deleteEdges (deleted G C : Set _)) T') :
    ∃ f : T → Fin n, Function.Injective f ∧ (∀ u, G.Adj u.val (f u) ∧ f u ∉ T) ∧
    let M := maximalCores G C
    let U := conesOf n C M
    let D := deleted G C
    (D.card + T.card ≤ U.card + M.card + T'.card ↔
      ∀ K : Finset (Fin n), (G.deleteEdges (D : Set _)).IsVertexCover (K : Set _) →
        D.card + (missed f K).card ≤ (raw n C U).card + repeated C U +
          (twice f K).card + (offMatching f K).card) := by
  obtain ⟨f,inj,hf⟩ := partners_exist p t
  refine ⟨f,inj,hf,?_⟩
  dsimp only
  rw [maximal_core_wires n G C ao]
  exact matched_budget_iff ht f inj (fun u => (hf u).2) _ _

end PEqualNP.Research.ConeWires
