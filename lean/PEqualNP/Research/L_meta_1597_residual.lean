import PEqualNP.Defs.TopForm

namespace PEqualNP.Research.G11Residual
open Finset PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds

abbrev V := Fin 11
def G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)
def edges : List (V × V) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
def miss (K : Finset V) := edges.filter fun e => e.1 ∉ K ∧ e.2 ∉ K
def symEdge (e : V × V) : Sym2 V := s(e.1,e.2)
def omitted (K : Finset V) := ((miss K).map symEdge).toFinset

theorem valid : ∀ e ∈ edges, G.Adj e.1 e.2 := by decide +kernel
theorem injective_on_edges : ∀ e ∈ edges, ∀ f ∈ edges, symEdge e = symEdge f → e = f := by decide +kernel
theorem noDuplicates : edges.Nodup := by decide +kernel

theorem omitted_card (K : Finset V) : (omitted K).card = (miss K).length := by
  rw [omitted,List.toFinset_card_of_nodup,List.length_map]
  apply List.Nodup.map_on
  · intro e he f hf h
    exact injective_on_edges e (List.mem_filter.mp he).1 f (List.mem_filter.mp hf).1 h
  · exact noDuplicates.filter _

theorem omitted_subset (K : Finset V) (U : Finset (Sym2 V))
    (h : (G.deleteEdges ↑U).IsVertexCover (↑K)) : omitted K ⊆ U := by
  intro z hz
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  have hm := List.mem_filter.mp hab
  by_contra out
  have adj : (G.deleteEdges ↑U).Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨valid _ hm.1,out⟩
  have hv := h adj
  simp at hm
  rcases hv with ha|hb
  · exact hm.2.1 ha
  · exact hm.2.2 hb

def price (k : ℕ) : ℕ := [16,12,8,5,3,2,1].getD k 0
def critical : List (Finset V) := [{3,8,9,10}, {5,7,8,10}, {6,8,9,10}, {7,8,9,10}]

def good (K : Finset V) : Bool := decide (price K.card ≤ (miss K).length ∧
    (K.card ≤ 4 → (miss K).length ≤ 3 → K ∈ critical))
def vertices := List.finRange 11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem table : ∀ K ∈ (univ : Finset V).powerset,
    price K.card ≤ (miss K).length ∧ (K.card ≤ 4 → (miss K).length ≤ 3 → K ∈ critical) := by
  intro K _
  let xs := vertices.filter (fun v => decide (v ∈ K))
  have sub : xs ∈ vertices.sublists := List.mem_sublists.mpr (List.filter_sublist)
  have eq : xs.toFinset = K := by ext v; simp [xs,vertices]
  have cert : vertices.sublists.all (fun t => good t.toFinset) = true := by decide +kernel
  have h := List.all_eq_true.mp cert xs sub
  simpa only [eq,good,decide_eq_true_eq] using h

theorem deletion_price (K : Finset V) (U : Finset (Sym2 V))
    (h : (G.deleteEdges ↑U).IsVertexCover (↑K)) : price K.card ≤ U.card := by
  have ht := (table K (mem_powerset.mpr (subset_univ _))).1
  rw [← omitted_card] at ht
  exact ht.trans (card_le_card (omitted_subset K U h))

theorem critical_triples (K : Finset V) (U : Finset (Sym2 V))
    (cover : (G.deleteEdges ↑U).IsVertexCover (↑K)) (k : K.card ≤ 4) (u : U.card ≤ 3) :
    K ∈ critical ∧ U = omitted K ∧ s((1 : V),(4 : V)) ∈ U := by
  have sub := omitted_subset K U cover
  have n := card_le_card sub
  rw [omitted_card] at n
  have crit := (table K (mem_powerset.mpr (subset_univ _))).2 k (n.trans u)
  have cert : ∀ S ∈ critical, (miss S).length = 3 ∧ s((1 : V),(4 : V)) ∈ omitted S := by decide +kernel
  obtain ⟨three,edge⟩ := cert K crit
  exact ⟨crit,(eq_of_subset_of_card_le sub (by rwa [omitted_card,three])).symm,sub edge⟩

theorem orientation : ∀ a b : V, G.Adj a b → (a,b) ∈ edges ∨ (b,a) ∈ edges := by decide +kernel

theorem cover_after_omitting (K : Finset V) : (G.deleteEdges ↑(omitted K)).IsVertexCover (↑K) := by
  intro a b adj
  obtain ⟨hab,kept⟩ := SimpleGraph.deleteEdges_adj.mp adj
  by_contra h
  push Not at h
  apply kept
  change s(a,b) ∈ ((miss K).map symEdge).toFinset
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  rcases orientation a b hab with ab|ba
  · exact ⟨(a,b),List.mem_filter.mpr ⟨ab, by simpa using h⟩,rfl⟩
  · exact ⟨(b,a),List.mem_filter.mpr ⟨ba, by simpa using And.intro h.2 h.1⟩,Sym2.eq_swap⟩

def witnesses : List (Finset V) := [∅, {8}, {8,10}, {7,8,10}, {3,8,9,10}, {0,5,7,8,10}, {0,1,5,7,8,10}, {0,1,3,5,7,8,10}, {0,1,2,3,4,5,6,9}, {0,1,2,3,4,5,6,7,8}, {0,1,2,3,4,5,6,7,8,9}, {0,1,2,3,4,5,6,7,8,9,10}]
theorem sharp (k : Fin 12) : ∃ K : Finset V, ∃ U : Finset (Sym2 V), K.card = k.val ∧
    U.card = price k.val ∧ (G.deleteEdges ↑U).IsVertexCover (↑K) := by
  have cert : ∀ j : Fin 12, (witnesses.getD j.val ∅).card = j.val ∧
      (miss (witnesses.getD j.val ∅)).length = price j.val := by decide +kernel
  obtain ⟨hk,hu⟩ := cert k
  exact ⟨_,_,hk,(omitted_card _).trans hu,cover_after_omitting _⟩

def budget (D : Circuit) := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
def centers (D : Circuit) := (tops G D \ centreless G D).card

/-- Apply the counting and cover conclusions from the posted hypotheses to a short circuit. -/
theorem short_obstruction (D : Circuit) (U : Finset (Sym2 V)) (size : D.size ≤ 21)
    (acc : 16 + centers D + budget D ≤ D.size + U.card + 1)
    (covers : ∀ K : Finset V, IsMinCover (G.deleteEdges ↑U) K → K.card ≤ centers D)
    (small : U.card ≤ 3) (cost : 5 ≤ budget D) :
    D.size = 21 ∧ budget D = 5 ∧ centers D = 4 ∧ U.card = 3 ∧
    ∃ K ∈ critical, IsMinCover (G.deleteEdges ↑U) K ∧ U = omitted K ∧ s((1 : V),(4 : V)) ∈ U := by
  classical
  let H := G.deleteEdges (↑U)
  let P (m : ℕ) := ∃ K : Finset V, H.IsVertexCover (↑K) ∧ K.card = m
  have ex : ∃ m, P m := ⟨_,univ,by simp [H],rfl⟩
  obtain ⟨K,hK,hc⟩ := Nat.find_spec ex
  have hmin : IsMinCover H K := ⟨hK,fun T ht => hc.trans_le (Nat.find_min' ex ⟨T,ht,rfl⟩)⟩
  have kt := covers K hmin
  obtain ⟨crit,equ,edge⟩ := critical_triples K U hK (by omega) small
  have cert : ∀ S ∈ critical, S.card = 4 := by decide +kernel
  have := cert K crit
  exact ⟨by omega,by omega,by omega,by omega,K,crit,hmin,equ,edge⟩

def separated (e f : V × V) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2
instance (e f : V × V) : Decidable (separated e f) := by unfold separated; infer_instance

theorem critical_matching : ∀ K ∈ critical, ∀ e ∈ miss K, ∀ f ∈ miss K,
    e ≠ f → separated e f := by decide +kernel

/-- Any routing through two junk gates must assign two disjoint positive pairs to one gate. -/
theorem shared_junk (D : Circuit) (K : Finset V) (crit : K ∈ critical)
    (two : (junk G D).card ≤ 2)
    (routed : ∀ e ∈ miss K, ∃ j ∈ junk G D, gateVal 11 D j (pairInput e.1 e.2) = true) :
    ∃ j ∈ junk G D, ∃ e ∈ miss K, ∃ f ∈ miss K, separated e f ∧
      gateVal 11 D j (pairInput e.1 e.2) = true ∧ gateVal 11 D j (pairInput f.1 f.2) = true := by
  classical
  let S := (miss K).toFinset
  have rho (e : V × V) : ∃ j, e ∈ S → j ∈ junk G D ∧ gateVal 11 D j (pairInput e.1 e.2) = true := by
    by_cases h : e ∈ S
    · obtain ⟨j,hj,yes⟩ := routed e (List.mem_toFinset.mp h)
      exact ⟨j,fun _ => ⟨hj,yes⟩⟩
    · exact ⟨0,fun he => (h he).elim⟩
  choose r hr using rho
  have cert : ∀ X ∈ critical, (miss X).toFinset.card = 3 := by decide +kernel
  have three : S.card = 3 := cert K crit
  obtain ⟨e,he,f,hf,ne,eq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (show (junk G D).card < S.card by omega) (fun e he => (hr e he).1)
  have em := List.mem_toFinset.mp he
  have fm := List.mem_toFinset.mp hf
  exact ⟨r e,(hr e he).1,e,em,f,fm,critical_matching K crit e em f fm ne,(hr e he).2,eq.symm ▸ (hr f hf).2⟩

end PEqualNP.Research.G11Residual
