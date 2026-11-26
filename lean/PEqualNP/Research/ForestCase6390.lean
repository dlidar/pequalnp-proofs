import PEqualNP.Outside.L_meta_659
/-!
The forest case of L-meta-6390. The graph lower bound is the zero-extra-output,
empty-marked-set instance of the upstream forest theorem L-meta-659. The remaining
lemmas transport its edge count, truth function and vertex cover to the posted
bipartite representation.
-/
namespace PEqualNP.Research.ForestCase6390
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset
variable {p l : ℕ}

theorem different (a : Fin p) (b : Fin l) : Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have e := congrArg Fin.val h
  change a.val = p + b.val at e
  omega

def label : (Fin p × Fin l) ↪ Sym2 (Fin (p+l)) where
  toFun e := s(Fin.castAdd l e.1,Fin.natAdd p e.2)
  inj' := by
    intro a b h
    rcases Sym2.eq_iff.mp h with h|h
    · exact Prod.ext (Fin.castAdd_inj.mp h.1) ((Fin.natAddEmb p).injective h.2)
    · exact False.elim (different _ _ h.1)

def graph (E : Finset (Fin p × Fin l)) : SimpleGraph (Fin (p+l)) :=
  SimpleGraph.fromEdgeSet (↑(E.map label))

theorem graph_edges (E : Finset (Fin p × Fin l)) : (graph E).edgeSet = ↑(E.map label) := by
  rw [graph,SimpleGraph.edgeSet_fromEdgeSet]
  ext q
  refine ⟨fun h => h.1,fun h => ⟨h,?_⟩⟩
  obtain ⟨e,_,rfl⟩ := Finset.mem_map.mp h
  intro diag
  exact different e.1 e.2 (Sym2.mk_isDiag_iff.mp diag)

theorem edge_count (E : Finset (Fin p × Fin l)) : (graph E).edgeSet.ncard = E.card := by
  rw [graph_edges,Set.ncard_coe_finset,Finset.card_map]

theorem edge_on (E : Finset (Fin p × Fin l)) (x : Fin (p+l) → Bool) :
    (∃ e ∈ E, x (Fin.castAdd l e.1) = true ∧ x (Fin.natAdd p e.2) = true) ↔
      ∃ a b, (graph E).Adj a b ∧ x a = true ∧ x b = true := by
  constructor
  · rintro ⟨e,he,ha,hb⟩
    refine ⟨_,_,?_,ha,hb⟩
    change s(Fin.castAdd l e.1,Fin.natAdd p e.2) ∈ (graph E).edgeSet
    rw [graph_edges]
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩
  · rintro ⟨a,b,ab,ha,hb⟩
    change s(a,b) ∈ (graph E).edgeSet at ab
    rw [graph_edges] at ab
    obtain ⟨e,he,eq⟩ := Finset.mem_map.mp ab
    refine ⟨e,he,?_⟩
    rcases Sym2.eq_iff.mp eq with h|h
    · exact ⟨(congrArg x h.1).trans ha,(congrArg x h.2).trans hb⟩
    · exact ⟨(congrArg x h.1).trans hb,(congrArg x h.2).trans ha⟩

theorem forest_graph_bound {n s : ℕ} (G : SimpleGraph (Fin n))
    (acyclic : ∀ v (c : G.Walk v v), ¬ c.IsCycle)
    (hEdge : ∃ a b, G.Adj a b) (C : Circuit) (hfan : FanInTwo C)
    (size : C.size ≤ s)
    (computes : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeSet.ncard + T.card ≤ s+1 := by
  classical
  have h := PEqualNP.Outside.L_meta_659 n 0 s G ∅ (fun j => Fin.elim0 j) acyclic
      (by simp) (Or.inr hEdge) (fun j => Fin.elim0 j)
      (by rintro i j _ _ ⟨k,_⟩; exact Fin.elim0 k)
  obtain ⟨T,t,cover,price,_⟩ := h.mp (by
    refine ⟨C,hfan,size,C.output,Fin.elim0,fun x => ⟨?_,fun j => Fin.elim0 j⟩⟩
    simpa [Circuit.eval] using computes x)
  have price' : G.edgeSet.ncard + T.card + t ≤ s+1 := by simpa using price
  exact ⟨T,cover,by omega⟩

theorem split_cover (E : Finset (Fin p × Fin l)) (T : Finset (Fin (p+l)))
    (cover : ∀ u v, (graph E).Adj u v → u ∈ T ∨ v ∈ T) :
    ∃ (P : Finset (Fin p)) (L : Finset (Fin l)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧ P.card+L.card ≤ T.card := by
  let P := univ.filter fun i : Fin p => Fin.castAdd l i ∈ T
  let L := univ.filter fun j : Fin l => Fin.natAdd p j ∈ T
  refine ⟨P,L,?_,?_⟩
  · intro e he
    have adj : (graph E).Adj (Fin.castAdd l e.1) (Fin.natAdd p e.2) := by
      change label e ∈ (graph E).edgeSet
      rw [graph_edges]
      exact mem_map.mpr ⟨_,he,rfl⟩
    simpa [P,L] using cover _ _ adj
  · let X := P.map (Fin.castAddEmb l)
    let Y := L.map (Fin.natAddEmb p)
    have dis : Disjoint X Y := by
      apply disjoint_left.mpr
      intro q hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact different a b eq.symm
    have sub : X ∪ Y ⊆ T := by
      intro q h
      rcases mem_union.mp h with h|h
      · obtain ⟨a,ha,rfl⟩ := mem_map.mp h
        exact (mem_filter.mp ha).2
      · obtain ⟨b,hb,rfl⟩ := mem_map.mp h
        exact (mem_filter.mp hb).2
    simpa [card_union_of_disjoint dis,X,Y] using card_le_card sub

theorem forest_case (E : Finset (Fin p × Fin l)) (C : Circuit)
    (acyclic : ∀ v (c : (graph E).Walk v v), ¬ c.IsCycle) (fan : FanInTwo C)
    (computes : ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x =
      decide (∃ e ∈ E, x (Fin.castAdd l e.1) = true ∧ x (Fin.natAdd p e.2) = true)) :
    ∃ (P : Finset (Fin p)) (L : Finset (Fin l)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧
      E.card + P.card + L.card ≤ C.size+1 := by
  classical
  by_cases emp : E = ∅
  · subst E; exact ⟨∅,∅,by simp⟩
  obtain ⟨e,he⟩ := nonempty_iff_ne_empty.mpr emp
  have hn := (edge_on E (fun _ => true)).mp ⟨e,he,rfl,rfl⟩
  obtain ⟨a,b,ab,_⟩ := hn
  obtain ⟨T,hT,cost⟩ := forest_graph_bound (graph E) acyclic ⟨a,b,ab⟩ C fan (le_refl _) (by
    intro x
    change (circuitFun _ C x = true) ↔ _
    rw [computes,decide_eq_true_eq]
    exact edge_on E x)
  obtain ⟨P,L,cover,h⟩ := split_cover E T hT
  rw [edge_count] at cost
  exact ⟨P,L,cover,by omega⟩
theorem forest_case_ao2 (E : Finset (Fin p × Fin l)) (C : Circuit)
    (acyclic : ∀ v (c : (graph E).Walk v v), ¬ c.IsCycle) (ao : PEqualNP.TopForm.IsAO2 (p+l) C)
    (computes : ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x =
      decide (∃ e ∈ E, x (Fin.castAdd l e.1) = true ∧ x (Fin.natAdd p e.2) = true)) :
    ∃ (P : Finset (Fin p)) (L : Finset (Fin l)), (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧
      E.card + P.card + L.card ≤ C.size+1 := by
  apply forest_case E C acyclic _ computes
  intro g hg
  refine ⟨?_, (ao.2.2 g hg).le⟩
  rcases ao.1 g hg with hor | hand
  · simp [hor]
  · simp [hand]

theorem cycle_of_counterexample (E : Finset (Fin p × Fin l)) (C : Circuit)
    (ao : PEqualNP.TopForm.IsAO2 (p+l) C)
    (computes : ∀ x : Fin (p+l) → Bool, circuitFun (p+l) C x =
      decide (∃ e ∈ E, x (Fin.castAdd l e.1) = true ∧ x (Fin.natAdd p e.2) = true))
    (failure : ¬ ∃ (P : Finset (Fin p)) (L : Finset (Fin l)),
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) ∧ E.card + P.card + L.card ≤ C.size+1) :
    ∃ (v : Fin (p+l)) (c : (graph E).Walk v v), c.IsCycle := by
  by_contra noCycle
  exact failure (forest_case_ao2 E C (fun v c hc => noCycle ⟨v,c,hc⟩) ao computes)
end PEqualNP.Research.ForestCase6390
