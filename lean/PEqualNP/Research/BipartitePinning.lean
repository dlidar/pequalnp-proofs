import PEqualNP.Research.MarkedReaderCycles
namespace PEqualNP.Research.BipartitePinning
open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ReaderBudget PEqualNP.Research.MinimumReaderBudget
open PEqualNP.Research.MarkedReaderCycles PEqualNP.MetaComplexity.NestedCover

theorem small_side {n : Nat} (G : SimpleGraph (Fin n)) (A X : Finset (Fin n))
    (ends : ∀ i j,G.Adj i j → i∉A)
    (color : ∀ i j,G.Adj i j → (i∈X ↔ j∉X)) :
    ∃ T : Finset (Fin n),2*T.card≤Aᶜ.card ∧ ∀ i j,G.Adj i j → i∈T ∨ j∈T := by
  classical
  let L := Aᶜ ∩ X
  let R := Aᶜ \ X
  have sum : L.card+R.card=Aᶜ.card := by
    rw [Nat.add_comm];exact card_sdiff_add_card_inter _ _
  have covers (i j : Fin n) (e : G.Adj i j) : (i∈L ∨ j∈L) ∧ (i∈R ∨ j∈R) := by
    have iU := mem_compl.mpr (ends i j e)
    have jU := mem_compl.mpr (ends j i e.symm)
    by_cases hx : i∈X
    · exact ⟨Or.inl (mem_inter.mpr ⟨iU,hx⟩),Or.inr (mem_sdiff.mpr ⟨jU,(color i j e).mp hx⟩)⟩
    · have hj : j∈X := by by_contra h; exact hx ((color i j e).mpr h)
      exact ⟨Or.inr (mem_inter.mpr ⟨jU,hj⟩),Or.inl (mem_sdiff.mpr ⟨iU,hx⟩)⟩
  by_cases h : L.card ≤ R.card
  · exact ⟨L,by omega,fun i j e => (covers i j e).1⟩
  · exact ⟨R,by omega,fun i j e => (covers i j e).2⟩

theorem bipartite_four_gate_pin {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A X : Finset (Fin n)) (C : Circuit)
    (hm : IsMinimalCircuit n C) (spec : circuitFun n C=graphFun G A)
    (deg : ∀ v∉A,G.degree v=3) (hend : ∀ i j,G.Adj i j → i∉A)
    (hedge : ∃ i j,G.Adj i j) (color : ∀ i j,G.Adj i j → (i∈X ↔ j∉X))
    (two : ∀ v∉A,2≤readers C.gates v.val) :
    ∃ v∉A,∃ s : Nat,s+4≤C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s := by
  classical
  obtain ⟨T,small,hcover⟩ := small_side G A X hend color
  have slots := minimum_raw_budget C hm
  rw [← Fin.sum_univ_eq_sum_range (fun i => readers C.gates i)] at slots
  have hmark : A.card ≤ ∑ v ∈ A,readers C.gates v.val := by
    calc
      _ = ∑ _v ∈ A,1 := by simp
      _ ≤ _ := sum_le_sum (fun v hv => marked_read G A C hm.1 spec hend hedge v hv)
  have hun : 2*Aᶜ.card ≤ ∑ v ∈ Aᶜ,readers C.gates v.val := by
    calc
      _ = ∑ _v ∈ Aᶜ,2 := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv => two v (mem_compl.mp hv))
  have sumR := sum_add_sum_compl A (fun v => readers C.gates v.val)
  have marks : (∑ v ∈ A,G.degree v)=0 := by
    apply sum_eq_zero;intro v hv;rw [degree_eq_zero_iff_notMem_support]
    rintro ⟨j,edge⟩;exact hend v j edge hv
  have active : (∑ v ∈ Aᶜ,G.degree v)=3*Aᶜ.card := by
    calc
      _ = ∑ _v ∈ Aᶜ,3 := sum_congr rfl (fun v hv => deg v (mem_compl.mp hv))
      _ = _ := by simp [Nat.mul_comm]
  have sumD := sum_add_sum_compl A (fun v => G.degree v)
  rw [marks,active,G.sum_degrees_eq_twice_card_edges] at sumD
  have hbudget : A.card+G.edgeFinset.card+T.card ≤ C.size+1 := by omega
  have hdeg (v) (hv : v∉A) := (G.ncard_neighborSet v).trans (deg v hv)
  let f := circuitFun n C
  have hspec (x) : f x=true ↔ (∃ a∈A,x a=true) ∨ ∃ i j,G.Adj i j ∧ x i=true ∧ x j=true := by
    simp [f,spec,graphFun]
  -- The final star construction and cofactor identity follow upstream R_meta_1745_3.
  obtain ⟨i,j,hij⟩ := hedge
  have marked_partner : ∃ v ∈ T, ∃ u, G.Adj u v := by
    rcases hcover i j hij with h | h
    · exact ⟨i,h,j,hij.symm⟩
    · exact ⟨j,h,i,hij⟩
  obtain ⟨v,hv,u,huv⟩ := marked_partner
  have hvA : v ∉ A := hend v u huv.symm
  let H := G.deleteIncidenceSet v
  let T' := T.erase v
  have keep : ∃ j, G.Adj u j ∧ j ≠ v := by
    by_contra! h
    have sub : G.neighborSet u ⊆ {v} := fun j hj =>
      Set.mem_singleton_iff.mpr (h j hj)
    have small := Set.ncard_le_ncard sub
    have deg := hdeg u (hend u v huv)
    rw [deg, Set.ncard_singleton] at small
    omega
  obtain ⟨j,huj,hjv⟩ := keep
  have kept : H.Adj u j := SimpleGraph.deleteIncidenceSet_adj.mpr ⟨huj,huv.ne,hjv⟩
  have no_empty : 0 < H.edgeFinset.card :=
    Finset.card_pos.mpr ⟨s(u,j), SimpleGraph.mem_edgeFinset.mpr kept⟩
  have cover' : ∀ a b : Fin n, H.Adj a b → a ∈ T' ∨ b ∈ T' := by
    intro a b hab
    obtain ⟨old, ha, hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
    exact (hcover a b old).imp (fun h => Finset.mem_erase.mpr ⟨ha,h⟩)
      (fun h => Finset.mem_erase.mpr ⟨hb,h⟩)
  have he : H.edgeFinset.card = G.edgeFinset.card - 3 := by
    have hd : G.degree v = 3 := (G.ncard_neighborSet v).symm.trans (hdeg v hvA)
    exact (G.card_edgeFinset_deleteIncidenceSet v).trans (by rw [hd])
  have ht : T'.card = T.card - 1 := Finset.card_erase_of_mem hv
  let s := A.card + H.edgeFinset.card + T'.card - 1
  have hs : s + 1 = A.card + H.edgeFinset.card + T'.card := by
    dsimp [s]
    omega
  have size : s + 4 ≤ C.size := by
    have htp := Finset.card_pos.mpr ⟨v,hv⟩
    omega
  have cut := PEqualNP.Outside.L_meta_198 n H A T' s (Or.inr ⟨u,j,kept⟩) cover' hs
  have eval_cut :
      (fun x : Fin n → Bool => decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true)) =
      (fun x : Fin n → Bool => f (Function.update x v false)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, hspec]
    constructor
    · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
      · have haz : a ≠ v := fun e => hvA (e ▸ ha)
        exact Or.inl ⟨a,ha, by simpa [Function.update_of_ne haz] using hxa⟩
      · obtain ⟨old,ha,hb⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hab
        exact Or.inr ⟨a,b,old,
          by simpa [Function.update_of_ne ha] using hxa,
          by simpa [Function.update_of_ne hb] using hxb⟩
    · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
      · have haz : a ≠ v := fun e => hvA (e ▸ ha)
        exact Or.inl ⟨a,ha, by simpa [Function.update_of_ne haz] using hxa⟩
      · have ha : a ≠ v := by intro e; simp [e] at hxa
        have hb : b ≠ v := by intro e; simp [e] at hxb
        exact Or.inr ⟨a,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab,ha,hb⟩,
          by simpa [Function.update_of_ne ha] using hxa,
          by simpa [Function.update_of_ne hb] using hxb⟩
  exact ⟨v,hvA,s,size,eval_cut ▸ cut⟩
end PEqualNP.Research.BipartitePinning
