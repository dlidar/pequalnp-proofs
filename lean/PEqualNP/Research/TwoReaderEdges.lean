import PEqualNP.Research.MarkedReaderCycles
import PEqualNP.Research.StarDeficit

namespace PEqualNP.Research.TwoReaderEdges
open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ReaderBudget PEqualNP.Research.MarkedReaderCycles
open PEqualNP.MetaComplexity.NestedCover
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edges having an endpoint adjacent to a chosen vertex. Includes its incident edges. -/
def nearEdges (v : V) := (G.neighborFinset v).biUnion (fun u => G.incidenceFinset u)
theorem near_bound (v : V) (d : Nat) (hv : G.degree v≤d)
    (hn : ∀ u,G.Adj v u → G.degree u≤d) : (nearEdges G v).card ≤ d*d := by
  apply (card_biUnion_le ..).trans
  calc
    _ ≤ ∑ _u ∈ G.neighborFinset v,d := by
      apply sum_le_sum;intro u hu;rw [G.card_incidenceFinset_eq_degree];exact hn u ((G.mem_neighborFinset v u).mp hu)
    _ ≤ _ := by simpa [G.card_neighborFinset_eq_degree] using Nat.mul_le_mul_right d hv

def cleanEdges (B : Finset V) := G.edgeFinset \ B.biUnion (nearEdges G)
theorem clean_count (B : Finset V) (d : Nat)
    (deg : ∀ v∈B,G.degree v≤d) (nbr : ∀ v∈B,∀ u,G.Adj v u → G.degree u≤d) :
    G.edgeFinset.card ≤ (cleanEdges G B).card + B.card*(d*d) := by
  classical
  have h : G.edgeFinset ⊆ cleanEdges G B ∪ B.biUnion (nearEdges G) := by
    intro e he;by_cases h : e∈B.biUnion (nearEdges G)
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨he,h⟩)
  have q := (card_le_card h).trans (card_union_le ..)
  have b : (B.biUnion (nearEdges G)).card ≤ B.card*(d*d) := calc
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _v ∈ B,d*d := sum_le_sum (fun v hv => near_bound G v d (deg v hv) (nbr v hv))
    _ = _ := by simp
  omega

theorem clean_property {B : Finset V} {v w : V} (good : s(v,w)∈cleanEdges G B) :
    G.Adj v w ∧ v∉B ∧ w∉B ∧ (∀ t,G.Adj t v → t∉B) ∧ (∀ t,G.Adj t w → t∉B) := by
  have mem := mem_sdiff.mp good
  have adj : G.Adj v w := G.mem_edgeFinset.mp mem.1
  have avoid (t u : V) (adj' : G.Adj t u) (h : u ∈ s(v,w)) : t∉B := by
    intro ht
    exact mem.2 (mem_biUnion.mpr ⟨t,ht,mem_biUnion.mpr ⟨u,(G.mem_neighborFinset t u).mpr adj',
      G.mem_incidenceFinset.mpr ⟨adj,h⟩⟩⟩)
  exact ⟨adj,avoid v w adj (by simp),avoid w v adj.symm (by simp),
    fun t a => avoid t v a (by simp),fun t a => avoid t w a (by simp)⟩

/-- Every gate saved below the best star cover removes one unit from the
three-reader budget and guarantees nine additional clean edges. -/
theorem star_savings_force_clean_edges {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hm : IsMinimalCircuit n C)
    (spec : circuitFun n C=graphFun G A) (deg : ∀ v∉A,G.degree v=3)
    (girth : ∀ v (p : G.Walk v v),p.IsCycle → 7≤p.length)
    (ends : ∀ i j,G.Adj i j → i∉A) (he : ∃ i j,G.Adj i j)
    (two : ∀ v∉A,2≤readers C.gates v.val) :
    let B := Aᶜ.filter (fun v => 3≤readers C.gates v.val)
    let saved := StarDeficit.score G A.card - (C.size+1)
    7*(B.card+saved) ≤ Aᶜ.card ∧
      3*Aᶜ.card+126*saved ≤ 14*(cleanEdges G B).card := by
  classical
  let B := Aᶜ.filter (fun v => 3≤readers C.gates v.val)
  let saved := StarDeficit.score G A.card - (C.size+1)
  obtain ⟨T,covT,cheap⟩ := CubicCover4697.nine_fourteenths G Aᶜ
    (fun v hv => (deg v (mem_compl.mp hv)).le) (fun i j e => mem_compl.mpr (ends i j e)) girth
  have best := StarDeficit.optimal (G:=G) (T:=T) covT
  obtain ⟨D,covD,optD⟩ := StarDeficit.attain G
  have hs := CubicCircuitCycles.size_from_cover G A D C hm he spec covD
  rw [optD] at hs
  have slots := MinimumReaderBudget.minimum_raw_budget C hm
  rw [← Fin.sum_univ_eq_sum_range (fun i => readers C.gates i)] at slots
  have hmark : A.card ≤ ∑ v ∈ A,readers C.gates v.val := by
    calc
      _ = ∑ _v ∈ A,1 := by simp
      _ ≤ _ := sum_le_sum (fun v hv => marked_read G A C hm.1 spec ends he v hv)
  have sumR := sum_add_sum_compl A (fun v => readers C.gates v.val)
  have h : (∑ v ∈ Aᶜ, ((2 : Nat) + if 3≤readers C.gates v.val then 1 else 0)) ≤
      ∑ v∈Aᶜ,readers C.gates v.val := by
    apply sum_le_sum;intro v hv;have := two v (mem_compl.mp hv);split <;> omega
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← card_filter] at h
  norm_cast at h
  change Aᶜ.card*2+B.card ≤ _ at h
  have q := clean_count G B 3 (fun v hv => (deg v (mem_compl.mp (mem_filter.mp hv).1)).le)
    (fun v _ u e => (deg u (ends u v e.symm)).le)
  have marks : (∑ v ∈ A,G.degree v)=0 := by
    apply sum_eq_zero;intro v hv;rw [degree_eq_zero_iff_notMem_support]
    rintro ⟨j,edge⟩;exact ends v j edge hv
  have active : (∑ v ∈ Aᶜ,G.degree v)=3*Aᶜ.card := by
    calc
      _ = ∑ _v ∈ Aᶜ,3 := sum_congr rfl (fun v hv => deg v (mem_compl.mp hv))
      _ = _ := by simp [Nat.mul_comm]
  have sumD := sum_add_sum_compl A (fun v => G.degree v)
  rw [marks,active,G.sum_degrees_eq_twice_card_edges] at sumD
  have high : 7*(B.card+saved) ≤ Aᶜ.card := by dsimp only [saved,StarDeficit.score];omega
  change 7*(B.card+saved) ≤ Aᶜ.card ∧ 3*Aᶜ.card+126*saved ≤ 14*(cleanEdges G B).card
  exact ⟨high,by omega⟩

end PEqualNP.Research.TwoReaderEdges
