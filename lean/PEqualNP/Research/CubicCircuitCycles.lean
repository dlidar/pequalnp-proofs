import PEqualNP.Research.MinimumReaderBudget
import PEqualNP.Research.CubicReaderCycles
import PEqualNP.Research.Cubic4697.BeyondTwoThirds
import PEqualNP.Outside.L_meta_198

namespace PEqualNP.Research.CubicCircuitCycles
open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ReaderBudget PEqualNP.Research.MinimumReaderBudget
open PEqualNP.Research.CubicReaderCycles
open PEqualNP.MetaComplexity.NestedCover

theorem size_from_cover {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T : Finset (Fin n)) (C : Circuit) (hm : IsMinimalCircuit n C)
    (he : ∃ i j,G.Adj i j) (spec : circuitFun n C = graphFun G A)
    (cov : ∀ i j,G.Adj i j → i∈T ∨ j∈T) :
    C.size+1 ≤ A.card + G.edgeFinset.card + T.card := by
  classical
  obtain ⟨i,j,ij⟩ := he
  have pos : 0 < G.edgeFinset.card := card_pos.mpr ⟨s(i,j),G.mem_edgeFinset.mpr ij⟩
  obtain ⟨D,fan,sz,ev⟩ := PEqualNP.Outside.L_meta_198 n G A T
    (A.card+G.edgeFinset.card+T.card-1) (Or.inr ⟨i,j,ij⟩) cov (by omega)
  have le := hm.2 D fan (by
    rw [spec]; funext x
    simpa [circuitFun,graphFun] using ev x)
  omega

theorem cubic_reader_budget {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalCircuit n C) (spec : circuitFun n C = graphFun G ∅)
    (he : ∃ i j,G.Adj i j) (deg : ∀ v,G.degree v=3)
    (girth : ∀ v (p : G.Walk v v),p.IsCycle → 7≤p.length) :
    7*(∑ v : Fin n,readers C.gates v.val) ≤ 15*n := by
  obtain ⟨T,cov,hT⟩ := PEqualNP.Research.CubicCover4697.nine_fourteenths G univ
    (fun v _ => (deg v).le) (fun _ _ _ => mem_univ _) girth
  have hs := size_from_cover G ∅ T C hm he spec cov
  have slots := minimum_raw_budget C hm
  have edges := cubic_degree_sum G deg
  simp only [card_empty,zero_add] at hs
  simp only [card_univ,Fintype.card_fin] at hT edges
  rw [Fin.sum_univ_eq_sum_range]
  omega

theorem robust_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (deg : ∀ v,G.degree v=3)
    (r : V → Nat) (two : ∀ v,2≤r v) (budget : 7*(∑ v,r v)≤15*Fintype.card V)
    (B : Finset V) (small : 28*B.card ≤ 3*Fintype.card V) :
    let S := (univ.filter (fun v => r v=2)) \ B
    ∃ v : S, ∃ p : (G.induce (S : Set V)).Walk v v,p.IsCycle := by
  classical
  let S := (univ.filter (fun v => r v=2)) \ B
  apply cycle_after_deletions G deg S
  have sub : Sᶜ ⊆ (univ.filter (fun v => 3≤r v)) ∪ B := by
    intro v hv; by_cases hb : v∈B
    · exact mem_union_right _ hb
    · apply mem_union_left _; apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      have ne : r v ≠ 2 := fun h => (mem_compl.mp hv) (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,h⟩,hb⟩)
      have := two v;omega
  have h := (card_le_card sub).trans (card_union_le ..)
  have := high_reader_count r two budget
  omega

theorem unavoidable_reader_cycle {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : IsMinimalCircuit n C) (spec : circuitFun n C = graphFun G ∅)
    (he : ∃ i j,G.Adj i j) (deg : ∀ v,G.degree v=3)
    (girth : ∀ v (p : G.Walk v v),p.IsCycle → 7≤p.length) :
    (∃ v : Fin n,readers C.gates v.val ≤ 1) ∨
    ∀ B : Finset (Fin n),28*B.card ≤ 3*n →
      let S := (univ.filter (fun v : Fin n => readers C.gates v.val=2)) \ B
      ∃ v : S, ∃ p : (G.induce (S : Set (Fin n))).Walk v v,p.IsCycle := by
  classical
  by_cases low : ∃ v : Fin n,readers C.gates v.val ≤ 1
  · exact Or.inl low
  · push_neg at low
    obtain ⟨i,j,hij⟩ := he
    haveI : Nonempty (Fin n) := ⟨i⟩
    right;intro B small
    apply robust_cycle G deg _ low _ B
    · simpa using small
    · simpa using cubic_reader_budget G C hm spec ⟨i,j,hij⟩ deg girth
end PEqualNP.Research.CubicCircuitCycles
