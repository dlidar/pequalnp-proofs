import Mathlib
namespace PEqualNP.Research.CubicReaderCycles
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem surviving_edges (S : Finset V) (d : ℕ) (deg : ∀ v∉S,G.degree v ≤ d) :
    G.edgeFinset.card ≤ (G.induce (S : Set V)).edgeFinset.card + Sᶜ.card * d := by
  classical
  let E := G.edgeFinset.filter (fun e => e.toFinset ⊆ S)
  have incl : G.edgeFinset ⊆ E ∪ Sᶜ.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    by_cases h : e.toFinset ⊆ S
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · obtain ⟨v,hv,hs⟩ := Finset.not_subset.mp h
      exact mem_union_right _ (mem_biUnion.mpr ⟨v,mem_compl.mpr hs,G.mem_incidenceFinset.mpr ⟨G.mem_edgeFinset.mp he,by simpa using hv⟩⟩)
  have hsum : (∑ v ∈ Sᶜ,(G.incidenceFinset v).card) ≤ Sᶜ.card*d := calc
    _ ≤ ∑ _v ∈ Sᶜ,d := sum_le_sum (fun v hv => by simpa using deg v (mem_compl.mp hv))
    _ = _ := by simp
  have h := (card_le_card incl).trans (card_union_le ..)
  have h' := (card_biUnion_le (s:=Sᶜ) (t:=fun v => G.incidenceFinset v)).trans hsum
  have he : E.card = _ := G.card_filter_edgeFinset_toFinset_subset S
  omega

theorem cubic_degree_sum (deg : ∀ v,G.degree v = 3) :
    2*G.edgeFinset.card = 3*Fintype.card V := by
  rw [← G.sum_degrees_eq_twice_card_edges]; simp [deg,Nat.mul_comm]

theorem cycle_after_deletions [Nonempty V] (deg : ∀ v,G.degree v = 3)
    (S : Finset V) (small : 4*Sᶜ.card ≤ Fintype.card V) :
    ∃ v : S, ∃ p : (G.induce (S : Set V)).Walk v v,p.IsCycle := by
  classical
  have h := surviving_edges G S 3 (fun v _ => (deg v).le)
  have hh := cubic_degree_sum G deg
  have eq := Finset.card_compl_add_card S
  have pos := Fintype.card_pos (α:=V)
  have hp : 0<S.card := by omega
  haveI : Nonempty ↥S := (card_pos.mp hp).to_subtype
  apply SimpleGraph.exists_isCycle_of_card_le
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Set.ncard_eq_toFinset_card']
  change S.card ≤ (G.induce (S : Set V)).edgeFinset.card
  omega

theorem high_reader_count (r : V → ℕ) (two : ∀ v,2 ≤ r v)
    (budget : 7*(∑ v,r v) ≤ 15*Fintype.card V) :
    7*(univ.filter (fun v => 3 ≤ r v)).card ≤ Fintype.card V := by
  have h : (∑ v : V, ((2 : Nat) + if 3 ≤ r v then 1 else 0)) ≤ ∑ v,r v := by
    apply sum_le_sum;intro v _;have := two v;split <;> omega
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,← card_filter] at h
  norm_cast at h
  omega

theorem two_reader_cycle [Nonempty V] (deg : ∀ v,G.degree v=3) (r : V → ℕ)
    (two : ∀ v,2 ≤ r v) (budget : 7*(∑ v,r v) ≤ 15*Fintype.card V) :
    let S := univ.filter (fun v => r v = 2)
    ∃ v : S, ∃ p : (G.induce (S : Set V)).Walk v v,p.IsCycle := by
  classical
  let S := univ.filter (fun v => r v = 2)
  have eq : Sᶜ = univ.filter (fun v => 3 ≤ r v) := by ext v;simp [S];have := two v;omega
  apply cycle_after_deletions G deg S
  rw [eq];have := high_reader_count r two budget;omega

end PEqualNP.Research.CubicReaderCycles
