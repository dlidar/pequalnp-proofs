import PEqualNP.Research.BipartitePinning
namespace PEqualNP.Research.BipartiteOptimum
open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ReaderBudget PEqualNP.Research.MinimumReaderBudget PEqualNP.Research.BipartitePinning
open PEqualNP.Research.MarkedReaderCycles PEqualNP.MetaComplexity.NestedCover
theorem bipartite_optimum {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A X : Finset (Fin n)) (C : Circuit)
    (hm : IsMinimalCircuit n C) (spec : circuitFun n C=graphFun G A)
    (deg : ∀ v∉A,G.degree v=3) (hend : ∀ i j,G.Adj i j → i∉A)
    (hedge : ∃ i j,G.Adj i j) (color : ∀ i j,G.Adj i j → (i∈X ↔ j∉X))
    (two : ∀ v∉A,2≤readers C.gates v.val) :
    C.size+1=A.card+2*Aᶜ.card ∧ ∀ v, readers C.gates v.val = (if v∈A then 1 else 2) := by
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
  have cap := CubicCircuitCycles.size_from_cover G A T C hm hedge spec hcover
  have total : C.size+1 = A.card+2*Aᶜ.card := by omega
  refine ⟨total,?_⟩
  let base (v : Fin n) : Nat := if v∈A then 1 else 2
  have base_le (v) : base v ≤ readers C.gates v.val := by
    dsimp [base];split
    · exact marked_read G A C hm.1 spec hend hedge v ‹_›
    · exact two v ‹_›
  have bA : (∑ v ∈ A,base v)=A.card := by
    calc
      _ = ∑ _v ∈ A,1 := sum_congr rfl (fun v hv => by simp [base,hv])
      _ = _ := by simp
  have bU : (∑ v ∈ Aᶜ,base v)=2*Aᶜ.card := by
    calc
      _ = ∑ _v ∈ Aᶜ,2 := sum_congr rfl (fun v hv => by simp [base,mem_compl.mp hv])
      _ = _ := by simp [Nat.mul_comm]
  have bsum := sum_add_sum_compl A base
  rw [bA,bU] at bsum
  intro v
  change readers C.gates v.val=base v
  by_contra ne
  have strict := sum_lt_sum (s:=univ) (f:=base) (g:=fun w : Fin n => readers C.gates w.val)
    (fun w _ => base_le w) ⟨v,mem_univ _,lt_of_le_of_ne (base_le v) (Ne.symm ne)⟩
  omega
end PEqualNP.Research.BipartiteOptimum
