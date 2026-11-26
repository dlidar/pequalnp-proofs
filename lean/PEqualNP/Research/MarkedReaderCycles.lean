import PEqualNP.Research.CubicCircuitCycles
namespace PEqualNP.Research.MarkedReaderCycles
open Finset SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.ReaderBudget PEqualNP.Research.MinimumReaderBudget
open PEqualNP.Research.CubicCircuitCycles PEqualNP.MetaComplexity.NestedCover
-- The list induction for unread wires is from upstream L_meta_3068.
theorem unread_agree (S : ℕ → Prop) (gs : List Gate)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, ¬ S i) :
    ∀ u v : List Bool, u.length = v.length →
      (∀ i, ¬ S i → u.getD i false = v.getD i false) →
      ∀ i, ¬ S i → (wiresFrom gs u).getD i false = (wiresFrom gs v).getD i false := by
  induction gs with
  | nil => intro u v _ h; exact h
  | cons g gs ih =>
    intro u v hl h i hi
    have same : g.op.eval (g.inputs.map fun a => u.getD a false) =
        g.op.eval (g.inputs.map fun a => v.getD a false) := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h a (avoid g List.mem_cons_self a ha)
    apply ih (fun g' hg' => avoid g' (List.mem_cons_of_mem _ hg'))
      (u ++ [g.op.eval (g.inputs.map fun a => u.getD a false)])
      (v ++ [g.op.eval (g.inputs.map fun a => v.getD a false)]) (by simp [hl]) _ i hi
    intro k hk
    by_cases hku : k < u.length
    · rw [List.getD_append _ _ _ _ hku, List.getD_append _ _ _ _ (by omega)]
      exact h k hk
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      rw [same, hl]

theorem unread_raw {n : Nat} (C : Circuit) (hf : FanInTwo C) (a : Fin n)
    (read : readers C.gates a.val = 0) (out : C.output ≠ a.val)
    (x y : Fin n → Bool) (agree : ∀ i,i≠a → x i=y i) : circuitFun n C x=circuitFun n C y := by
  have h := unread_agree (fun k => k=a.val) (C.gates.map trimmedGate) (by
    intro g hg k hk eq
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
    have pos := reads_positive ht (show a.val ∈ used t from eq ▸ hk)
    omega) (List.ofFn x) (List.ofFn y) (by simp) (by
      intro i hi
      by_cases lt : i<n
      · rw [List.getD_eq_getElem _ _ (by simpa using lt),List.getD_eq_getElem _ _ (by simpa using lt)]
        simp only [List.getElem_ofFn];exact agree _ (fun e => hi (congrArg Fin.val e))
      · simp [List.getD_eq_getElem?_getD,lt] ) C.output out
  change (wiresFrom C.gates _).getD _ _ = (wiresFrom C.gates _).getD _ _
  simpa only [trim_wires C.gates hf] using h

theorem marked_read {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (C : Circuit) (hf : FanInTwo C) (spec : circuitFun n C=graphFun G A)
    (ends : ∀ i j,G.Adj i j → i∉A) (he : ∃ i j,G.Adj i j) (a : Fin n) (ha : a∈A) :
    1≤readers C.gates a.val := by
  classical
  obtain ⟨i,j,ij⟩ := he
  have out : C.output ≠ a.val := by
    intro eq
    let x (k : Fin n) := decide (k=i ∨ k=j)
    have ev := congrFun spec x
    have yes : graphFun G A x = true := by
      simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
      exact Or.inr ⟨i,j,ij,by simp [x],by simp [x]⟩
    have raw : circuitFun n C x = x a := by
      change (wiresFrom C.gates (List.ofFn x)).getD C.output false = _
      rw [eq,getD_wiresFrom _ _ _ (by simpa using a.isLt),List.getD_eq_getElem _ _ (by simpa using a.isLt)]
      simp
    have ai : a≠i := fun e => ends i j ij (e ▸ ha)
    have aj : a≠j := fun e => ends j i ij.symm (e ▸ ha)
    change circuitFun n C x=graphFun G A x at ev
    rw [raw,yes] at ev
    simp [x,ai,aj] at ev
  by_contra! h
  have eq := unread_raw C hf a (by omega) out (fun i => decide (i=a)) (fun _ => false)
    (fun i hi => by simp [hi])
  rw [spec] at eq
  have yes : graphFun G A (fun i => decide (i=a))=true := by
    simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
    exact Or.inl ⟨a,ha,by simp⟩
  rw [yes] at eq
  simp [graphFun] at eq

theorem active_reader_budget {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hm : IsMinimalCircuit n C)
    (spec : circuitFun n C = graphFun G A) (deg : ∀ v∉A,G.degree v=3)
    (girth : ∀ v (p : G.Walk v v),p.IsCycle → 7≤p.length)
    (ends : ∀ i j,G.Adj i j → i∉A) (he : ∃ i j,G.Adj i j) :
    7*(∑ v ∈ Aᶜ,readers C.gates v.val) ≤ 15*Aᶜ.card := by
  classical
  obtain ⟨T,cov,hT⟩ := PEqualNP.Research.CubicCover4697.nine_fourteenths G Aᶜ
    (fun v hv => (deg v (mem_compl.mp hv)).le) (fun i j ij => mem_compl.mpr (ends i j ij)) girth
  have hs := size_from_cover G A T C hm he spec cov
  have slots := minimum_raw_budget C hm
  rw [← Fin.sum_univ_eq_sum_range (fun i => readers C.gates i)] at slots
  have hmark : A.card ≤ ∑ v ∈ A,readers C.gates v.val := by
    calc
      _ = ∑ _v ∈ A,1 := by simp
      _ ≤ _ := sum_le_sum (fun v hv => marked_read G A C hm.1 spec ends he v hv)
  have sumR := sum_add_sum_compl A (fun v => readers C.gates v.val)
  have zeroDeg (v) (hv : v∈A) : G.degree v=0 := by
    rw [degree_eq_zero_iff_notMem_support]
    rintro ⟨j,edge⟩;exact ends v j edge hv
  have marks : (∑ v ∈ A,G.degree v)=0 := sum_eq_zero zeroDeg
  have active : (∑ v ∈ Aᶜ,G.degree v)=3*Aᶜ.card := by
    calc
      _ = ∑ _v ∈ Aᶜ,3 := sum_congr rfl (fun v hv => deg v (mem_compl.mp hv))
      _ = _ := by simp [Nat.mul_comm]
  have sumD := sum_add_sum_compl A (fun v => G.degree v)
  rw [marks,active,G.sum_degrees_eq_twice_card_edges] at sumD
  omega

set_option maxHeartbeats 1600000 in
theorem marked_cycle {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (C : Circuit) (hm : IsMinimalCircuit n C)
    (spec : circuitFun n C = graphFun G A) (deg : ∀ v∉A,G.degree v=3)
    (girth : ∀ v (p : G.Walk v v),p.IsCycle → 7≤p.length)
    (ends : ∀ i j,G.Adj i j → i∉A) (he : ∃ i j,G.Adj i j) :
    let U := Aᶜ
    let H := G.induce (U : Set (Fin n))
    let r := fun v : U => readers C.gates v.val.val
    (∃ v : U,r v≤1) ∨ ∀ B : Finset U,28*B.card ≤ 3*U.card →
      let S := (univ.filter (fun v => r v=2)) \ B
      ∃ v : S, ∃ p : (H.induce (S : Set U)).Walk v v,p.IsCycle := by
  classical
  let U := Aᶜ
  let H := G.induce (U : Set (Fin n))
  let r := fun v : U => readers C.gates v.val.val
  by_cases low : ∃ v : U,r v≤1
  · exact Or.inl low
  · push Not at low
    obtain ⟨i,j,ij⟩ := he
    haveI : Nonempty U := ⟨⟨i,mem_compl.mpr (ends i j ij)⟩⟩
    letI : Fintype ↥(U : Set (Fin n)) := FinsetCoe.fintype U
    have degreeU (v : U) : H.degree v=3 := by
      have h := SimpleGraph.degree_induce_of_neighborSet_subset (G:=G) (s:=(U : Set (Fin n))) (v:=v)
        (fun j hj => mem_compl.mpr (ends j v.val (G.adj_symm hj)))
      have eq : H.degree v = G.degree v.val := by convert! h using 1 <;> congr 1 <;> apply Subsingleton.elim
      rw [eq]
      exact deg v.val (mem_compl.mp v.property)
    have budget := active_reader_budget G A C hm spec deg girth ends ⟨i,j,ij⟩
    right;intro B small
    apply @robust_cycle ↥U (FinsetCoe.fintype U) _ _ H _ degreeU r low _ B
    · simpa only [Fintype.card_coe] using small
    · rw [Fintype.card_coe]
      dsimp only [r]
      rw [Finset.sum_coe_sort U (fun v : Fin n => readers C.gates v.val)]
      simpa only [r,Finset.sum_attach] using budget
end PEqualNP.Research.MarkedReaderCycles
