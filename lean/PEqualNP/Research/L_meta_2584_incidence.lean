import PEqualNP.Research.L_meta_2584_budget

namespace PEqualNP.Research.ReadTwoIncidence
open PEqualNP.ReadK PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Research.ReadTwoBudget

/-- The increasing order in the project's input list, as in upstream L-meta-2237. -/
theorem cor_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by
    simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold PEqualNP.ReadK.setList
  rw [h]
  rfl


variable {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)

def incidence (z : Fin (P+L) → Bool) : Bool :=
  decide (∃ (p : Fin P) (l : Fin L), I p l ∧ z (Fin.castAdd L p) ∧ z (Fin.natAdd P l))

theorem left_lt_right (p : Fin P) (l : Fin L) : Fin.castAdd L p < Fin.natAdd P l := by
  change p.val < P + l.val; have := p.isLt; omega

/-- The prime supports are exactly the incident pairs, including for empty or disconnected sides. -/
theorem prime_iff (hC : ∀ z, circuitFun (P+L) C z = incidence I z) (S : Finset (Fin (P+L))) :
    IsPrimeImplicant (P+L) C S ↔
      ∃ (p : Fin P) (l : Fin L), I p l ∧ S = {Fin.castAdd L p,Fin.natAdd P l} := by
  classical
  constructor
  · intro h
    obtain ⟨p,l,hi,hp,hl⟩ := of_decide_eq_true ((hC _).symm ▸ h.1 : incidence I (setInput S) = true)
    refine ⟨p,l,hi,?_⟩
    let T : Finset (Fin (P+L)) := {Fin.castAdd L p, Fin.natAdd P l}
    have sub : T ⊆ S := by simpa only [T, Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro (of_decide_eq_true hp) (of_decide_eq_true hl)
    by_contra ne
    have bad := h.2 T (Finset.mem_ssubsets.mpr (Finset.ssubset_iff_subset_ne.mpr ⟨sub,Ne.symm ne⟩))
    have yes : circuitFun (P+L) C (setInput T) = true := by
      rw [hC]; apply decide_eq_true; exact ⟨p,l,hi,by simp [setInput,T],by simp [setInput,T]⟩
    simp [yes] at bad
  · rintro ⟨p,l,hi,rfl⟩
    constructor
    · rw [hC]; apply decide_eq_true; exact ⟨p,l,hi,by simp [setInput],by simp [setInput]⟩
    · intro T hT
      have hs := Finset.mem_ssubsets.mp hT
      rw [hC]; apply decide_eq_false
      rintro ⟨u,v,_,hu,hv⟩
      have hl : Fin.castAdd L u ∈ T := of_decide_eq_true hu
      have hr : Fin.natAdd P v ∈ T := of_decide_eq_true hv
      have e := (Finset.mem_insert.mp (hs.subset hl)).resolve_right (fun h =>
        (ne_of_lt (left_lt_right u l)) (Finset.mem_singleton.mp h))
      have f := Finset.mem_singleton.mp ((Finset.mem_insert.mp (hs.subset hr)).resolve_left
        (fun h => (ne_of_lt (left_lt_right p v)) h.symm))
      exact hs.not_ge (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff,←e,←f] using And.intro hl hr)

theorem read2_iff_edges (hAO : IsAO2 (P+L) C) (hC : ∀ z, circuitFun (P+L) C z = incidence I z) :
    IsReadK (P+L) C 2 ↔ ∀ (p : Fin P) (l : Fin L), I p l →
      ((fastWires C (P+L) p.val (P+l.val)).getD C.output zero) 2 2 = true := by
  constructor
  · intro h p l hp
    rw [← correct C hAO]
    have H := h _ ((prime_iff I C hC _).mpr ⟨p,l,hp,rfl⟩)
    simpa [cor_setList_pair _ _ (left_lt_right p l)] using H
  · intro h S hS
    obtain ⟨p,l,hp,rfl⟩ := (prime_iff I C hC S).mp hS
    rw [cor_setList_pair _ _ (left_lt_right p l),correct C hAO]
    exact h p l hp

#print axioms read2_iff_edges
end PEqualNP.Research.ReadTwoIncidence
