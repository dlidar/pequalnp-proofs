import PEqualNP.Research.Transport3321

namespace PEqualNP.Research.Attachments3321
open Finset PEqualNP.MetaComplexity
open PEqualNP.Research.ForestNormal3321 PEqualNP.Research.GateCuts3321
open PEqualNP.Research.Transport3321

theorem value_insert {p l} (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l) (z) :
    value (insert (a,b) E) z = (value E z || (z (Fin.castAdd l a) && z (Fin.natAdd p b))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [value_true,Bool.or_eq_true,Bool.and_eq_true,Target]
  constructor
  · rintro ⟨i,j,he,pi,lj⟩
    rcases mem_insert.mp he with eq|old
    · cases eq;exact Or.inr ⟨pi,lj⟩
    · exact Or.inl ⟨i,j,old,pi,lj⟩
  · rintro (⟨i,j,old,pi,lj⟩|⟨pi,lj⟩)
    · exact ⟨i,j,mem_insert_of_mem old,pi,lj⟩
    · exact ⟨a,b,mem_insert_self _ _,pi,lj⟩

theorem target_nonconstant {p l} {E : Finset (Fin p × Fin l)} (ne : E.Nonempty) :
    Nonconst (value E) := by
  obtain ⟨⟨i,j⟩,mem⟩ := ne
  refine ⟨fun _ => false,fun _ => true,?_⟩
  have a : value E (fun _ => false) = false := Bool.eq_false_iff.mpr (fun h => by
    obtain ⟨_,_,_,no,_⟩ := (value_true _ _).mp h;cases no)
  have b : value E (fun _ => true) = true := (value_true _ _).mpr ⟨i,j,mem,rfl,rfl⟩
  simp [a,b]

theorem ignore_isolated {p l} (E : Finset (Fin p × Fin l)) (v : Fin (p+l))
    (iso : ∀ e ∈ E, Fin.castAdd l e.1 ≠ v ∧ Fin.natAdd p e.2 ≠ v) : Ignores (value E) v := by
  intro x b
  apply Bool.eq_iff_iff.mpr
  rw [value_true,value_true]
  constructor <;> rintro ⟨i,j,he,a,c⟩ <;> refine ⟨i,j,he,?_,?_⟩
  all_goals first | simpa [Function.update_of_ne (iso (i,j) he).1] using a
                  | simpa [Function.update_of_ne (iso (i,j) he).2] using c

theorem point_line_ne {p l} (a : Fin p) (b : Fin l) : Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro eq
  have h := congrArg Fin.val eq
  simp at h;omega

theorem point_tests {p l} (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Bool) :
    ∃ x, value E x = false ∧ x (Fin.castAdd l a) = b := by
  let x : Fin (p+l) → Bool := fun i => decide (i=Fin.castAdd l a) && b
  refine ⟨x,Bool.eq_false_iff.mpr (fun h => ?_),by simp [x]⟩
  obtain ⟨i,j,_,_,bad⟩ := (value_true _ _).mp h
  simpa [x,(point_line_ne a j).symm] using bad

theorem path_two {p n lo hi} (E : Finset (Fin p × Fin (n+1))) (ne : E.Nonempty)
    (a u : Fin p) (v : Fin (n+1)) (diff : a ≠ u)
    (fresh : ∀ e ∈ E, e.1 ≠ u ∧ e.2 ≠ v) (hk : 0 < lo) (h : Bounds E lo hi) :
    Bounds (insert (u,v) (insert (a,v) E)) (lo+3) (hi+3) := by
  let A := Fin.castAdd (n+1) a
  let U := Fin.castAdd (n+1) u
  let V := Fin.natAdd p v
  have au : A ≠ U := fun eq => diff (Fin.ext (congrArg (fun i : Fin (p+(n+1)) => i.val) eq))
  have fu : Ignores (value E) U := by
    apply ignore_isolated
    intro e mem
    exact ⟨fun eq => (fresh _ mem).1 (Fin.ext (congrArg (fun i : Fin (p+(n+1)) => i.val) eq)),(point_line_ne _ _).symm⟩
  have fv : Ignores (value E) V := by
    apply ignore_isolated
    intro e mem
    refine ⟨point_line_ne _ _,fun eq => (fresh _ mem).2 (Fin.ext ?_)⟩
    have h := congrArg Fin.val eq
    simp [V] at h;exact h
  have idf : value (insert (u,v) (insert (a,v) E)) = tail (value E) (fun x => x A) U V := by
    funext x
    simp only [value_insert,tail,A,U,V]
    generalize value E x = q
    cases q <;> cases x (Fin.castAdd (n+1) a) <;> cases x (Fin.castAdd (n+1) u) <;>
      cases x (Fin.natAdd p v) <;> rfl
  refine ⟨?_,?_⟩
  · rw [idf]
    exact tail_cost (point_line_ne u v) h.1 hk (target_nonconstant ne) fu fv
      (fun x b => Function.update_of_ne au _ _) (fun x b => Function.update_of_ne (point_line_ne a v) _ _)
      (point_tests E a)
  · obtain ⟨P,L,cov,budget⟩ := h.2
    refine ⟨P,insert v L,?_,?_⟩
    · intro e mem
      rcases mem_insert.mp mem with rfl|other
      · exact Or.inr (mem_insert_self _ _)
      rcases mem_insert.mp other with rfl|old
      · exact Or.inr (mem_insert_self _ _)
      exact (cov _ old).imp_right mem_insert_of_mem
    · have c := card_insert_le (u,v) (insert (a,v) E)
      have d := card_insert_le (a,v) E
      have e := card_insert_le v L
      have pos := card_pos.mpr ne
      omega

end PEqualNP.Research.Attachments3321
