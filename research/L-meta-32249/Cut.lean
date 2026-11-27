import Mathlib

namespace MonotoneCut
variable {A B J : Type} [Preorder A] [Preorder B]

def Works (F : A → B → Bool) (e : A → J → Bool) : Prop :=
  Monotone e ∧ ∃ D : (J → Bool) → B → Bool, Monotone D ∧ (∀ z,Monotone (D z)) ∧ ∀ a b,D (e a) b=F a b

def Preserves (F : A → B → Bool) (e : A → J → Bool) : Prop :=
  ∀ a a',e a≤e a' → F a≤F a'

theorem works_iff (F : A → B → Bool) (e : A → J → Bool) (right : ∀ a,Monotone (F a)) :
    Works F e ↔ Monotone e ∧ Preserves F e := by
  classical
  constructor
  · rintro ⟨he,D,hD,_,ok⟩
    refine ⟨he,fun a a' h b => ?_⟩
    rw [← ok,← ok];exact hD h b
  · rintro ⟨he,pres⟩
    let D := fun (z : J → Bool) b => decide (∃ a,e a≤z ∧ F a b=true)
    refine ⟨he,D,?_,?_,?_⟩
    · intro z z' h b
      apply Bool.le_iff_imp.mpr
      intro ok
      obtain ⟨a,ha,hf⟩ := of_decide_eq_true ok
      exact decide_eq_true ⟨a,ha.trans h,hf⟩
    · intro z b b' h
      apply Bool.le_iff_imp.mpr
      intro ok
      obtain ⟨a,ha,hf⟩ := of_decide_eq_true ok
      exact decide_eq_true ⟨a,ha,Bool.le_iff_imp.mp (right a h) hf⟩
    · intro a b
      apply le_antisymm
      · apply Bool.le_iff_imp.mpr
        intro ok
        obtain ⟨a',ha,hf⟩ := of_decide_eq_true ok
        exact Bool.le_iff_imp.mp (pres a' a ha b) hf
      · apply Bool.le_iff_imp.mpr
        intro ok
        exact decide_eq_true ⟨a,le_rfl,ok⟩

def Violates (F : A → B → Bool) (v : A × A) : Prop := ∃ b,F v.1 b=true ∧ F v.2 b=false
def Conflict (v w : A × A) : Prop := v.1≤w.2 ∨ w.1≤v.2
def Separates (e : A → J → Bool) (v : A × A) (j : J) : Prop := e v.1 j=true ∧ e v.2 j=false

theorem separating_bit (F : A → B → Bool) (e : A → J → Bool) (pres : Preserves F e)
    (v : A × A) (bad : Violates F v) : ∃ j,Separates e v j := by
  classical
  by_contra! no
  have h : e v.1≤e v.2 := by
    intro j
    cases p : e v.1 j <;> cases n : e v.2 j <;> simp_all [Separates]
  obtain ⟨b,hp,hn⟩ := bad
  have wrong := pres v.1 v.2 h b
  rw [hp,hn] at wrong
  exact (by decide : ¬(true ≤ false)) wrong

theorem conflicting_bits {e : A → J → Bool} (he : Monotone e) {v w : A × A} (c : Conflict v w)
    {i j : J} (hv : Separates e v i) (hw : Separates e w j) : i≠j := by
  rintro rfl
  rcases c with c|c
  · have h := he c i
    rw [hv.1,hw.2] at h
    exact (by decide : ¬(true ≤ false)) h
  · have h := he c i
    rw [hw.1,hv.2] at h
    exact (by decide : ¬(true ≤ false)) h

theorem color_of_code {F : A → B → Bool} {e : A → J → Bool} (ok : Works F e)
    {V : Type} (v : V → A × A) (hv : ∀ i,Violates F (v i)) :
    ∃ col : V → J, ∀ i j,Conflict (v i) (v j) → col i≠col j := by
  classical
  obtain ⟨he,D,hd,_,rep⟩ := ok
  have pres : Preserves F e := by
    intro a a' h b;rw [←rep,←rep];exact hd h b
  choose col good using fun i => separating_bit F e pres (v i) (hv i)
  exact ⟨col,fun i j con => conflicting_bits he con (good i) (good j)⟩
end MonotoneCut
