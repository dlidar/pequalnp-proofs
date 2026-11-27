import Four
namespace MonotoneCut
variable {A B I J : Type} [Preorder A] [Preorder B]
def Both (F : A → B → Bool) (e : A → I → Bool) (h : B → J → Bool) : Prop :=
  Monotone e ∧ Monotone h ∧ ∃ D : (I → Bool) → (J → Bool) → Bool,
    Monotone D ∧ (∀ z,Monotone (D z)) ∧ ∀ a b,D (e a) (h b)=F a b

theorem both_iff (F : A → B → Bool) (e : A → I → Bool) (h : B → J → Bool) :
    Both F e h ↔ Works F e ∧ Works (fun b a => F a b) h := by
  classical
  constructor
  · rintro ⟨me,mh,D,md,nd,ok⟩
    constructor
    · refine ⟨me,fun z b => D z (h b),?_,fun z => (nd z).comp mh,ok⟩
      intro z w le b;exact md le _
    · refine ⟨mh,fun z a => D (e a) z,?_,?_,fun b a => ok a b⟩
      · intro z w le a;exact nd (e a) le
      · intro z a b le;exact md (me le) z
  · rintro ⟨⟨me,d,md,_,de⟩,mh,g,mg,_,ge⟩
    let D := fun (z : I → Bool) (w : J → Bool) => decide (∃ a b,e a≤z ∧ h b≤w ∧ F a b=true)
    refine ⟨me,mh,D,?_,?_,?_⟩
    · intro u v le w;apply Bool.le_iff_imp.mpr;intro hu
      obtain ⟨a,b,ha,hb,ab⟩ := of_decide_eq_true hu
      exact decide_eq_true ⟨a,b,ha.trans le,hb,ab⟩
    · intro z u v le;apply Bool.le_iff_imp.mpr;intro hu
      obtain ⟨a,b,ha,hb,ab⟩ := of_decide_eq_true hu
      exact decide_eq_true ⟨a,b,ha,hb.trans le,ab⟩
    · intro a b;apply le_antisymm
      · apply Bool.le_iff_imp.mpr;intro hz
        obtain ⟨a',b',ha,hb,ab⟩ := of_decide_eq_true hz
        have s := md ha b';rw [de,de] at s
        have t := mg hb a;rw [ge,ge] at t
        exact Bool.le_iff_imp.mp (s.trans t) ab
      · apply Bool.le_iff_imp.mpr;intro ab;exact decide_eq_true ⟨a,b,le_rfl,le_rfl,ab⟩

end MonotoneCut
namespace Graph32249
open MonotoneCut

def BothCan (F : Four → Four → Bool) (n : Nat) := ∃ k l,k+l=n ∧
  ∃ (e : Four → Fin k → Bool) (h : Four → Fin l → Bool), Both F e h

theorem add_widths {F : Four → Four → Bool} {a b : Nat}
    (ha : ∀ k,Can F k ↔ a≤k) (hb : ∀ k,Can (fun y x => F x y) k ↔ b≤k) (n : Nat) :
    BothCan F n ↔ a+b≤n := by
  constructor
  · rintro ⟨k,l,rfl,e,h,ok⟩
    have both := (both_iff _ _ _).1 ok
    exact Nat.add_le_add ((ha _).1 ⟨e,both.1⟩) ((hb _).1 ⟨h,both.2⟩)
  · intro h
    obtain ⟨e,he⟩ := (ha a).2 le_rfl
    obtain ⟨f,hf⟩ := (hb (n-a)).2 (by omega)
    exact ⟨a,n-a,by omega,e,f,(both_iff _ _ _).2 ⟨he,hf⟩⟩
end Graph32249
