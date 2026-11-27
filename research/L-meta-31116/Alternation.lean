import Universal

namespace InverterRepair
variable {α : Type*} [Preorder α]

def OneInverterSeparates (P N : α → Prop) : Prop :=
  ∃ (h : α → Bool) (D : α → Bool → Bool), Monotone h ∧ Decoder D ∧
    (∀ p,P p → D p (!(h p))=true) ∧ (∀ n,N n → D n (!(h n))=false)

def Alternation (P N : α → Prop) : Prop :=
  ∃ p n q m, P p ∧ N n ∧ P q ∧ N m ∧ p≤n ∧ n≤q ∧ q≤m

theorem reversal_forces {D : α → Bool → Bool} (hd : Decoder D) (h : α → Bool)
    {p n : α} (pn : p ≤ n) (yes : D p (!(h p))=true) (no : D n (!(h n))=false) :
    h p=false ∧ h n=true := by
  have obstruction : ¬ (!(h p)) ≤ (!(h n)) := by
    intro le
    have t := (hd.1 _ pn).trans (hd.2 _ le)
    change D p (!(h p)) ≤ D n (!(h n)) at t
    rw [yes,no] at t; exact Bool.noConfusion (le_antisymm t (Bool.false_le _))
  cases a : h p <;> cases b : h n <;> simp_all

noncomputable def mark (P N : α → Prop) (x : α) : Bool := by
  classical exact decide (∃ p n, P p ∧ N n ∧ p≤n ∧ n≤x)

theorem marked (P N : α → Prop) (x : α) :
    mark P N x=true ↔ ∃ p n, P p ∧ N n ∧ p≤n ∧ n≤x := by
  classical simp [mark]

theorem mark_mono (P N : α → Prop) : Monotone (mark P N) := by
  intro x y xy; cases e : mark P N x
  · exact Bool.false_le _
  · obtain ⟨p,n,hp,hn,pn,nx⟩ := (marked P N x).mp e
    rw [(marked P N y).mpr ⟨p,n,hp,hn,pn,nx.trans xy⟩]

noncomputable def decodeMarked (P : α → Prop) (h : α → Bool) (x : α) (b : Bool) : Bool := by
  classical exact decide (∃ p, P p ∧ p≤x ∧ (!(h p)) ≤ b)

theorem decodes (P : α → Prop) (h : α → Bool) (x : α) (b : Bool) :
    decodeMarked P h x b=true ↔ ∃ p,P p ∧ p≤x ∧ (!(h p))≤b := by
  classical simp [decodeMarked]

theorem decodeMarked_mono (P : α → Prop) (h : α → Bool) : Decoder (decodeMarked P h) := by
  constructor
  · intro b x y xy
    change decodeMarked P h x b ≤ decodeMarked P h y b
    cases e : decodeMarked P h x b
    · exact Bool.false_le _
    · obtain ⟨p,hp,px,hb⟩ := (decodes ..).mp e
      rw [(decodes P h y b).mpr ⟨p,hp,px.trans xy,hb⟩]
  · intro x a b ab;cases e : decodeMarked P h x a
    · exact Bool.false_le _
    · obtain ⟨p,hp,px,ha⟩ := (decodes ..).mp e
      rw [(decodes P h x b).mpr ⟨p,hp,px,ha.trans ab⟩]

theorem one_inverter_iff (P N : α → Prop) :
    OneInverterSeparates P N ↔ ¬ Alternation P N := by
  constructor
  · rintro ⟨h,D,hh,hd,hp,hn⟩ ⟨a,b,c,d,pa,nb,pc,nd,ab,bc,cd⟩
    have left := reversal_forces hd h ab (hp _ pa) (hn _ nb)
    have right := reversal_forces hd h cd (hp _ pc) (hn _ nd)
    have clash := hh bc
    rw [left.2,right.1] at clash
    exact Bool.noConfusion (le_antisymm clash (Bool.false_le _))
  · intro free
    let h := mark P N
    refine ⟨h,decodeMarked P h,mark_mono P N,decodeMarked_mono P h,?_,?_⟩
    · intro p hp; exact (decodes ..).mpr ⟨p,hp,le_rfl,le_rfl⟩
    · intro n hn; cases eq : decodeMarked P h n (!(h n))
      · rfl
      · obtain ⟨p,hp,pn,hz⟩ := (decodes ..).mp eq
        have vn : h n=true := (marked P N n).mpr ⟨p,n,hp,hn,pn,le_rfl⟩
        have vp : h p=false := by
          cases e : h p
          · rfl
          · obtain ⟨a,b,pa,nb,ab,bp⟩ := (marked P N p).mp e
            exact (free ⟨a,b,p,n,pa,nb,hp,hn,ab,bp,pn⟩).elim
        rw [vn,vp] at hz
        exact Bool.noConfusion (le_antisymm hz (Bool.false_le _))
end InverterRepair
