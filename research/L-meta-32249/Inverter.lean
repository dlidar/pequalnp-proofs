import FormulaTree
namespace Graph32249
open PEqualNP.Research.TripleFormulaMass InverterBridge

def extra (x : X (Fin 8)) (v : Bool) : X (Fin 9) := Fin.lastCases v x
theorem raise_extra (f : Formula (Fin 8)) (x : X (Fin 8)) (v : Bool) :
    (raise f).eval (extra x v)=f.eval x := by
  induction f with
  | var i => simp [raise,Formula.eval,extra]
  | conj f g ih jh | disj f g ih jh => simp [raise,Formula.eval,ih,jh]

theorem context_extra (c : Context (Fin 8)) (x : X (Fin 8)) (v : Bool) :
    (withRaw c).eval (extra x v)=c.eval x v := by
  induction c with
  | hole =>
    change Fin.lastCases (motive := fun _ : Fin 9 => Bool) v x (Fin.last 8)=v
    rw [Fin.lastCases_last]
  | meet f c ih | join f c ih => simp [withRaw,Formula.eval,Context.eval,raise_extra,ih]

theorem two_leaves (g : Formula (Fin 8)) (size : g.leaves=2) :
    ∃ i j,g=.conj (.var i) (.var j) ∨ g=.disj (.var i) (.var j) := by
  cases g with
  | var i => simp [Formula.leaves] at size
  | conj a b =>
    have ha := formula_pos a;have hb := formula_pos b
    simp only [Formula.leaves] at size
    obtain ⟨i,rfl⟩ := leaf_case a (by omega)
    obtain ⟨j,rfl⟩ := leaf_case b (by omega)
    exact ⟨i,j,Or.inl rfl⟩
  | disj a b =>
    have ha := formula_pos a;have hb := formula_pos b
    simp only [Formula.leaves] at size
    obtain ⟨i,rfl⟩ := leaf_case a (by omega)
    obtain ⟨j,rfl⟩ := leaf_case b (by omega)
    exact ⟨i,j,Or.inr rfl⟩

def Price (G : X (Fin 8) → Bool) (n : Nat) := ∀ f : Formula (Fin 9),
    (∀ x,f.eval (extra x (!(G x)))=target x) → n≤f.leaves

theorem from_prices (raw : ∀ i, Price (fun x => x i) 15)
    (and_price : ∀ i j,Price (fun x => x i && x j) 14)
    (or_price : ∀ i j,Price (fun x => x i || x j) 14)
    (c : Context (Fin 8)) (g : Formula (Fin 8)) (ok : ∀ x,c.eval x (!(g.eval x))=target x) :
    15≤g.leaves+c.rawLeaves := by
  have lifted : ∀ x,(withRaw c).eval (extra x (!(g.eval x)))=target x :=
    fun x => (context_extra c x _).trans (ok x)
  by_contra! small
  by_cases one : g.leaves=1
  · obtain ⟨i,gi⟩ := leaf_case g one
    rw [gi] at lifted
    have h := raw i _ lifted
    rw [raw_leaves] at h;omega
  by_cases two : g.leaves=2
  · obtain ⟨i,j,h|h⟩ := two_leaves g two
    · rw [h] at lifted;have lb := and_price i j _ lifted;rw [raw_leaves] at lb;omega
    · rw [h] at lifted;have lb := or_price i j _ lifted;rw [raw_leaves] at lb;omega
  · have hp := formula_pos g
    obtain ⟨f,hf,eq⟩ := apply_three c g ok (by omega)
    have lb := raw 0 (raise f) (fun x => (raise_extra f x _).trans (eq x))
    rw [raise_leaves] at lb;omega
end Graph32249
