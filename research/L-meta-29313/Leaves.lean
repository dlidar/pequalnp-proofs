import Context
namespace InverterBridge
open Finset PEqualNP.Research.TripleFormulaMass
variable {I : Type} [DecidableEq I]

theorem var_count (f : Formula I) : (vars f).card≤f.leaves := by
  induction f with
  | var i => simp [vars,Formula.leaves]
  | conj f g ih jh | disj f g ih jh =>
    exact (card_union_le _ _).trans (Nat.add_le_add ih jh)

namespace Context
def rawLeaves : Context I → Nat
  | .hole => 0
  | .meet f c | .join f c => f.leaves+c.rawLeaves

theorem count (c : Context I) : c.posVars.card+c.negVars.card≤c.rawLeaves := by
  induction c with
  | hole => simp [posVars,negVars,rawLeaves]
  | meet f c ih =>
    have hu := card_union_le (s:=vars f) (t:=c.posVars); have hv := var_count f
    simp only [posVars,negVars,rawLeaves];omega
  | join f c ih =>
    have hu := card_union_le (s:=vars f) (t:=c.negVars); have hv := var_count f
    simp only [posVars,negVars,rawLeaves];omega

theorem signal_mono (c : Context I) (x : X I) : Monotone (fun y => c.eval x y) := by
  intro a b h
  induction c with
  | hole => exact h
  | meet f c ih => exact inf_le_inf le_rfl ih
  | join f c ih => exact sup_le_sup le_rfl ih

theorem eval_depends (c : Context I) (s : Bool) : Depends (fun x => c.eval x s) (c.posVars ∪ c.negVars) := by
  induction c with
  | hole => intro x y h; rfl
  | meet f c ih =>
    intro x y h
    have e := eval_dep f x y (fun i hi => h i (by simp [posVars,negVars,hi]))
    have v := ih x y (by intro i hi; apply h; rcases mem_union.mp hi with hp|hq <;> simp [posVars,negVars, *])
    simp only [eval]; rw [show f.eval x=f.eval y from e,show c.eval x s=c.eval y s from v]
  | join f c ih =>
    intro x y h
    have e := eval_dep f x y (fun i hi => h i (by simp [posVars,negVars,hi]))
    have v := ih x y (by intro i hi; apply h; rcases mem_union.mp hi with hp|hq <;> simp [posVars,negVars, *])
    simp only [eval]; rw [show f.eval x=f.eval y from e,show c.eval x s=c.eval y s from v]

variable [Fintype I]
theorem cover (c : Context I) {G : X I → Bool} (anti : Antitone G)
    (essential : ∀ i, ∃ x y : X I,x≤y ∧ (∀ j,j≠i → x j=y j) ∧ c.eval x (G x)=false ∧ c.eval y (G y)=true) :
    c.posVars ∪ c.negVars=univ := by
  apply eq_univ_of_forall
  intro i
  by_contra hi
  obtain ⟨x,y,hxy,same,h0,h1⟩ := essential i
  have e := c.eval_depends (G y) x y (fun j hj => same j (fun v => hi (v ▸ hj)))
  have v := c.signal_mono x (anti hxy)
  change c.eval x (G y) ≤ c.eval x (G x) at v
  rw [show c.eval x (G y)=c.eval y (G y) from e,h0,h1] at v
  exact Bool.noConfusion (le_antisymm v bot_le)

theorem mixed_count (c : Context I) {G : X I → Bool} (anti : Antitone G)
    (essential : ∀ i, ∃ x y : X I,x≤y ∧ (∀ j,j≠i → x j=y j) ∧ c.eval x (G x)=false ∧ c.eval y (G y)=true) :
    Fintype.card I + (c.posVars ∩ c.negVars).card ≤ c.rawLeaves := by
  have eq := card_union_add_card_inter c.posVars c.negVars
  rw [c.cover anti essential,card_univ] at eq
  exact eq ▸ c.count

end Context
end InverterBridge
