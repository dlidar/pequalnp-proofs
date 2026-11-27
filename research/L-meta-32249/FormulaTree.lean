import Triple
import Graph

namespace Graph32249
open PEqualNP.Research.TripleFormulaMass InverterBridge

def enc (x : X (Fin 8)) (i : Fin 8) : X (Fin 9) := Fin.lastCases (!(x i)) x

def raise (f : Formula (Fin 8)) : Formula (Fin 9) := match f with
  | .var i => .var i.castSucc
  | .conj f g => .conj (raise f) (raise g)
  | .disj f g => .disj (raise f) (raise g)

theorem raise_eval (f : Formula (Fin 8)) (x : X (Fin 8)) (i : Fin 8) :
    (raise f).eval (enc x i) = f.eval x := by
  induction f with
  | var j => simp [raise,Formula.eval,enc]
  | conj f g ih jh | disj f g ih jh => simp [raise,Formula.eval,ih,jh]

theorem raise_leaves (f : Formula (Fin 8)) : (raise f).leaves=f.leaves := by
  induction f <;> simp_all [raise,Formula.leaves]

def withRaw : Context (Fin 8) → Formula (Fin 9)
  | .hole => .var (Fin.last 8)
  | .meet f c => .conj (raise f) (withRaw c)
  | .join f c => .disj (raise f) (withRaw c)

theorem raw_eval (c : Context (Fin 8)) (x : X (Fin 8)) (i : Fin 8) :
    (withRaw c).eval (enc x i)=c.eval x (!(x i)) := by
  induction c with
  | hole =>
    change Fin.lastCases (motive := fun _ : Fin 9 => Bool) (!(x i)) x (Fin.last 8) = !(x i)
    rw [Fin.lastCases_last]
  | meet f c ih | join f c ih => simp [withRaw,Formula.eval,Context.eval,raise_eval,ih]

theorem raw_leaves (c : Context (Fin 8)) : (withRaw c).leaves = c.rawLeaves+1 := by
  induction c <;> simp_all [withRaw,Formula.leaves,Context.rawLeaves,raise_leaves,Nat.add_assoc]

theorem formula_pos (g : Formula (Fin 8)) : 0<g.leaves := by induction g <;> simp_all [Formula.leaves] <;> omega

theorem leaf_case (g : Formula (Fin 8)) (one : g.leaves=1) : ∃ i,g=.var i := by
  cases g with
  | var i => exact ⟨i,rfl⟩
  | conj a b | disj a b =>
    have := formula_pos a; have := formula_pos b
    simp only [Formula.leaves] at one;omega

theorem apply_three (c : Context (Fin 8)) (g : Formula (Fin 8)) (ok : ∀ x,c.eval x (!(g.eval x))=target x)
    (small : c.rawLeaves≤11) :
    ∃ f : Formula (Fin 8), f.leaves≤c.rawLeaves+2 ∧ ∀ x,f.eval x=target x := by
  have eq : (fun x => c.eval x (!(g.eval x)))=target := funext ok
  have anti : Antitone (fun x => !(g.eval x)) := by
    intro x y h
    have le := eval_mono g h
    exact (show ∀ a b : Bool, a≤b → (!b)≤(!a) by decide) _ _ le
  obtain ⟨f,hf,he⟩ := c.three_mixed _ anti (by rw [eq]; exact mono) (by simpa only [ok] using essential)
    (by simpa using small)
  exact ⟨f,hf,fun x => (he x).trans (ok x)⟩
end Graph32249
