import Bridge
namespace InverterBridge
open PEqualNP.Research.TripleFormulaMass
variable {I : Type} [DecidableEq I]

def vars : Formula I → Finset I
  | .var i => {i}
  | .conj f g | .disj f g => vars f ∪ vars g

theorem eval_mono (f : Formula I) : Monotone (fun x => f.eval x) := by
  intro x y h
  induction f with
  | var i => exact h i
  | conj f g ih jh => exact inf_le_inf ih jh
  | disj f g ih jh => exact sup_le_sup ih jh

theorem eval_dep (f : Formula I) : Depends (fun x => f.eval x) (vars f) := by
  induction f with
  | var i => intro x y h; exact h i (by simp [vars])
  | conj f g ih jh | disj f g ih jh =>
    intro x y h
    simp only [Formula.eval,ih x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      jh x y (fun i hi => h i (Finset.mem_union_right _ hi))]

inductive Context (I : Type) where
  | hole
  | meet (sibling : Formula I) (next : Context I)
  | join (sibling : Formula I) (next : Context I)

namespace Context
def eval (x : X I) (y : Bool) : Context I → Bool
  | .hole => y
  | .meet f c => f.eval x && c.eval x y
  | .join f c => f.eval x || c.eval x y

def req (x : X I) : Context I → Bool
  | .hole => true
  | .meet f c => f.eval x && c.req x
  | .join _ c => c.req x
def ban (x : X I) : Context I → Bool
  | .hole => false
  | .meet _ c => c.ban x
  | .join f c => f.eval x || c.ban x

def posVars : Context I → Finset I
  | .hole => ∅
  | .meet f c => vars f ∪ c.posVars
  | .join _ c => c.posVars
def negVars : Context I → Finset I
  | .hole => ∅
  | .meet _ c => c.negVars
  | .join f c => vars f ∪ c.negVars

theorem req_mono (c : Context I) : Monotone (fun x => c.req x) := by
  intro x y h
  induction c with
  | hole => rfl
  | meet f c ih => exact inf_le_inf (eval_mono f h) ih
  | join f c ih => exact ih
theorem ban_mono (c : Context I) : Monotone (fun x => c.ban x) := by
  intro x y h
  induction c with
  | hole => rfl
  | meet f c ih => exact ih
  | join f c ih => exact sup_le_sup (eval_mono f h) ih

theorem req_dep (c : Context I) : Depends (fun x => c.req x) c.posVars := by
  induction c with
  | hole => intro x y _; rfl
  | join f c ih => exact ih
  | meet f c ih =>
    intro x y h
    simp only [req,eval_dep f x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      ih x y (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem ban_dep (c : Context I) : Depends (fun x => c.ban x) c.negVars := by
  induction c with
  | hole => intro x y _; rfl
  | meet f c ih => exact ih
  | join f c ih =>
    intro x y h
    simp only [ban,eval_dep f x y (fun i hi => h i (Finset.mem_union_left _ hi)),
      ih x y (fun i hi => h i (Finset.mem_union_right _ hi))]

theorem active (c : Context I) (x : X I) {y z : Bool} :
    c.eval x y ≠ c.eval x z → c.req x=true ∧ c.ban x=false := by
  induction c with
  | hole => simp [req,ban]
  | meet f c ih => cases h : f.eval x <;> simp [eval,req,ban,h] <;> exact ih
  | join f c ih => cases h : f.eval x <;> simp [eval,req,ban,h] <;> exact ih

theorem pass (c : Context I) (x : X I) (y : Bool) :
    c.req x=true → c.ban x=false → c.eval x y=y := by
  induction c with
  | hole => simp [eval]
  | meet f c ih => cases h : f.eval x <;> simp [req,ban,eval,h] <;> exact ih
  | join f c ih => cases h : f.eval x <;> simp [req,ban,eval,h] <;> exact ih

variable [Fintype I]
theorem eliminate (c : Context I) (G : X I → Bool) (anti : Antitone G)
    (mono : Monotone (fun x => c.eval x (G x))) (i j : I)
    (sub : ∀ t∈c.posVars,t∈c.negVars → t=i ∨ t=j) :
    ∃ k : Fin 4, ∀ x,c.eval x (G x) = c.eval x (choose k (x i,x j)) := by
  obtain ⟨k,hk⟩ := replace_two (P:=c.posVars) (Q:=c.negVars)
    c.req_mono c.ban_mono mono anti c.req_dep c.ban_dep (fun x a b => c.pass x (G x) a b) i j sub
  refine ⟨k,fun x => ?_⟩
  by_contra ne
  obtain ⟨a,b⟩ := c.active x ne
  exact ne ((hk x a b).trans (c.pass x _ a b).symm)
end Context
end InverterBridge
