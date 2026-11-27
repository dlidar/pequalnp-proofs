import FormulaMass

namespace PEqualNP.Research.FanoErase
open PEqualNP.Research.TripleFormulaMass

/-- Set every auxiliary input to false. None is the constant false expression. -/
def prune {I J : Type} : Formula (I ⊕ J) → Option (Formula I)
  | .var (.inl i) => some (.var i)
  | .var (.inr _) => none
  | .conj a b => match prune a,prune b with
    | some x,some y => some (.conj x y)
    | _,_ => none
  | .disj a b => match prune a,prune b with
    | some x,some y => some (.disj x y)
    | some x,none => some x
    | none,y => y

def rawLeaves {I J : Type} : Formula (I ⊕ J) → ℕ
  | .var (.inl _) => 1
  | .var (.inr _) => 0
  | .conj a b | .disj a b => rawLeaves a + rawLeaves b

def optEval {I : Type} (x : I → Bool) : Option (Formula I) → Bool
  | none => false
  | some f => f.eval x

theorem pruneEval {I J : Type} (f : Formula (I ⊕ J)) (x : I → Bool) :
    optEval x (prune f) = f.eval (Sum.elim x (fun _ => false)) := by
  induction f with
  | var i => cases i <;> rfl
  | conj a b ha hb =>
    cases e : prune a <;> cases h : prune b <;>
      simp_all [optEval,prune,Formula.eval]
  | disj a b ha hb =>
    cases e : prune a <;> cases h : prune b <;>
      simp_all [optEval,prune,Formula.eval]

theorem pruneSize {I J : Type} (f : Formula (I ⊕ J)) :
    ((prune f).map Formula.leaves).getD 0 ≤ rawLeaves f := by
  induction f with
  | var i => cases i <;> simp [prune,rawLeaves,Formula.leaves]
  | conj a b ha hb =>
    cases e : prune a <;> cases h : prune b <;>
      simp_all [prune,rawLeaves,Formula.leaves] <;> omega
  | disj a b ha hb =>
    cases e : prune a <;> cases h : prune b <;>
      simp_all [prune,rawLeaves,Formula.leaves] <;> omega

end PEqualNP.Research.FanoErase
