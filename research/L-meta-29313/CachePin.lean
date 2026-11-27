import Restrict
namespace InverterBridge
open PEqualNP.Research.TripleFormulaMass
variable {I : Type}
def cacheReads : Formula (Option I) → Nat
  | .var none => 1
  | .var (some _) => 0
  | .conj f g | .disj f g => cacheReads f + cacheReads g
def cacheInput (x : X I) (v : Bool) : Option I → Bool := Option.elim' v x
def pinCache (v : Bool) : Formula (Option I) → Value I
  | .var none => .fixed v
  | .var (some i) => .term (.var i)
  | .conj f g => .andV (pinCache v f) (pinCache v g)
  | .disj f g => .orV (pinCache v f) (pinCache v g)

theorem pinCache_eval (f : Formula (Option I)) (b : Bool) (x : X I) :
    (pinCache b f).eval x=f.eval (cacheInput x b) := by
  induction f with
  | var i => cases i <;> rfl
  | conj f g ih jh => simp [pinCache,Value.andV_eval,Formula.eval,ih,jh]
  | disj f g ih jh => simp [pinCache,Value.orV_eval,Formula.eval,ih,jh]

theorem pinCache_count (f : Formula (Option I)) (b : Bool) :
    cacheReads f + (pinCache b f).leaves ≤ f.leaves := by
  induction f with
  | var i => cases i <;> simp [cacheReads,pinCache,Value.leaves,Formula.leaves]
  | conj f g ih jh =>
    have := Value.andV_count (pinCache b f) (pinCache b g)
    simp only [cacheReads,pinCache,Formula.leaves];omega
  | disj f g ih jh =>
    have := Value.orV_count (pinCache b f) (pinCache b g)
    simp only [cacheReads,pinCache,Formula.leaves];omega

theorem pinCache_sandwich (f : Formula (Option I)) (x : X I) (v : Bool) :
    (pinCache false f).eval x ≤ f.eval (cacheInput x v) ∧ f.eval (cacheInput x v) ≤ (pinCache true f).eval x := by
  classical
  rw [pinCache_eval,pinCache_eval]
  constructor
  · apply eval_mono
    intro i
    cases i <;> simp [cacheInput]
  · apply eval_mono
    intro i
    cases i <;> simp [cacheInput]
end InverterBridge
