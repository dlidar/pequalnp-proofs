import Convert
namespace InverterBridge
open Finset PEqualNP.Research.TripleFormulaMass
namespace Value

def andV {I} : Value I → Value I → Value I
  | .fixed b,t => if b then t else .fixed false
  | .term f,.fixed b => if b then .term f else .fixed false
  | .term f,.term g => .term (.conj f g)
def orV {I} : Value I → Value I → Value I
  | .fixed b,t => if b then .fixed true else t
  | .term f,.fixed b => if b then .fixed true else .term f
  | .term f,.term g => .term (.disj f g)
theorem andV_count {I} (a b : Value I) : (andV a b).leaves≤a.leaves+b.leaves := by
  cases a with
  | fixed t => cases t <;> cases b <;> simp [andV,leaves]
  | term f => cases b with
    | fixed t => cases t <;> simp [andV,leaves]
    | term g => rfl
theorem orV_count {I} (a b : Value I) : (orV a b).leaves≤a.leaves+b.leaves := by
  cases a with
  | fixed t => cases t <;> cases b <;> simp [orV,leaves]
  | term f => cases b with
    | fixed t => cases t <;> simp [orV,leaves]
    | term g => rfl
theorem andV_eval {I} (a b : Value I) (x : X I) : (andV a b).eval x=(a.eval x && b.eval x) := by
  cases a with
  | fixed t => cases t <;> cases b <;> simp [andV,eval]
  | term f => cases b with
    | fixed t => cases t <;> simp [andV,eval]
    | term g => rfl
theorem orV_eval {I} (a b : Value I) (x : X I) : (orV a b).eval x=(a.eval x || b.eval x) := by
  cases a with
  | fixed t => cases t <;> cases b <;> simp [orV,eval]
  | term f => cases b with
    | fixed t => cases t <;> simp [orV,eval]
    | term g => rfl
end Value

variable {I : Type} [DecidableEq I]
def restrict (s : Finset I) (a : X I) : Formula I → Value I
  | .var i => if i∈s then .fixed (a i) else .term (.var i)
  | .conj f g => .andV (restrict s a f) (restrict s a g)
  | .disj f g => .orV (restrict s a f) (restrict s a g)

theorem restrict_eval (s : Finset I) (a x : X I) (f : Formula I) :
    (restrict s a f).eval x=f.eval (fun i => if i∈s then a i else x i) := by
  induction f with
  | var i => by_cases h : i∈s <;> simp [restrict,h,Value.eval,Formula.eval]
  | conj f g ih jh => simp [restrict,Value.andV_eval,Formula.eval,ih,jh]
  | disj f g ih jh => simp [restrict,Value.orV_eval,Formula.eval,ih,jh]

theorem restrict_count (s : Finset I) (a : X I) (f : Formula I) :
    ((vars f) ∩ s).card + (restrict s a f).leaves ≤ f.leaves := by
  induction f with
  | var i => by_cases h : i∈s <;> simp [vars,restrict,h,Formula.leaves,Value.leaves]
  | conj f g ih jh =>
    have ct := card_union_le (vars f ∩ s) (vars g ∩ s)
    have val := Value.andV_count (restrict s a f) (restrict s a g)
    simp only [vars,union_inter_distrib_right,restrict,Formula.leaves];omega
  | disj f g ih jh =>
    have ct := card_union_le (vars f ∩ s) (vars g ∩ s)
    have val := Value.orV_count (restrict s a f) (restrict s a g)
    simp only [vars,union_inter_distrib_right,restrict,Formula.leaves];omega
end InverterBridge
