import Upper
namespace PEqualNP.Research.Cached9815
open TripleFormulaMass Finset
def Strong (k : Key) := ∀ f : Formula (Option EdgeInput),(∀ x,f.eval (extendsKey k x)=target x) → 26 ≤ f.leaves
theorem by_strong_cert (wt : Weights) (cap : Int) (hcap : 0<cap)
    (total : 25*cap < mass wt univ univ) (raw : rawOK wt cap=true)
    (k : Key) (extra : extraOK wt cap k=true) : Strong k := by
  intro f correct
  have test := atom_from_columns (fun r => extendsKey k (pos r)) (fun c => extendsKey k (neg c)) wt cap (by
    intro i s hm
    cases i with
    | none => exact score_ok _ _ _ _ (by simpa [extraOK] using extra) _ hm
    | some i =>
      have hi := List.all_eq_true.mp raw i (by simp)
      exact score_ok _ _ _ _ (by simpa [extendsKey,fill] using hi) _ hm)
  have h := weight_bound _ _ wt cap test f univ univ (fun r _ => (correct _).trans (rows_ok r))
    (fun c _ => (correct _).trans (cols_ok c))
  by_contra! small
  have le : (f.leaves : Int) ≤ 25 := by omega
  linarith [mul_le_mul_of_nonneg_left le (le_of_lt hcap)]
def adjacent (a b : EdgeInput) := ((a==0 && b==8) || (b==0 && a==8)) || ((a==0 && b==10) || (b==0 && a==10)) || ((a==1 && b==7) || (b==1 && a==7)) || ((a==1 && b==9) || (b==1 && a==9)) || ((a==1 && b==13) || (b==1 && a==13)) || ((a==2 && b==8) || (b==2 && a==8)) || ((a==2 && b==13) || (b==2 && a==13)) || ((a==3 && b==7) || (b==3 && a==7)) || ((a==3 && b==11) || (b==3 && a==11)) || ((a==3 && b==12) || (b==3 && a==12)) || ((a==4 && b==10) || (b==4 && a==10)) || ((a==4 && b==11) || (b==4 && a==11)) || ((a==4 && b==13) || (b==4 && a==13)) || ((a==5 && b==9) || (b==5 && a==9)) || ((a==5 && b==10) || (b==5 && a==10)) || ((a==5 && b==12) || (b==5 && a==12)) || ((a==6 && b==8) || (b==6 && a==8)) || ((a==6 && b==9) || (b==6 && a==9)) || ((a==6 && b==11) || (b==6 && a==11))
def usefulKey (k : Key) : Bool := let p := pairTab[k.val % 91]!
  decide (91≤k.val) && (List.finRange 14).any (fun j => adjacent p.1 j && adjacent p.2 j)
def Sharp (k : Key) := ∃ f : Formula (Option EdgeInput), f.leaves=25 ∧ ∀ x,f.eval (extendsKey k x)=target x
end PEqualNP.Research.Cached9815
