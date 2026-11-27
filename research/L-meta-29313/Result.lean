import Cert0
import Cert1
import Cert2
import Cert3
import Cert4
import Cert5
import Cert6
import Cert7
import FormulaTree
namespace Graph29313
open PEqualNP.Research.TripleFormulaMass InverterBridge
theorem all_raw (i : Fin 8) (f : Formula (Fin 9)) (ok : ∀ x,f.eval (enc x i)=target x) : 13<f.leaves := by
  fin_cases i <;> first | exact Cert0.bound f ok | exact Cert1.bound f ok | exact Cert2.bound f ok | exact Cert3.bound f ok | exact Cert4.bound f ok | exact Cert5.bound f ok | exact Cert6.bound f ok | exact Cert7.bound f ok
theorem monotone_leaves (f : Formula (Fin 8)) (ok : ∀ x,f.eval x=target x) : 13<f.leaves := by
  have h := all_raw 0 (raise f) (fun x => (raise_eval f x 0).trans (ok x))
  simpa only [raise_leaves] using h
/-- An unshared one-inverter expression has g.leaves+c.rawLeaves gates. -/
theorem one_inverter_lower (c : Context (Fin 8)) (g : Formula (Fin 8)) (ok : ∀ x,c.eval x (!(g.eval x))=target x) :
    14≤g.leaves+c.rawLeaves := by
  by_contra! small
  by_cases hg : g.leaves=1
  · obtain ⟨i,rfl⟩ := leaf_case g hg
    have bound := all_raw i (withRaw c) (fun x => (raw_eval c x i).trans (ok x))
    rw [raw_leaves] at bound
    omega
  · have gp := formula_pos g
    obtain ⟨f,size,eq⟩ := apply_three c g ok (by omega)
    have bound := monotone_leaves f eq
    omega
end Graph29313
