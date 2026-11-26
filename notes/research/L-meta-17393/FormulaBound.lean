import Circuit
namespace PEqualNP.Research.Triangle17393
open Finset PEqualNP.Research.TripleFormulaMass
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
def row (i : Fin 10) := ([19, 37, 73, 134, 266, 524, 176, 336, 608, 896] : List Nat).getD i.val 0
def col (i : Fin 10) := ([126, 413, 483, 492, 683, 725, 730, 822, 825, 839] : List Nat).getD i.val 0
def p (r i : Fin 10) := (row r).testBit i.val
def q (c i : Fin 10) := (col c).testBit i.val
def plus (c : Fin 10) := ([504, 742, 798, 222, 853, 685, 365, 435, 627, 907] : List Nat).getD c.val 0
def minus (c : Fin 10) := ([512, 256, 32, 1, 128, 16, 2, 4, 8, 64] : List Nat).getD c.val 0
def wt (r c : Fin 10) : Int := if (plus c).testBit r.val then 3 else if (minus c).testBit r.val then -4 else 0
def allowed (i : Fin 10) := (univ.filter (fun r => p r i=true)).powerset
def score (i : Fin 10) (s : Finset (Fin 10)) : Int :=
  ∑ c∈univ.filter (fun c => q c i=false),max 0 (∑ r∈s,wt r c)
def bad (i : Fin 10) := (allowed i).filter (fun s => 6 < score i s)
theorem positives : ∀ r, triangle (p r)=true := by decide +kernel
theorem negatives : ∀ c, triangle (q c)=false := by decide +kernel
theorem total : mass wt univ univ=140 := by decide +kernel
theorem cap : ∀ i,bad i=∅ := by decide +kernel
theorem test_bound (i : Fin 10) (s : Finset (Fin 10)) (hs : s∈allowed i) :
    score i s ≤ 6 := by
  by_contra! h
  have m : s∈bad i := mem_filter.mpr ⟨hs,h⟩
  simpa [cap] using m
theorem formula_lower (f : Formula (Fin 10)) (exact_on : ∀ x,f.eval x=triangle x) :
    24 ≤ f.leaves := by
  have h := weight_bound p q wt 6 (atom_from_columns p q wt 6 test_bound) f univ univ
    (fun r _ => (exact_on _).trans (positives r)) (fun c _ => (exact_on _).trans (negatives c))
  rw [total] at h
  omega
theorem exact_formula (k : Nat) : (∃ f : Formula (Fin 10), (∀ x,f.eval x=triangle x) ∧ f.leaves≤k) ↔ 24≤k := by
  constructor
  · rintro ⟨f,ok,b⟩
    exact (formula_lower f ok).trans b
  · intro h
    exact ⟨witness,fun x => (witness_eval x).trans (reference_correct x),witness_size ▸ h⟩
end PEqualNP.Research.Triangle17393
