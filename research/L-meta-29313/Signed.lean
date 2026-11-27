import FormulaMass
import Reference
open Finset PEqualNP.Research.TripleFormulaMass
namespace Graph29313

def bits (x : Nat) (i : Fin 8) := x.testBit i.val
def enc (x : Fin 8 → Bool) (neg : Fin 8) : Fin 9 → Bool := Fin.lastCases (!(x neg)) x

theorem atom_rows {R C I : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (p : R → I → Bool) (q : C → I → Bool) (w : R → C → Int) (cap : Int)
    (test : ∀ i,∀ s ∈ (univ.filter (fun c => q c i=false)).powerset,
      (∑ r∈univ.filter (fun r => p r i=true),max 0 (∑ c∈s,w r c)) ≤ cap) :
    ∀ i (rs : Finset R) (cs : Finset C), (∀ r∈rs,p r i=true) →
      (∀ c∈cs,q c i=false) → mass w rs cs ≤ cap := by
  intro i rs cs hp hq
  have sub : rs ⊆ univ.filter (fun r => p r i=true) := fun r hr => mem_filter.mpr ⟨mem_univ _,hp r hr⟩
  rw [mass,sum_comm]
  calc
    _ ≤ ∑ r∈rs,max 0 (∑ c∈cs,w r c) := sum_le_sum (fun r _ => le_max_right _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_left _ _)
    _ ≤ _ := test i cs (mem_powerset.mpr (fun c hc => mem_filter.mpr ⟨mem_univ _,hq c hc⟩))

theorem signed_lower {r c : Nat} (P : Fin r → Nat) (N : Fin c → Nat)
    (w : Fin r → Fin c → Int) (neg : Fin 8) (cap : Int) (bound : Nat)
    (hp : ∀ i,target (bits (P i))=true) (hn : ∀ i,target (bits (N i))=false)
    (test : ∀ i : Fin 9, ∀ s ∈ (univ.filter (fun j => enc (bits (N j)) neg i=false)).powerset,
      (∑ j∈univ.filter (fun j => enc (bits (P j)) neg i=true), max 0 (∑ k∈s,w j k)) ≤ cap)
    (nonneg : 0 ≤ cap) (score : cap*(bound: Int) < mass w univ univ)
    (f : Formula (Fin 9)) (ok : ∀ x,f.eval (enc x neg)=target x) : bound < f.leaves := by
  have h := weight_bound (fun j => enc (bits (P j)) neg) (fun j => enc (bits (N j)) neg) w cap
    (atom_rows _ _ w cap test) f univ univ (fun j _ => (ok _).trans (hp j)) (fun j _ => (ok _).trans (hn j))
  by_contra! le
  have := mul_le_mul_of_nonneg_left (show (f.leaves:Int)≤bound by exact_mod_cast le) nonneg
  linarith
end Graph29313
