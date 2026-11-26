import Mathlib

namespace PEqualNP.Research.TripleFormulaMass
open Finset
inductive Formula (I : Type) where
  | var (i : I)
  | conj (f g : Formula I)
  | disj (f g : Formula I)
def Formula.eval {I} (x : I → Bool) : Formula I → Bool
  | .var i => x i
  | .conj f g => f.eval x && g.eval x
  | .disj f g => f.eval x || g.eval x
def Formula.leaves {I} : Formula I → Nat
  | .var _ => 1
  | .conj f g | .disj f g => f.leaves+g.leaves

variable {R C I : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
def mass (w : R → C → Int) (rs : Finset R) (cs : Finset C) := ∑ c∈cs,∑ r∈rs,w r c
theorem columns_partition (w : R → C → Int) (rs : Finset R) {t cs : Finset C} (sub : t⊆cs) :
    mass w rs (cs\t)+mass w rs t=mass w rs cs := sum_sdiff sub
theorem rows_partition (w : R → C → Int) (cs : Finset C) {t rs : Finset R} (sub : t⊆rs) :
    mass w (rs\t) cs+mass w t cs=mass w rs cs := by
  simp only [mass,← sum_add_distrib];apply sum_congr rfl;intro c hc;exact sum_sdiff sub

theorem weight_bound (p : R → I → Bool) (q : C → I → Bool) (w : R → C → Int) (cap : Int)
    (atom : ∀ i (rs : Finset R) (cs : Finset C), (∀ r∈rs,p r i=true) →
      (∀ c∈cs,q c i=false) → mass w rs cs ≤ cap) (f : Formula I)
    (rs : Finset R) (cs : Finset C) (hp : ∀ r∈rs,f.eval (p r)=true)
    (hq : ∀ c∈cs,f.eval (q c)=false) : mass w rs cs ≤ cap*f.leaves := by
  classical
  induction f generalizing rs cs with
  | var i => simpa [Formula.leaves] using atom i rs cs hp hq
  | conj f g ih jh =>
    let t := cs.filter (fun c => f.eval (q c)=false)
    have a := ih rs t (fun r hr => (Bool.and_eq_true_iff.mp (hp r hr)).1)
      (fun c hc => (mem_filter.mp hc).2)
    have b := jh rs (cs\t) (fun r hr => (Bool.and_eq_true_iff.mp (hp r hr)).2) (by
      intro c hc
      have no := (mem_sdiff.mp hc).2
      have ne : f.eval (q c)≠false := fun e => no (mem_filter.mpr ⟨(mem_sdiff.mp hc).1,e⟩)
      have h := hq c (mem_sdiff.mp hc).1
      simpa [Formula.eval,Bool.eq_true_of_not_eq_false ne] using h)
    have eq := columns_partition w rs (filter_subset _ cs : t⊆cs)
    rw [← eq]
    simpa only [Formula.leaves,Nat.cast_add,mul_add,add_comm] using add_le_add b a
  | disj f g ih jh =>
    let t := rs.filter (fun r => f.eval (p r)=true)
    have a := ih t cs (fun r hr => (mem_filter.mp hr).2)
      (fun c hc => (Bool.or_eq_false_iff.mp (hq c hc)).1)
    have b := jh (rs\t) cs (by
      intro r hr
      have no := (mem_sdiff.mp hr).2
      have ne : f.eval (p r)≠true := fun e => no (mem_filter.mpr ⟨(mem_sdiff.mp hr).1,e⟩)
      have h := hp r (mem_sdiff.mp hr).1
      simpa [Formula.eval,Bool.eq_false_of_not_eq_true ne] using h)
      (fun c hc => (Bool.or_eq_false_iff.mp (hq c hc)).2)
    have eq := rows_partition w cs (filter_subset _ rs : t⊆rs)
    rw [← eq]
    simpa only [Formula.leaves,Nat.cast_add,mul_add,add_comm] using add_le_add b a

theorem atom_from_columns (p : R → I → Bool) (q : C → I → Bool) (w : R → C → Int) (cap : Int)
    (test : ∀ i,∀ s ∈ (univ.filter (fun r => p r i=true)).powerset,
      (∑ c∈univ.filter (fun c => q c i=false),max 0 (∑ r∈s,w r c)) ≤ cap) :
    ∀ i (rs : Finset R) (cs : Finset C), (∀ r∈rs,p r i=true) →
      (∀ c∈cs,q c i=false) → mass w rs cs ≤ cap := by
  intro i rs cs hp hq
  have sub : cs ⊆ univ.filter (fun c => q c i=false) := fun c hc => mem_filter.mpr ⟨mem_univ _,hq c hc⟩
  calc
    _ ≤ ∑ c∈cs,max 0 (∑ r∈rs,w r c) := sum_le_sum (fun c _ => le_max_right _ _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => le_max_left _ _)
    _ ≤ _ := test i rs (mem_powerset.mpr (fun r hr => mem_filter.mpr ⟨mem_univ _,hp r hr⟩))
end PEqualNP.Research.TripleFormulaMass
