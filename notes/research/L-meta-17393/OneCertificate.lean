import One
namespace PEqualNP.Research.Triangle17393.One
open Finset PEqualNP.Research.TripleFormulaMass PEqualNP.Research.BoundTree17393
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
def tree0 : BoundTree17393.Tree (Fin 17) := (.fork 0 (.fork 1 .leaf (.fork 2 .leaf .leaf)) (.fork 1 (.fork 2 .leaf .leaf) (.fork 2 .leaf .leaf)))
theorem cert0 : check wt (cols 0) 84 tree0 ∅ (rows 0) = true := by decide +kernel
def tree1 : BoundTree17393.Tree (Fin 17) := (.fork 0 (.fork 3 (.fork 7 .leaf .leaf) (.fork 7 .leaf .leaf)) (.fork 3 (.fork 7 (.fork 4 (.fork 8 .leaf .leaf) (.fork 8 .leaf .leaf)) (.fork 4 (.fork 8 .leaf .leaf) (.fork 8 .leaf .leaf))) (.fork 7 (.fork 4 (.fork 8 .leaf .leaf) (.fork 8 .leaf .leaf)) (.fork 4 (.fork 8 .leaf .leaf) (.fork 8 .leaf .leaf)))))
theorem cert1 : check wt (cols 1) 84 tree1 ∅ (rows 1) = true := by decide +kernel
def tree2 : BoundTree17393.Tree (Fin 17) := (.fork 1 (.fork 3 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf)) (.fork 3 (.fork 11 (.fork 4 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf)) (.fork 4 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf))) (.fork 11 (.fork 4 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf)) (.fork 4 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf)))))
theorem cert2 : check wt (cols 2) 84 tree2 ∅ (rows 2) = true := by decide +kernel
def tree3 : BoundTree17393.Tree (Fin 17) := (.fork 2 (.fork 7 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf)) (.fork 7 (.fork 11 (.fork 8 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf)) (.fork 8 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf))) (.fork 11 (.fork 8 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf)) (.fork 8 (.fork 12 .leaf .leaf) (.fork 12 .leaf .leaf)))))
theorem cert3 : check wt (cols 3) 84 tree3 ∅ (rows 3) = true := by decide +kernel
def tree4 : BoundTree17393.Tree (Fin 17) := (.fork 0 (.fork 5 (.fork 9 .leaf .leaf) (.fork 9 .leaf .leaf)) (.fork 5 (.fork 9 (.fork 6 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)) (.fork 6 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf))) (.fork 9 (.fork 6 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)) (.fork 6 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)))))
theorem cert4 : check wt (cols 4) 84 tree4 ∅ (rows 4) = true := by decide +kernel
def tree5 : BoundTree17393.Tree (Fin 17) := (.fork 1 (.fork 5 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 5 (.fork 13 (.fork 6 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 6 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf))) (.fork 13 (.fork 6 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 6 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)))))
theorem cert5 : check wt (cols 5) 84 tree5 ∅ (rows 5) = true := by decide +kernel
def tree6 : BoundTree17393.Tree (Fin 17) := (.fork 2 (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 9 (.fork 13 (.fork 10 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 10 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf))) (.fork 13 (.fork 10 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 10 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)))))
theorem cert6 : check wt (cols 6) 84 tree6 ∅ (rows 6) = true := by decide +kernel
def tree7 : BoundTree17393.Tree (Fin 17) := (.fork 3 (.fork 5 (.fork 16 .leaf (.fork 15 (.fork 4 .leaf .leaf) (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)))) (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)) (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf))))) (.fork 5 (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)) (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)))) (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)) (.fork 4 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf))))))
theorem cert7 : check wt (cols 7) 84 tree7 ∅ (rows 7) = true := by decide +kernel
def tree8 : BoundTree17393.Tree (Fin 17) := (.fork 7 (.fork 9 (.fork 16 .leaf (.fork 15 (.fork 8 .leaf .leaf) (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)))) (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)) (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf))))) (.fork 9 (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)) (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)))) (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)) (.fork 8 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf))))))
theorem cert8 : check wt (cols 8) 84 tree8 ∅ (rows 8) = true := by decide +kernel
def tree9 : BoundTree17393.Tree (Fin 17) := (.fork 11 (.fork 13 (.fork 16 .leaf (.fork 15 (.fork 12 .leaf .leaf) (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)))) (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf))))) (.fork 13 (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)))) (.fork 16 (.fork 15 .leaf .leaf) (.fork 15 (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf)) (.fork 12 (.fork 14 .leaf .leaf) (.fork 14 .leaf .leaf))))))
theorem cert9 : check wt (cols 9) 84 tree9 ∅ (rows 9) = true := by decide +kernel
def tree10 : BoundTree17393.Tree (Fin 17) := (.fork 3 (.fork 5 (.fork 7 (.fork 9 .leaf (.fork 11 .leaf .leaf)) (.fork 9 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf))) (.fork 7 (.fork 9 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf)) (.fork 9 (.fork 11 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 11 .leaf .leaf)))) (.fork 5 (.fork 7 (.fork 9 (.fork 11 .leaf .leaf) (.fork 11 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf))) (.fork 9 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf))) (.fork 7 (.fork 9 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf)) (.fork 9 (.fork 11 .leaf .leaf) (.fork 11 .leaf .leaf)))))
theorem cert10 : check wt (cols 10) 84 tree10 ∅ (rows 10) = true := by decide +kernel
def certTree (i : Fin 11) := (#[tree0,tree1,tree2,tree3,tree4,tree5,tree6,tree7,tree8,tree9,tree10] : Array (BoundTree17393.Tree (Fin 17))).getD i.val .leaf
theorem all_checked (i : Fin 11) : check wt (cols i) 84 (certTree i) ∅ (rows i)=true := by
  fin_cases i
  · exact cert0
  · exact cert1
  · exact cert2
  · exact cert3
  · exact cert4
  · exact cert5
  · exact cert6
  · exact cert7
  · exact cert8
  · exact cert9
  · exact cert10
theorem lower (f : Formula (Fin 11)) (ok : ∀ x,f.eval (lift x)=triangle x) : 24 ≤ f.leaves := by
  have atom (i : Fin 11) (rs : Finset (Fin 17)) (cs : Finset (Fin 16)) (hp : ∀ r∈rs,p r i=true) (hq : ∀ c∈cs,q c i=false) : mass wt rs cs ≤ 84 := by
    apply checked wt (cols i) 84 (certTree i) ∅ (rows i) rs cs (empty_subset _)
    · simp only [empty_union]
      exact fun r hr => mem_filter.mpr ⟨mem_univ _,hp r hr⟩
    · exact fun c hc => mem_filter.mpr ⟨mem_univ _,hq c hc⟩
    · exact all_checked i
  have h := weight_bound p q wt 84 atom f univ univ
    (fun r _ => (ok _).trans (pos r)) (fun c _ => (ok _).trans (neg c))
  rw [total] at h
  omega
end PEqualNP.Research.Triangle17393.One
