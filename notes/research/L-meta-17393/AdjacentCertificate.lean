import Adjacent
namespace PEqualNP.Research.Triangle17393.Adjacent
open Finset PEqualNP.Research.TripleFormulaMass PEqualNP.Research.BoundTree17393
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
def tree0 : BoundTree17393.Tree (Fin 19) := (.fork 1 (.fork 3 (.fork 0 .leaf (.fork 2 (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf)) (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf)))) (.fork 0 (.fork 2 (.fork 4 .leaf (.fork 16 .leaf .leaf)) (.fork 4 (.fork 16 .leaf .leaf) .leaf)) (.fork 2 (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf)) (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf))))) (.fork 3 (.fork 0 (.fork 2 (.fork 4 .leaf (.fork 16 .leaf .leaf)) (.fork 4 (.fork 16 .leaf .leaf) .leaf)) (.fork 2 (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf)) (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf)))) (.fork 0 (.fork 2 (.fork 4 .leaf (.fork 16 .leaf .leaf)) (.fork 4 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf))) (.fork 2 (.fork 4 .leaf .leaf) (.fork 4 .leaf .leaf)))))
theorem cert0 : check wt (cols 0) 1308 tree0 ∅ (rows 0) = true := by decide +kernel
def tree1 : BoundTree17393.Tree (Fin 19) := (.fork 5 (.fork 9 (.fork 0 .leaf (.fork 6 (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)) (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)))) (.fork 0 (.fork 6 (.fork 10 .leaf (.fork 18 .leaf .leaf)) (.fork 10 (.fork 18 .leaf .leaf) .leaf)) (.fork 6 (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)) (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf))))) (.fork 9 (.fork 0 (.fork 6 (.fork 10 .leaf (.fork 18 .leaf .leaf)) (.fork 10 (.fork 18 .leaf .leaf) .leaf)) (.fork 6 (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)) (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)))) (.fork 0 (.fork 6 (.fork 10 .leaf (.fork 18 .leaf .leaf)) (.fork 10 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf))) (.fork 6 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)))))
theorem cert1 : check wt (cols 1) 1308 tree1 ∅ (rows 1) = true := by decide +kernel
def tree2 : BoundTree17393.Tree (Fin 19) := (.fork 1 (.fork 5 (.fork 13 .leaf (.fork 2 .leaf (.fork 6 .leaf .leaf))) (.fork 13 (.fork 2 .leaf .leaf) (.fork 2 .leaf .leaf))) (.fork 5 (.fork 13 (.fork 2 .leaf (.fork 6 .leaf .leaf)) (.fork 2 .leaf (.fork 6 .leaf .leaf))) (.fork 13 (.fork 2 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)) (.fork 2 (.fork 6 .leaf .leaf) (.fork 6 .leaf .leaf)))))
theorem cert2 : check wt (cols 2) 1308 tree2 ∅ (rows 2) = true := by decide +kernel
def tree3 : BoundTree17393.Tree (Fin 19) := (.fork 3 (.fork 9 (.fork 13 .leaf (.fork 4 .leaf (.fork 10 .leaf .leaf))) (.fork 13 (.fork 4 .leaf .leaf) (.fork 4 .leaf .leaf))) (.fork 9 (.fork 13 (.fork 4 .leaf (.fork 10 .leaf .leaf)) (.fork 4 .leaf (.fork 10 .leaf .leaf))) (.fork 13 (.fork 4 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)) (.fork 4 (.fork 10 .leaf .leaf) (.fork 10 .leaf .leaf)))))
theorem cert3 : check wt (cols 3) 1308 tree3 ∅ (rows 3) = true := by decide +kernel
def tree4 : BoundTree17393.Tree (Fin 19) := (.fork 7 (.fork 11 .leaf (.fork 0 .leaf .leaf)) (.fork 11 (.fork 0 .leaf .leaf) (.fork 0 .leaf .leaf)))
theorem cert4 : check wt (cols 4) 1308 tree4 ∅ (rows 4) = true := by decide +kernel
def tree5 : BoundTree17393.Tree (Fin 19) := (.fork 15 (.fork 7 (.fork 1 .leaf (.fork 16 .leaf .leaf)) (.fork 1 (.fork 16 .leaf (.fork 2 .leaf .leaf)) (.fork 16 .leaf (.fork 2 .leaf .leaf)))) (.fork 7 (.fork 1 (.fork 16 .leaf (.fork 2 .leaf .leaf)) (.fork 16 .leaf .leaf)) (.fork 1 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf))))
theorem cert5 : check wt (cols 5) 1308 tree5 ∅ (rows 5) = true := by decide +kernel
def tree6 : BoundTree17393.Tree (Fin 19) := (.fork 15 (.fork 11 (.fork 3 .leaf (.fork 16 .leaf .leaf)) (.fork 3 (.fork 16 .leaf (.fork 4 .leaf .leaf)) (.fork 16 .leaf (.fork 4 .leaf .leaf)))) (.fork 11 (.fork 3 (.fork 16 .leaf (.fork 4 .leaf .leaf)) (.fork 16 .leaf .leaf)) (.fork 3 (.fork 16 .leaf .leaf) (.fork 16 .leaf .leaf))))
theorem cert6 : check wt (cols 6) 1308 tree6 ∅ (rows 6) = true := by decide +kernel
def tree7 : BoundTree17393.Tree (Fin 19) := (.fork 17 (.fork 7 (.fork 5 .leaf (.fork 18 .leaf .leaf)) (.fork 5 (.fork 18 .leaf (.fork 6 .leaf .leaf)) (.fork 18 .leaf (.fork 6 .leaf .leaf)))) (.fork 7 (.fork 5 (.fork 18 .leaf (.fork 6 .leaf .leaf)) (.fork 18 .leaf .leaf)) (.fork 5 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf))))
theorem cert7 : check wt (cols 7) 1308 tree7 ∅ (rows 7) = true := by decide +kernel
def tree8 : BoundTree17393.Tree (Fin 19) := (.fork 17 (.fork 11 (.fork 9 .leaf (.fork 18 .leaf .leaf)) (.fork 9 (.fork 18 .leaf (.fork 10 .leaf .leaf)) (.fork 18 .leaf (.fork 10 .leaf .leaf)))) (.fork 11 (.fork 9 (.fork 18 .leaf (.fork 10 .leaf .leaf)) (.fork 18 .leaf .leaf)) (.fork 9 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf))))
theorem cert8 : check wt (cols 8) 1308 tree8 ∅ (rows 8) = true := by decide +kernel
def tree9 : BoundTree17393.Tree (Fin 19) := (.fork 15 (.fork 17 (.fork 13 .leaf (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf))) (.fork 13 (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)) (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)))) (.fork 17 (.fork 13 (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)) (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf))) (.fork 13 (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)) (.fork 16 (.fork 18 .leaf .leaf) (.fork 18 .leaf .leaf)))))
theorem cert9 : check wt (cols 9) 1308 tree9 ∅ (rows 9) = true := by decide +kernel
def tree10 : BoundTree17393.Tree (Fin 19) := (.fork 7 (.fork 11 (.fork 17 (.fork 5 (.fork 9 .leaf .leaf) (.fork 9 .leaf (.fork 13 (.fork 15 .leaf .leaf) .leaf))) (.fork 5 (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 (.fork 15 .leaf .leaf) .leaf)))) (.fork 17 (.fork 5 (.fork 9 .leaf .leaf) (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 (.fork 15 .leaf .leaf) .leaf))) (.fork 5 (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 9 (.fork 13 (.fork 15 .leaf .leaf) .leaf) (.fork 13 (.fork 15 .leaf .leaf) .leaf))))) (.fork 11 (.fork 17 (.fork 5 (.fork 9 .leaf (.fork 13 .leaf .leaf)) (.fork 9 .leaf (.fork 13 (.fork 15 .leaf .leaf) .leaf))) (.fork 5 (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 (.fork 15 .leaf .leaf) .leaf)) (.fork 9 (.fork 13 .leaf .leaf) (.fork 13 (.fork 15 .leaf .leaf) .leaf)))) (.fork 17 (.fork 5 .leaf .leaf) (.fork 5 (.fork 9 (.fork 13 (.fork 15 .leaf .leaf) .leaf) (.fork 13 .leaf .leaf)) (.fork 9 (.fork 13 .leaf .leaf) .leaf)))))
theorem cert10 : check wt (cols 10) 1308 tree10 ∅ (rows 10) = true := by decide +kernel
def tree11 : BoundTree17393.Tree (Fin 19) := (.fork 7 (.fork 11 (.fork 15 (.fork 1 (.fork 3 .leaf .leaf) (.fork 3 .leaf (.fork 13 (.fork 17 .leaf .leaf) .leaf))) (.fork 1 (.fork 3 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 3 (.fork 13 .leaf .leaf) (.fork 13 (.fork 17 .leaf .leaf) .leaf)))) (.fork 15 (.fork 1 (.fork 3 .leaf .leaf) (.fork 3 (.fork 13 .leaf .leaf) (.fork 13 (.fork 17 .leaf .leaf) .leaf))) (.fork 1 (.fork 3 (.fork 13 .leaf .leaf) (.fork 13 .leaf .leaf)) (.fork 3 (.fork 13 (.fork 17 .leaf .leaf) .leaf) (.fork 13 (.fork 17 .leaf .leaf) .leaf))))) (.fork 11 (.fork 15 (.fork 1 (.fork 3 .leaf (.fork 13 .leaf .leaf)) (.fork 3 .leaf (.fork 13 (.fork 17 .leaf .leaf) .leaf))) (.fork 1 (.fork 3 (.fork 13 .leaf .leaf) (.fork 13 (.fork 17 .leaf .leaf) .leaf)) (.fork 3 (.fork 13 .leaf .leaf) (.fork 13 (.fork 17 .leaf .leaf) .leaf)))) (.fork 15 (.fork 1 .leaf .leaf) (.fork 1 (.fork 3 (.fork 13 (.fork 17 .leaf .leaf) .leaf) (.fork 13 .leaf .leaf)) (.fork 3 (.fork 13 .leaf .leaf) .leaf)))))
theorem cert11 : check wt (cols 11) 1308 tree11 ∅ (rows 11) = true := by decide +kernel
def certTree (i : Fin 12) := (#[tree0,tree1,tree2,tree3,tree4,tree5,tree6,tree7,tree8,tree9,tree10,tree11] : Array (BoundTree17393.Tree (Fin 19))).getD i.val .leaf
theorem all_checked (i : Fin 12) : check wt (cols i) 1308 (certTree i) ∅ (rows i)=true := by
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
  · exact cert11
theorem lower (f : Formula (Fin 12)) (ok : ∀ x,f.eval (lift x)=triangle x) : 22 ≤ f.leaves := by
  have atom (i : Fin 12) (rs : Finset (Fin 19)) (cs : Finset (Fin 19)) (hp : ∀ r∈rs,p r i=true) (hq : ∀ c∈cs,q c i=false) : mass wt rs cs ≤ 1308 := by
    apply checked wt (cols i) 1308 (certTree i) ∅ (rows i) rs cs (empty_subset _)
    · simp only [empty_union]
      exact fun r hr => mem_filter.mpr ⟨mem_univ _,hp r hr⟩
    · exact fun c hc => mem_filter.mpr ⟨mem_univ _,hq c hc⟩
    · exact all_checked i
  have h := weight_bound p q wt 1308 atom f univ univ
    (fun r _ => (ok _).trans (pos r)) (fun c _ => (ok _).trans (neg c))
  rw [total] at h
  omega
end PEqualNP.Research.Triangle17393.Adjacent
