import ClonePin
import CloneLift

open PEqualNP.Represents PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Mask114591Family Mask114591ClonePin Mask114591CloneLift

namespace Mask114591CloneCosts

/-- Duplicating a column costs exactly one monotone gate whenever a row
accepts that column and rejects another column. -/
theorem duplicate_budget {n m : Nat} (A : Fin n → Fin m → Bool) (p : Fin m) (t : Nat)
    (diff : ∃ u v, A u p = true ∧ A u v = false) :
    RepSizeAtMost (fun u v => A u (projectLast p v)) (t+1) ↔ RepSizeAtMost A t := by
  constructor
  · rintro ⟨C,hc,sz,hr⟩
    obtain ⟨u,v,ht,hf⟩ := diff
    obtain ⟨D,hd,hs,rep⟩ := delete_column (A := A)
      (B := fun u v => A u (projectLast p v))
      (fun u v => by simp [projectLast,v.isLt])
      ⟨u,v,by simpa [projectLast] using ht,hf⟩ ⟨u,p,ht⟩ hc hr
    exact ⟨D,hd,by omega,rep⟩
  · rintro ⟨C,hc,sz,hr⟩
    exact ⟨_,lift_mono _ _ hc,by rw [lift_size]; omega,lift_rep p hr⟩

theorem extend_old (k : Nat) (u : Fin 4) (v : Fin (5+k)) :
    clone (k+1) u ⟨v.val,by omega⟩ = clone k u v := by
  simp only [clone,project]

theorem extend_last (k : Nat) (u : Fin 4) :
    clone (k+1) u (Fin.last (5+k)) = base u 2 := by simp [clone,project]

theorem cloned_projection (k : Nat) (u : Fin 4) (v : Fin (5+(k+1))) :
    clone (k+1) u v = clone k u (projectLast (⟨2,by omega⟩ : Fin (5+k)) v) := by
  dsimp [projectLast]
  split_ifs with hv
  · exact extend_old k u ⟨v.val,hv⟩
  · have hlarge : ¬v.val < 5 := by omega
    simp [clone,project,hlarge]

theorem cloned_budget (k t : Nat) :
    RepSizeAtMost (clone k) (t+k) ↔ RepSizeAtMost base t := by
  induction k with
  | zero =>
    have eq : clone 0 = base := by
      funext u v
      simp [clone,project,v.isLt]
    simp [eq]
  | succ k ih =>
    rw [← ih]
    constructor
    · rintro ⟨C,hc,sz,hr⟩
      have w : ∃ u v, clone (k+1) u (Fin.last (5+k)) = true ∧ clone k u v = false := by
        refine ⟨(1 : Fin 4),⟨0,by omega⟩,?_,?_⟩
        · rw [extend_last];decide
        · simp [clone,project,base]; decide
      have oth : ∃ u v, clone k u v = true := by
        refine ⟨(0 : Fin 4),⟨0,by omega⟩,?_⟩
        simp [clone,project,base]
      obtain ⟨D,hd,hs,rep⟩ := delete_column (extend_old k) w oth hc hr
      exact ⟨D,hd,by omega,rep⟩
    · rintro ⟨C,hc,sz,hr⟩
      let p : Fin (5+k) := ⟨2,by omega⟩
      refine ⟨lift (4+(5+k)) (4+p.val) C,lift_mono _ _ hc,?_,?_⟩
      · rw [lift_size];omega
      · intro u v
        rw [cloned_projection]
        exact lift_rep p hr u v

end Mask114591CloneCosts
#print axioms Mask114591CloneCosts.cloned_budget
#print axioms Mask114591CloneCosts.duplicate_budget
