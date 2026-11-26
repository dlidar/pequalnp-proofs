import PEqualNP.Research.Dominating3321
import PEqualNP.Research.SixCofactors3321

namespace PEqualNP.Research.Theta3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Research.GateCuts3321 PEqualNP.Research.SixCofactors3321
open PEqualNP.Research.Dominating3321

def internal : Finset ℕ := {1,2,3,5,6,7}

theorem relabel_lower {n k} (f g : Fn n) (π : Fin n → Fin n) (low : Lower g k)
    (ev : ∀ x, f (x ∘ π) = g x) : Lower f k := by
  intro s hs
  have h := Helpers.PermInputs.relabel_size π _ _ hs
  rw [show (fun x => f (x ∘ π)) = g from funext ev] at h
  exact low s h

set_option maxRecDepth 8000
set_option maxHeartbeats 3000000

theorem isolated_lower (v : Fin 8) (mem : v.val ∈ internal) : Lower (cut graph13726 v false) 9 := by
  fin_cases v
  · exact False.elim ((by decide : _ ∉ internal) mem)
  · exact relabel_lower _ graph13726_0 ![0,1,2,3,4,5,6,7] lower_graph13726_0 (by decide +kernel)
  · exact relabel_lower _ graph13726_0 ![0,2,1,3,4,5,7,6] lower_graph13726_0 (by decide +kernel)
  · exact relabel_lower _ graph13726_0 ![0,2,3,1,4,7,5,6] lower_graph13726_0 (by decide +kernel)
  · exact False.elim ((by decide : _ ∉ internal) mem)
  · exact relabel_lower _ graph13726_0 ![4,5,6,7,0,1,2,3] lower_graph13726_0 (by decide +kernel)
  · exact relabel_lower _ graph13726_0 ![4,5,7,6,0,2,1,3] lower_graph13726_0 (by decide +kernel)
  · exact relabel_lower _ graph13726_0 ![4,7,5,6,0,2,3,1] lower_graph13726_0 (by decide +kernel)

theorem theta_lower (C : Circuit) (mono : Monotone2 C) (ev : ∀ x, C.eval (List.ofFn x) = graph13726 x) :
    11 ≤ C.size := by
  apply gain internal graph13726 (k:=9) (by exact ⟨1,by decide⟩) (by decide) _ _ _ isolated_lower C mono ev
  · unfold cut centers internal;decide +kernel
  · unfold cut internal;decide +kernel
  · unfold cut internal;decide +kernel

end PEqualNP.Research.Theta3321
