import PEqualNP.Research.SingletonProfiles
import PEqualNP.Research.FlagSamples

namespace PEqualNP.Research.CombinedDesign
open Finset PEqualNP.Research.CapBoundary PEqualNP.Research.StarDesign

def design : List Word := [2458753, 9449524, 4751635, 25363204, 162112, 34475016]
theorem design_legal : ∀ x ∈ design, Generic x := by
  have h : design.all (fun x => decide (Generic x)) = true := by decide +kernel
  exact fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)
theorem design_size : design.length=6 ∧ design.Nodup := by decide +kernel
theorem row_cover : ∀ a b : V,a≠b → ∃ x∈design,rowHit x a b := by
  intro a b ab
  have cert : ∀ i j : V,i≠j → design.any (fun x => decide (rowHit x i j))=true := by decide +kernel
  obtain ⟨x,hx,hit⟩ := List.any_eq_true.mp (cert a b ab)
  exact ⟨x,hx,of_decide_eq_true hit⟩
theorem col_cover : ∀ a b : V,a≠b → ∃ x∈design,colHit x a b := by
  intro a b ab
  have cert : ∀ i j : V,i≠j → design.any (fun x => decide (colHit x i j))=true := by decide +kernel
  obtain ⟨x,hx,hit⟩ := List.any_eq_true.mp (cert a b ab)
  exact ⟨x,hx,of_decide_eq_true hit⟩


theorem points_covered : ∀ p : V, ∃ x∈design,p∈pts x := by
  intro p
  have all : ∀ p : V, design.any (fun x => decide (p∈pts x))=true := by decide +kernel
  obtain ⟨x,hx,hp⟩ := List.any_eq_true.mp (all p)
  exact ⟨x,hx,of_decide_eq_true hp⟩

theorem lines_covered : ∀ l : V, ∃ x∈design,l∈lines x := by
  intro l
  have all : ∀ l : V, design.any (fun x => decide (l∈lines x))=true := by decide +kernel
  obtain ⟨x,hx,hl⟩ := List.any_eq_true.mp (all l)
  exact ⟨x,hx,of_decide_eq_true hl⟩

end PEqualNP.Research.CombinedDesign
