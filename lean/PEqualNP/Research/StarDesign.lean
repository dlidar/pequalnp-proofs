import PEqualNP.Research.L_meta_1980_cap_boundary
import PEqualNP.Research.StarCodeBound

namespace PEqualNP.Research.StarDesign
open Finset PEqualNP.Research.CapBoundary PEqualNP.Research.StarCodeBound

def rowHit (x : Word) (a b : V) := (a∈pts x ∨ b∈pts x) ∧ ∃ l∈lines x,inc a l ∨ inc b l
def colHit (x : Word) (a b : V) := (a∈lines x ∨ b∈lines x) ∧ ∃ p∈pts x,inc p a ∨ inc p b
instance (x a b) : Decidable (rowHit x a b) := by unfold rowHit;infer_instance
instance (x a b) : Decidable (colHit x a b) := by unfold colHit;infer_instance

theorem row_separates {x a b} (gen : Generic x) (hit : rowHit x a b) :
    ¬ (a∈pts x ↔ b∈pts x) := by
  rintro same
  obtain ⟨one,l,hl,e⟩ := hit
  have both : a∈pts x ∧ b∈pts x := one.elim (fun h => ⟨h,same.mp h⟩) (fun h => ⟨same.mpr h,h⟩)
  exact e.elim (gen.1 a both.1 l hl) (gen.1 b both.2 l hl)

theorem col_separates {x a b} (gen : Generic x) (hit : colHit x a b) :
    ¬ (a∈lines x ↔ b∈lines x) := by
  rintro same
  obtain ⟨one,p,hp,e⟩ := hit
  have both : a∈lines x ∧ b∈lines x := one.elim (fun h => ⟨h,same.mp h⟩) (fun h => ⟨same.mpr h,h⟩)
  exact e.elim (gen.1 p hp a both.1) (gen.1 p hp b both.2)

theorem capacity (x : Word) (g : Generic x) : (pts x).card+(lines x).card ≤ 7 := by
  obtain ⟨y,hy,xy⟩ := (exact_boundary x).mp g
  have p := card_le_card (point_subset xy)
  have l := card_le_card (line_subset xy)
  rcases (sizes y hy).2 with eq|eq <;> omega

/-- Five legal negative tests leave at least one pair merger without a distinguishing row. -/
theorem five_insufficient (r : Fin 5 → Word) (g : ∀ i,Generic (r i)) :
    (∃ a b : V,a≠b ∧ ∀ i,¬rowHit (r i) a b) ∨
    (∃ a b : V,a≠b ∧ ∀ i,¬colHit (r i) a b) := by
  rcases collision (fun j => pts (r j)) (fun j => lines (r j)) (fun j => capacity _ (g j)) with h|h
  · left; unfold Function.Injective at h; push_neg at h
    obtain ⟨a,b,same,ne⟩ := h
    refine ⟨a,b,ne,?_⟩
    intro i hit
    have eq := Finset.ext_iff.mp same i
    exact row_separates (g i) hit (by simpa [profile] using eq)
  · right; unfold Function.Injective at h; push_neg at h
    obtain ⟨a,b,same,ne⟩ := h
    refine ⟨a,b,ne,?_⟩
    intro i hit
    have eq := Finset.ext_iff.mp same i
    exact col_separates (g i) hit (by simpa [profile] using eq)

def design : List Word := [9703956,33858704,52445288,4352320,29360412,2790402]
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

end PEqualNP.Research.StarDesign
