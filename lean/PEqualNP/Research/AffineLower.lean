import PEqualNP.Research.AffineArea
import PEqualNP.Research.AffineRoutes

namespace PEqualNP.Research.AffineLower
open Finset PEqualNP.Research.AffineRectangleCover PEqualNP.Research.AffineArea PEqualNP.Research.AffineSymmetry

theorem area (A : Finset P) (B : Finset L) (good : ∀ p ∈ A, ∀ l ∈ B, zero p l = true) :
    A.card * B.card ≤ 54 := by
  by_cases small : B.card ≤ 1
  · have h := card_le_univ A
    have : A.card ≤ 25 := by simpa using h
    exact (Nat.mul_le_mul this small).trans (by decide)
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  let gs := route a b
  let f := move rowMap gs
  let g := move colMap gs
  have hf : Function.Injective f := move_inj rowMap (fun j _ _ => row_inj j _ _) gs
  have hg : Function.Injective g := move_inj colMap (fun j _ _ => col_inj j _ _) gs
  have h := anchored (g a) (g b) (normalize a b hab) (A.image f) (B.image g)
    (mem_image_of_mem g ha) (mem_image_of_mem g hb) (by
      intro p hp l hl
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hl
      exact (move_zero gs x y).trans (good x hx y hy))
  simpa [card_image_of_injective _ hf, card_image_of_injective _ hg] using h

def cells := (univ : Finset (P × L)).filter fun c => zero c.1 c.2
theorem count : cells.card = 600 := by decide +kernel
def unionCells : List Box → Finset (P × L)
  | [] => ∅
  | (a,b) :: t => (a ×ˢ b) ∪ unionCells t

theorem total (bs : List Box) (h : ∀ r ∈ bs, ∀ p ∈ r.1, ∀ l ∈ r.2, zero p l = true) :
    (unionCells bs).card ≤ bs.length * 54 := by
  induction bs with
  | nil => simp [unionCells]
  | cons r t ih =>
    obtain ⟨a,b⟩ := r
    have ha := area a b (h (a,b) (by simp))
    have ht := ih (fun r hr => h r (by simp [hr]))
    have hv := card_union_le (a ×ˢ b) (unionCells t)
    simp only [unionCells, List.length_cons, card_product] at *
    omega

theorem contains (bs : List Box) (r : Box) (hr : r∈bs) (p : P) (l : L) (hp : p∈r.1) (hl : l∈r.2) :
    (p,l) ∈ unionCells bs := by
  induction bs with
  | nil => simp at hr
  | cons b t ih =>
    rcases List.mem_cons.mp hr with eq | ht
    · subst r
      rcases b with ⟨a,b⟩
      exact mem_union_left _ (mem_product.mpr ⟨hp,hl⟩)
    · rcases b with ⟨a,b⟩
      exact mem_union_right _ (ih ht)

theorem lower (bs : List Box) (sound : ∀ r ∈ bs, ∀ p ∈ r.1, ∀ l ∈ r.2, zero p l = true)
    (complete : ∀ p l, zero p l = true → ∃ r∈bs, p∈r.1 ∧ l∈r.2) : 12 ≤ bs.length := by
  have h : cells ⊆ unionCells bs := by
    rintro ⟨p,l⟩ he
    obtain ⟨r,hr,hp,hl⟩ := complete p l (mem_filter.mp he).2
    exact contains bs r hr p l hp hl
  have hc := (card_le_card h).trans (total bs sound)
  rw [count] at hc
  omega
end PEqualNP.Research.AffineLower
