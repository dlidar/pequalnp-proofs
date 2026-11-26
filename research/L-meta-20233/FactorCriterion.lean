import Mathlib

namespace SplitMonotoneFactor

variable {A X Y : Type*} [Preorder X] [Preorder Y]

def Need (right : A → Y) (P : A → Prop) (a b : A) : Prop :=
  P a ∧ ¬ P b ∧ right a ≤ right b

def Factors (left : A → X) (right : A → Y) (P : A → Prop) : Prop :=
  ∃ f : X → Prop, Monotone f ∧
    ∃ g : Y × Prop → Prop, Monotone g ∧ ∀ a, g (right a, f (left a)) ↔ P a

theorem four_row_criterion (left : A → X) (right : A → Y) (P : A → Prop) :
    Factors left right P ↔
      ∀ a b c d, Need right P a b → Need right P c d → ¬ left a ≤ left d := by
  constructor
  · rintro ⟨f, hf, g, hg, fit⟩
    have forces (a b : A) (h : Need right P a b) : f (left a) ∧ ¬ f (left b) := by
      have hsep : ¬ (f (left a) → f (left b)) := by
        intro hi
        have hle : (right a, f (left a)) ≤ (right b, f (left b)) := ⟨h.2.2, hi⟩
        exact h.2.1 ((fit b).mp ((hg hle) ((fit a).mpr h.1)))
      tauto
    exact fun a b c d hab hcd had => (forces c d hcd).2 ((hf had) (forces a b hab).1)
  · intro clean
    let f (x : X) : Prop := ∃ a b, Need right P a b ∧ left a ≤ x
    have hf : Monotone f := by
      rintro x z hx ⟨a, b, hab, hax⟩
      exact ⟨a, b, hab, hax.trans hx⟩
    let g (z : Y × Prop) : Prop :=
      ∃ a, P a ∧ right a ≤ z.1 ∧ (f (left a) → z.2)
    have hg : Monotone g := by
      rintro x z hx ⟨a, ha, hay, hax⟩
      exact ⟨a, ha, hay.trans hx.1, fun h => hx.2 (hax h)⟩
    refine ⟨f, hf, g, hg, fun d => ⟨?_, ?_⟩⟩
    · rintro ⟨c, hc, hcd, transfer⟩
      by_contra hd
      have req : Need right P c d := ⟨hc, hd, hcd⟩
      obtain ⟨a, b, hab, had⟩ := transfer ⟨c, d, req, le_rfl⟩
      exact clean a b c d hab req had
    · exact fun hd => ⟨d, hd, le_rfl, id⟩

end SplitMonotoneFactor

#print axioms SplitMonotoneFactor.four_row_criterion
