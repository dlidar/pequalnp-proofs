import Mathlib.Tactic

namespace PEqualNP.Research.UniversalInverterRepair

variable {X : Type*} [Preorder X]

/-- A suffix can use every original input and the output of the inverter. -/
def Safe (f d r : X → Bool) := ∀ F : X → Bool → Bool,
    (∀ x y, x ≤ y → ∀ a b, a ≤ b → F x a ≤ F y b) →
    (∀ x, F x (!d x) = f x) → ∀ x, F x (r x) = f x

def Fits (f d r : X → Bool) :=
  (∀ x, f x = true → d x = false → r x = true) ∧
  (∀ x, f x = false → d x = true → r x = false)

theorem safe_of_fits {f d r : X → Bool} (h : Fits f d r) : Safe f d r := by
  intro F hm orig x
  have mb := hm x x le_rfl false true (by decide)
  specialize orig x
  cases hf : f x <;> cases hd : d x <;> cases hr : r x <;>
    simp_all [Fits,Bool.le_iff_imp]

theorem fits_of_safe {f d r : X → Bool} (hf : Monotone f) (hd : Monotone d) (h : Safe f d r) :
    Fits f d r := by
  classical
  constructor
  · intro x fx dx
    let F (y : X) (z : Bool) := f y && (z || decide (¬ y ≤ x))
    have mono : ∀ a b, a ≤ b → ∀ i j, i ≤ j → F a i ≤ F b j := by
      intro a b ab i j ij
      simp only [F,Bool.le_iff_imp,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at *
      rintro ⟨ha, hi | hn⟩
      · exact ⟨Bool.le_iff_imp.mp (hf ab) ha, Or.inl (ij hi)⟩
      · exact ⟨Bool.le_iff_imp.mp (hf ab) ha, Or.inr (fun hb => hn (ab.trans hb))⟩
    have orig (y : X) : F y (!d y) = f y := by
      by_cases hy : y ≤ x
      · have dy := Bool.eq_false_of_le_false ((hd hy).trans (by rw [dx]))
        simp [F,dy]
      · simp [F,hy]
    simpa [F,fx] using h F mono orig x
  · intro x fx dx
    let F (y : X) (z : Bool) := f y || (z && decide (x ≤ y))
    have mono : ∀ a b, a ≤ b → ∀ i j, i ≤ j → F a i ≤ F b j := by
      intro a b ab i j ij
      simp only [F,Bool.le_iff_imp,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at *
      rintro (ha | ⟨hi,hn⟩)
      · exact Or.inl (Bool.le_iff_imp.mp (hf ab) ha)
      · exact Or.inr ⟨ij hi, hn.trans ab⟩
    have orig (y : X) : F y (!d y) = f y := by
      by_cases hy : x ≤ y
      · have dy := Bool.eq_true_of_true_le ((by rw [dx] : true ≤ d x).trans (hd hy))
        simp [F,dy]
      · simp [F,hy]
    simpa [F,fx] using h F mono orig x

theorem safe_iff {f d r : X → Bool} (hf : Monotone f) (hd : Monotone d) :
    Safe f d r ↔ Fits f d r := ⟨fits_of_safe hf hd, safe_of_fits⟩

end PEqualNP.Research.UniversalInverterRepair
