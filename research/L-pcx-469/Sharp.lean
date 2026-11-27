import Uniform
namespace SpinMass
open Finset
theorem single_iff {t : ℕ} (e : Pair t) (p : Mask t) :
    obs (some e) p ≠ obs none p ↔ p e.val.1 ≠ 0 ∧ p e.val.2 ≠ 0 := by
  have h := mass_identity (some e) p
  have h' := mass_identity none p
  have hn := rawprod_pos p
  change 4*obs (some e) p = 2*_ * factor (p e.val.1) (p e.val.2) at h
  change 4*obs none p = 2*_ * 4 at h'
  have he : obs (some e) p = obs none p ↔ factor (p e.val.1) (p e.val.2) = 4 := by
    calc
      _ ↔ 4*obs (some e) p = 4*obs none p := by omega
      _ ↔ _ := by rw [h,h']; exact Nat.mul_right_inj (Nat.mul_pos (by decide) hn).ne'
  rw [ne_eq,he]
  exact (by decide : ∀ a b, ¬factor a b = 4 ↔ a ≠ 0 ∧ b ≠ 0) _ _

theorem exact_distance {t : ℕ} (e : Pair t) :
    9 * dist (obs (some e)) (obs none) = 4 * 3^t := by
  unfold dist
  rw [support_sum e, dimensions e]
  have h (r : Away e → Fin 3) : (∑ x : Fin 3, ∑ y : Fin 3,
      if obs (some e) (fill e r x y) ≠ obs none (fill e r x y) then 1 else 0 : ℕ) = 4 := by
    simp only [single_iff]
    have h₁ (x y) : fill e r x y e.val.1 = x := by simp [fill]
    have h₂ (x y) : fill e r x y e.val.2 = y := by simp [fill,(ne_of_lt e.property).symm]
    simp_rw [h₁,h₂]
    decide
  simp only [h,sum_const,card_univ,nsmul_eq_mul]
  change 9*(Fintype.card (Away e → Fin 3)*4) = _
  ring
end SpinMass
