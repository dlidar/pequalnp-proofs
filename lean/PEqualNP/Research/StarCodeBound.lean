import Mathlib

namespace PEqualNP.Research.StarCodeBound
open Finset
abbrev Code := Finset (Fin 5)

theorem small_bins : ((univ : Finset Code).filter fun S => S.card ≤ 1).card=6 ∧
    ((univ : Finset Code).filter fun S => S.card=0).card=1 := by decide +kernel

theorem no_collisions (code : Fin 13 → Code) (inj : Function.Injective code) :
    19 ≤ ∑ i, (code i).card := by
  have small (P : Code → Prop) [DecidablePred P] :
      (univ.filter fun i : Fin 13 => P (code i)).card ≤ (univ.filter P).card := by
    rw [←card_image_of_injective _ inj]
    apply card_le_card
    rintro _ h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  have lo := small (fun S => S.card ≤ 1)
  have nil := small (fun S => S.card=0)
  rw [small_bins.1] at lo;rw [small_bins.2] at nil
  have point (i : Fin 13) : 2 ≤ (code i).card + (if (code i).card≤1 then 1 else 0) +
      (if (code i).card=0 then 1 else 0) := by split <;> split <;> omega
  have s := sum_le_sum (s:=univ) (fun i _ => point i)
  simp only [sum_add_distrib,sum_boole] at s
  have n : ∑ _ : Fin 13, (2:ℕ) = 26 := by decide
  rw [n] at s; norm_cast at s; omega

def profile (test : Fin 5 → Finset (Fin 13)) (v : Fin 13) : Code := univ.filter fun j => v ∈ test j

theorem transpose (test : Fin 5 → Finset (Fin 13)) :
    ∑ v, (profile test v).card = ∑ j, (test j).card := by
  simp only [profile,card_filter]
  rw [sum_comm]
  simp

theorem collision (P L : Fin 5 → Finset (Fin 13)) (bound : ∀ j,(P j).card+(L j).card ≤ 7) :
    ¬Function.Injective (profile P) ∨ ¬Function.Injective (profile L) := by
  by_contra! h
  have p := no_collisions _ h.1
  have l := no_collisions _ h.2
  rw [transpose] at p l
  have sum := sum_le_sum (s:=univ) (fun j _ => bound j)
  have n : ∑ _ : Fin 5, (7:ℕ) = 35 := by decide
  rw [sum_add_distrib,n] at sum
  omega

end PEqualNP.Research.StarCodeBound
