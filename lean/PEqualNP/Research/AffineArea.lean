import PEqualNP.Research.AffineMatrix

namespace PEqualNP.Research.AffineArea
open Finset PEqualNP.Research.AffineRectangleCover
def test : List P → Finset L → Nat → Bool
  | [], s, k => decide (k * s.card ≤ 54)
  | a :: t, s, k => decide ((k + t.length + 1) * s.card ≤ 54) ||
      (test t s k && test t (s.filter (fun l => zero a l)) (k+1))

theorem test_sound (t : List P) (s : Finset L) (k : Nat) (ok : test t s k = true)
    (A : Finset P) (B : Finset L) (ha : A ⊆ t.toFinset) (hb : B ⊆ s)
    (good : ∀ a ∈ A, ∀ b ∈ B, zero a b = true) : (k + A.card) * B.card ≤ 54 := by
  induction t generalizing s k A with
  | nil =>
    have hh : A = ∅ := by simpa using ha
    simp [hh] at *
    exact (Nat.mul_le_mul_left k (card_le_card hb)).trans (of_decide_eq_true ok)
  | cons a t ih =>
    simp only [test, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at ok
    rcases ok with h | ⟨h₁,h₂⟩
    · have hcard := (card_le_card ha).trans (List.toFinset_card_le _)
      simp only [List.length_cons] at hcard
      exact (Nat.mul_le_mul (by omega) (card_le_card hb)).trans h
    · by_cases h : a ∈ A
      · have ha' : A.erase a ⊆ t.toFinset := by
          intro x hx
          have v := ha (mem_of_mem_erase hx)
          simpa [List.toFinset_cons, ne_of_mem_erase hx] using v
        have hb' : B ⊆ s.filter (fun l => zero a l) := fun l hl =>
          mem_filter.mpr ⟨hb hl, good a h l hl⟩
        have v := ih _ _ h₂ (A.erase a) ha' hb' (fun x hx => good x (mem_of_mem_erase hx))
        have hh := card_erase_add_one h
        convert v using 2 <;> omega
      · apply ih _ _ h₁ A _ hb good
        intro x hx
        have v := ha hx
        have hn : x ≠ a := fun he => h (he ▸ hx)
        simpa [List.toFinset_cons, hn] using v

def allowedRows (a b : L) := (List.finRange 25).filter fun p => zero p a && zero p b
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
theorem parallel_test : test (allowedRows 25 26) univ 0 = true := by decide +kernel
theorem crossing_test : test (allowedRows 0 25) univ 0 = true := by decide +kernel

theorem anchored (a b : L) (can : (a=25 ∧ b=26) ∨ (a=0 ∧ b=25))
    (A : Finset P) (B : Finset L) (ha : a∈B) (hb : b∈B)
    (good : ∀ p ∈ A, ∀ l ∈ B, zero p l = true) : A.card * B.card ≤ 54 := by
  have ok : test (allowedRows a b) univ 0 = true := by
    rcases can with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact parallel_test
    · exact crossing_test
  have h := test_sound _ _ _ ok A B (by
    intro p hp
    simp [allowedRows, good p hp a ha, good p hp b hb]) (subset_univ _) good
  simpa using h
end PEqualNP.Research.AffineArea
