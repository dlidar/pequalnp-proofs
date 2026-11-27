import Winners
namespace SpinCircuit
open Finset SpinHash SpinMass
variable {t b k H I : ℕ}
def batch (f : Fin H → Label t b) (m : Fin I → Mask b) (i : Fin (H*I)) : Mask t :=
  let z := finProdFinEquiv.symm i
  m z.2 ∘ f z.1

theorem flat_sum (F : Fin (H*I) → ℕ) : ∑ i, F i = ∑ h : Fin H, ∑ j : Fin I, F (finProdFinEquiv (h,j)) := by
  rw [← finProdFinEquiv.sum_comp F, Fintype.sum_prod_type]

def fullW (k t : ℕ) := k*(2*t+2)+1

theorem lost_rows (W : ℕ) (y : Packet (H*I)) :
    totalLost (rows W y) = (univ.filter (fun i => y i = none)).card := by
  have h := sum_boole (R:=ℕ) (fun i => y i=none) univ
  rw [Nat.cast_id,flat_sum] at h
  simpa [totalLost, rows, erasures,clip] using h

theorem error_rows (f : Fin H → Label t b) (m : Fin I → Mask b) (G : Model t k) (y : Packet (H*I)) :
    totalErrors f m G (rows (fullW k t) y) ≤ (univ.filter (fun i =>
      y i ≠ none ∧ y i ≠ some (reading G (batch f m i)))).card := by
  have h := sum_boole (R:=ℕ) (fun i => y i ≠ none ∧ y i ≠ some (reading G (batch f m i))) univ
  rw [Nat.cast_id,flat_sum] at h
  rw [←h];apply sum_le_sum;intro i _
  unfold cost
  apply sum_le_sum;intro j _
  let index := finProdFinEquiv (i,j)
  have hb : reading G (batch f m index) < 2^fullW k t := reading_bound _ _
  have hv : batch f m index = m j ∘ f i := by simp [batch,index]
  change (if clip (fullW k t) (y index) ≠ none ∧ clip (fullW k t) (y index) ≠ some (reading G (m j ∘ f i)) then 1 else 0) ≤
    if y index ≠ none ∧ y index ≠ some (reading G (batch f m index)) then 1 else 0
  rw [hv] at hb ⊢
  by_cases hl : y index = none
  · simp [hl,clip]
  · by_cases hh : y index = some (reading G (m j ∘ f i))
    · simp [hh,clip,Nat.mod_eq_of_lt hb]
    · simp [hl,hh];split <;> decide

theorem winning_value (f : Fin H → Label t b) (m : Fin I → Mask b) (G : Model t k) (e : Pair t)
    (W : ℕ) (y : Packet (H*I))
    (h : ∀ a, a ≠ mult G e → totalPrice k f m e (mult G e) (rows W y) < totalPrice k f m e a (rows W y))
    (a : Fin (k+1)) : winner (W:=W) f m e a y ↔ mult G e = a.val := by
  constructor
  · intro hw
    by_contra hn
    have hh := h a.val (fun hz => hn hz.symm)
    have hcap : mult G e ≤ k := by simpa [mult] using card_filter_le univ (fun l => G l=some e)
    have hle := hw ⟨mult G e,by omega⟩
    exact (not_lt_of_ge hle) hh
  · intro ha a'
    by_cases hn : a'.val = mult G e
    · rw [hn,ha]
    · exact ha ▸ (h a'.val hn).le
end SpinCircuit
