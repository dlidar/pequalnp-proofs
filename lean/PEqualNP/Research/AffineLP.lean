import PEqualNP.Research.AffineLower
import PEqualNP.Research.AffineFractional

namespace PEqualNP.Research.AffineLP
open Finset PEqualNP.Research.AffineRectangleCover PEqualNP.Research.AffineLower
open PEqualNP.Research.AffineFractional
abbrev Cell := P × L
def rect (b : Box) : Finset Cell := b.1 ×ˢ b.2
def Sound (b : Box) := ∀ p ∈ b.1, ∀ l ∈ b.2, zero p l = true
def cost {n : Nat} (weight : Fin n → ℚ) := ∑ k, weight k
def mass {n : Nat} (R : Fin n → Box) (weight : Fin n → ℚ) (c : Cell) :=
  ∑ k, if c ∈ rect (R k) then weight k else 0

theorem mass_bound {n : Nat} (R : Fin n → Box) (wt : Fin n → ℚ)
    (nn : ∀ k, 0 ≤ wt k) (hs : ∀ k, Sound (R k))
    (hc : ∀ c ∈ cells, 1 ≤ mass R wt c) : 100/9 ≤ cost wt := by
  have hcard (k : Fin n) : (cells.filter (fun c => c ∈ rect (R k))).card ≤ 54 := by
    apply le_trans (card_le_card (show cells.filter (fun c => c ∈ rect (R k)) ⊆ rect (R k) from fun c h => (mem_filter.mp h).2))
    simpa [rect] using area (R k).1 (R k).2 (hs k)
  have term (k : Fin n) : (∑ c ∈ cells, if c ∈ rect (R k) then wt k else 0) ≤ 54 * wt k := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard k) (nn k)
  have h : (600 : ℚ) ≤ 54 * cost wt := calc
    (600 : ℚ) = ∑ _c ∈ cells, (1 : ℚ) := by simp [count]
    _ ≤ ∑ c ∈ cells, mass R wt c := sum_le_sum hc
    _ = ∑ k, ∑ c ∈ cells, if c ∈ rect (R k) then wt k else 0 := sum_comm
    _ ≤ ∑ k, 54 * wt k := sum_le_sum (fun k _ => term k)
    _ = 54 * cost wt := by simp [cost, mul_sum]
  linarith

def member (k : Fin 100) := boxes[k.val]!
def basis (k : Fin 100) : Box :=
  (univ.filter (fun p => (member k).1.testBit p.val),univ.filter (fun l => (member k).2.testBit l.val))
def copies (p : P) (l : L) := (univ.filter (fun k : Fin 100 => hits p l (member k))).card

set_option maxRecDepth 80000
set_option maxHeartbeats 8000000

theorem basis_sound (k : Fin 100) : Sound (basis k) := by
  intro p hp l hl
  have h := mem_filter.mp hp
  have t := mem_filter.mp hl
  have safe : ∀ (k : Fin 100) (p : P) (l : L), hits p l (member k) = true → zero p l = true := by decide +kernel
  exact safe k p l (by simp [hits, h.2, t.2])

theorem mem_basis (k : Fin 100) (p : P) (l : L) :
    (p,l) ∈ rect (basis k) ↔ hits p l (member k) = true := by simp [rect,basis,hits]
private theorem count0 : ∀ l : L, copies 0 l = if zero 0 l then 9 else 0 := by decide +kernel
private theorem count1 : ∀ l : L, copies 1 l = if zero 1 l then 9 else 0 := by decide +kernel
private theorem count2 : ∀ l : L, copies 2 l = if zero 2 l then 9 else 0 := by decide +kernel
private theorem count3 : ∀ l : L, copies 3 l = if zero 3 l then 9 else 0 := by decide +kernel
private theorem count4 : ∀ l : L, copies 4 l = if zero 4 l then 9 else 0 := by decide +kernel
private theorem count5 : ∀ l : L, copies 5 l = if zero 5 l then 9 else 0 := by decide +kernel
private theorem count6 : ∀ l : L, copies 6 l = if zero 6 l then 9 else 0 := by decide +kernel
private theorem count7 : ∀ l : L, copies 7 l = if zero 7 l then 9 else 0 := by decide +kernel
private theorem count8 : ∀ l : L, copies 8 l = if zero 8 l then 9 else 0 := by decide +kernel
private theorem count9 : ∀ l : L, copies 9 l = if zero 9 l then 9 else 0 := by decide +kernel
private theorem count10 : ∀ l : L, copies 10 l = if zero 10 l then 9 else 0 := by decide +kernel
private theorem count11 : ∀ l : L, copies 11 l = if zero 11 l then 9 else 0 := by decide +kernel
private theorem count12 : ∀ l : L, copies 12 l = if zero 12 l then 9 else 0 := by decide +kernel
private theorem count13 : ∀ l : L, copies 13 l = if zero 13 l then 9 else 0 := by decide +kernel
private theorem count14 : ∀ l : L, copies 14 l = if zero 14 l then 9 else 0 := by decide +kernel
private theorem count15 : ∀ l : L, copies 15 l = if zero 15 l then 9 else 0 := by decide +kernel
private theorem count16 : ∀ l : L, copies 16 l = if zero 16 l then 9 else 0 := by decide +kernel
private theorem count17 : ∀ l : L, copies 17 l = if zero 17 l then 9 else 0 := by decide +kernel
private theorem count18 : ∀ l : L, copies 18 l = if zero 18 l then 9 else 0 := by decide +kernel
private theorem count19 : ∀ l : L, copies 19 l = if zero 19 l then 9 else 0 := by decide +kernel
private theorem count20 : ∀ l : L, copies 20 l = if zero 20 l then 9 else 0 := by decide +kernel
private theorem count21 : ∀ l : L, copies 21 l = if zero 21 l then 9 else 0 := by decide +kernel
private theorem count22 : ∀ l : L, copies 22 l = if zero 22 l then 9 else 0 := by decide +kernel
private theorem count23 : ∀ l : L, copies 23 l = if zero 23 l then 9 else 0 := by decide +kernel
private theorem count24 : ∀ l : L, copies 24 l = if zero 24 l then 9 else 0 := by decide +kernel
theorem counts (p : P) (l : L) : copies p l = if zero p l then 9 else 0 := by
  fin_cases p
  · exact count0 l
  · exact count1 l
  · exact count2 l
  · exact count3 l
  · exact count4 l
  · exact count5 l
  · exact count6 l
  · exact count7 l
  · exact count8 l
  · exact count9 l
  · exact count10 l
  · exact count11 l
  · exact count12 l
  · exact count13 l
  · exact count14 l
  · exact count15 l
  · exact count16 l
  · exact count17 l
  · exact count18 l
  · exact count19 l
  · exact count20 l
  · exact count21 l
  · exact count22 l
  · exact count23 l
  · exact count24 l

theorem basis_mass (c : Cell) (hc : c ∈ cells) : mass basis (fun _ => 1/9) c = 1 := by
  rcases c with ⟨p,l⟩
  have he := (mem_filter.mp hc).2
  simp only [mass, mem_basis, ← sum_filter, sum_const, nsmul_eq_mul]
  change (copies p l : ℚ) * (1/9) = 1
  rw [counts, he]
  norm_num
theorem attained : (∀ k, Sound (basis k)) ∧
    (∀ c ∈ cells, 1 ≤ mass basis (fun _ => 1/9) c) ∧ cost (n:=100) (fun _ => 1/9) = 100/9 := by
  refine ⟨basis_sound,fun c hc => (basis_mass c hc).ge,?_⟩
  norm_num [cost]
end PEqualNP.Research.AffineLP
