import PEqualNP.Research.AffineMatrix
namespace PEqualNP.Research.AffineFooling
open Finset PEqualNP.Research.AffineRectangleCover
abbrev V := Fin 8
abbrev E := Fin 28
def left (e : E) : V := (#[0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 5, 5, 6] : Array V)[e.val]!
def right (e : E) : V := (#[1, 2, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 7, 3, 4, 5, 6, 7, 4, 5, 6, 7, 5, 6, 7, 6, 7, 7] : Array V)[e.val]!
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
theorem distinct_ends : ∀ e : E, left e ≠ right e := by decide +kernel
theorem unique_line : ∀ a b : P, a ≠ b →
    ((univ : Finset L).filter (fun l => !zero a l && !zero b l)).card ≤ 1 := by decide +kernel
def cross (S : Finset V) (k : V) (e : E) : Bool :=
  (k == left e && decide (right e ∈ S)) || (k == right e && decide (left e ∈ S))
def both (S : Finset V) (e : E) : Bool := decide (left e ∈ S ∧ right e ∈ S)
def num (h : E → Bool) : Nat := ∑ e, if h e then 1 else 0
-- A column containing d of eight rows contributes at most d cross edges
-- and contains all pairs among those rows.
theorem local_count : ∀ (S : Finset V) (k : V), 3 * num (cross S k) ≤ 6 + num (both S) := by decide +kernel

theorem no_eight (row : V → P) (col : V → L) (hr : Function.Injective row) (hl : Function.Injective col)
    (op : ∀ i j : V, i ≠ j → zero (row i) (col j) = false ∨ zero (row j) (col i) = false) : False := by
  let S (k : V) := univ.filter (fun i : V => !(zero (row i) (col k)))
  have one (e : E) : 1 ≤ ∑ k : V, if cross (S k) k e then 1 else 0 := by
    obtain h | h := op (left e) (right e) (distinct_ends e)
    · have he : cross (S (right e)) (right e) e = true := by simp [cross,S,h]
      exact le_trans (show 1 ≤ (if cross (S (right e)) (right e) e then 1 else 0) by simp [he])
        (single_le_sum (f := fun k : V => if cross (S k) k e then 1 else 0) (fun _ _ => Nat.zero_le _) (mem_univ _))
    · have he : cross (S (left e)) (left e) e = true := by simp [cross,S,h]
      exact le_trans (show 1 ≤ (if cross (S (left e)) (left e) e then 1 else 0) by simp [he])
        (single_le_sum (f := fun k : V => if cross (S k) k e then 1 else 0) (fun _ _ => Nat.zero_le _) (mem_univ _))
  have atMost (e : E) : (∑ k : V, if both (S k) e then 1 else 0) ≤ 1 := by
    rw [← sum_filter]; simp only [sum_const, nsmul_one]
    apply card_le_one.mpr
    intro a ha b hb
    have ha' := (mem_filter.mp ha).2
    have hb' := (mem_filter.mp hb).2
    simp [both, S] at ha' hb'
    apply hl
    apply card_le_one.mp (unique_line _ _ (fun eq => distinct_ends e (hr eq)))
    · simp [ha'.1,ha'.2]
    · simp [hb'.1,hb'.2]
  have low : 28 ≤ ∑ k : V, num (cross (S k) k) := calc
    28 = ∑ _ : E, 1 := by simp
    _ ≤ ∑ e : E, ∑ k : V, if cross (S k) k e then 1 else 0 := sum_le_sum (fun e _ => one e)
    _ = _ := sum_comm
  have high : (∑ k : V, num (both (S k))) ≤ 28 := calc
    _ = ∑ e : E, ∑ k : V, if both (S k) e then 1 else 0 := sum_comm
    _ ≤ ∑ _ : E, 1 := sum_le_sum (fun e _ => atMost e)
    _ = _ := by simp
  have h := sum_le_sum (s := (univ : Finset V)) (fun k _ => local_count (S k) k)
  simp only [← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  omega
end PEqualNP.Research.AffineFooling

namespace PEqualNP.Research.AffineFooling
open PEqualNP.Research.AffineRectangleCover
def sixRow (k : Fin 6) : P := (#[0,1,2,6,9,12] : Array P)[k.val]!
def sixCol (k : Fin 6) : L := (#[1,2,5,16,25,20] : Array L)[k.val]!
theorem six_zeros : ∀ k, zero (sixRow k) (sixCol k) = true := by decide +kernel
theorem six_conflicts : ∀ i j, i ≠ j →
    zero (sixRow i) (sixCol j) = false ∨ zero (sixRow j) (sixCol i) = false := by decide +kernel
end PEqualNP.Research.AffineFooling
