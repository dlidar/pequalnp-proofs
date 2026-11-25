import PEqualNP.Research.L_meta_2341_data

namespace PEqualNP.Research.PuncturedFlags
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000

/-- The intersection records all quadrangles forced true by a conjunction
of the least monotone positive extensions for these omitted coordinates. -/
def common (ds : List (Fin 26)) := ds.foldr (fun d z => column d &&& z) (2^234-1)
def omissions (ds : List (Fin 26)) := ds.foldr (fun d z => 2^d.val ||| z) 0
def pointStar : List (Fin 26) := [0,17,23,25]
def lineStar : List (Fin 26) := [1,3,9,13]
private theorem col0 : ∀ j : Fin 234, (column 0).testBit j.val = project 0 (neg j) := by decide +kernel
private theorem col1 : ∀ j : Fin 234, (column 1).testBit j.val = project 1 (neg j) := by decide +kernel
private theorem col2 : ∀ j : Fin 234, (column 2).testBit j.val = project 2 (neg j) := by decide +kernel
private theorem col3 : ∀ j : Fin 234, (column 3).testBit j.val = project 3 (neg j) := by decide +kernel
private theorem col4 : ∀ j : Fin 234, (column 4).testBit j.val = project 4 (neg j) := by decide +kernel
private theorem col5 : ∀ j : Fin 234, (column 5).testBit j.val = project 5 (neg j) := by decide +kernel
private theorem col6 : ∀ j : Fin 234, (column 6).testBit j.val = project 6 (neg j) := by decide +kernel
private theorem col7 : ∀ j : Fin 234, (column 7).testBit j.val = project 7 (neg j) := by decide +kernel
private theorem col8 : ∀ j : Fin 234, (column 8).testBit j.val = project 8 (neg j) := by decide +kernel
private theorem col9 : ∀ j : Fin 234, (column 9).testBit j.val = project 9 (neg j) := by decide +kernel
private theorem col10 : ∀ j : Fin 234, (column 10).testBit j.val = project 10 (neg j) := by decide +kernel
private theorem col11 : ∀ j : Fin 234, (column 11).testBit j.val = project 11 (neg j) := by decide +kernel
private theorem col12 : ∀ j : Fin 234, (column 12).testBit j.val = project 12 (neg j) := by decide +kernel
private theorem col13 : ∀ j : Fin 234, (column 13).testBit j.val = project 13 (neg j) := by decide +kernel
private theorem col14 : ∀ j : Fin 234, (column 14).testBit j.val = project 14 (neg j) := by decide +kernel
private theorem col15 : ∀ j : Fin 234, (column 15).testBit j.val = project 15 (neg j) := by decide +kernel
private theorem col16 : ∀ j : Fin 234, (column 16).testBit j.val = project 16 (neg j) := by decide +kernel
private theorem col17 : ∀ j : Fin 234, (column 17).testBit j.val = project 17 (neg j) := by decide +kernel
private theorem col18 : ∀ j : Fin 234, (column 18).testBit j.val = project 18 (neg j) := by decide +kernel
private theorem col19 : ∀ j : Fin 234, (column 19).testBit j.val = project 19 (neg j) := by decide +kernel
private theorem col20 : ∀ j : Fin 234, (column 20).testBit j.val = project 20 (neg j) := by decide +kernel
private theorem col21 : ∀ j : Fin 234, (column 21).testBit j.val = project 21 (neg j) := by decide +kernel
private theorem col22 : ∀ j : Fin 234, (column 22).testBit j.val = project 22 (neg j) := by decide +kernel
private theorem col23 : ∀ j : Fin 234, (column 23).testBit j.val = project 23 (neg j) := by decide +kernel
private theorem col24 : ∀ j : Fin 234, (column 24).testBit j.val = project 24 (neg j) := by decide +kernel
private theorem col25 : ∀ j : Fin 234, (column 25).testBit j.val = project 25 (neg j) := by decide +kernel
theorem column_correct : ∀ (i : Fin 26) (j : Fin 234), (column i).testBit j.val = project i (neg j) := by
  intro i; fin_cases i
  · exact col0
  · exact col1
  · exact col2
  · exact col3
  · exact col4
  · exact col5
  · exact col6
  · exact col7
  · exact col8
  · exact col9
  · exact col10
  · exact col11
  · exact col12
  · exact col13
  · exact col14
  · exact col15
  · exact col16
  · exact col17
  · exact col18
  · exact col19
  · exact col20
  · exact col21
  · exact col22
  · exact col23
  · exact col24
  · exact col25
theorem common_bit (ds : List (Fin 26)) (j : Fin 234) :
    (common ds).testBit j.val = ds.all (fun d => project d (neg j)) := by
  induction ds with
  | nil =>
    change (2^234-1 : ℕ).testBit j.val = true
    exact (by decide +kernel : ∀ k : Fin 234, (2^234-1 : ℕ).testBit k.val = true) j
  | cons d ds ih => change (column d &&& common ds).testBit j.val = _
                    rw [Nat.testBit_and,column_correct,ih]; rfl

theorem common_bound (ds : List (Fin 26)) : common ds < 2^234 := by
  cases ds with
  | nil => decide
  | cons d ds => exact lt_of_le_of_lt Nat.and_le_left ((by decide +kernel : ∀ i : Fin 26, column i < 2^234) d)

theorem zero_iff (ds : List (Fin 26)) :
    common ds = 0 ↔ ∀ j : Fin 234, ds.all (fun d => project d (neg j)) = false := by
  constructor
  · intro h j; rw [←common_bit,h,Nat.zero_testBit]
  · intro h; apply Nat.eq_of_testBit_eq; intro k; rw [Nat.zero_testBit]
    by_cases hk : k < 234
    · exact (common_bit ds ⟨k,hk⟩).trans (h ⟨k,hk⟩)
    · apply Nat.testBit_lt_two_pow
      exact (common_bound ds).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

end PEqualNP.Research.PuncturedFlags
