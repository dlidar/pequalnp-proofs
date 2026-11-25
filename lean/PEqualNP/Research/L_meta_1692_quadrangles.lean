import PEqualNP.Research.L_meta_1780_gate_price

namespace PEqualNP.Research.QuadrangleBoundary
open Finset
abbrev V := Fin 13
abbrev Side := Finset V
def inc (p l : V) := p-l ∈ ({0,1,3,9} : Side)
instance (p l : V) : Decidable (inc p l) := by unfold inc; infer_instance
def quad (Q : Side) := Q.card = 4 ∧ ∀ k : V, (Q.filter fun u => inc u k).card ≤ 2
instance (Q : Side) : Decidable (quad Q) := by unfold quad; infer_instance
def avoids (Q : Side) (l : V) := ∀ p ∈ Q, ¬ inc p l
instance (Q l) : Decidable (avoids Q l) := by unfold avoids; infer_instance
def catalog : List (Side × Side) := [
  ({0,1,2,5},{3,7,8}),
  ({0,1,2,6},{7,8,9}),
  ({0,1,2,7},{3,8,9}),
  ({0,1,2,11},{3,7,9}),
  ({0,1,4,6},{2,7,9}),
  ({0,1,4,8},{2,6,9}),
  ({0,1,4,11},{6,7,9}),
  ({0,1,4,12},{2,6,7}),
  ({0,1,5,10},{3,6,8}),
  ({0,1,5,11},{3,6,7}),
  ({0,1,5,12},{6,7,8}),
  ({0,1,6,7},{2,8,9}),
  ({0,1,6,12},{2,7,8}),
  ({0,1,7,8},{2,3,9}),
  ({0,1,7,10},{2,3,8}),
  ({0,1,8,10},{2,3,6}),
  ({0,1,8,11},{3,6,9}),
  ({0,1,10,12},{2,6,8}),
  ({0,2,3,4},{5,9,11}),
  ({0,2,3,6},{8,9,11}),
  ({0,2,3,7},{5,8,9}),
  ({0,2,3,10},{5,8,11}),
  ({0,2,4,6},{7,9,11}),
  ({0,2,4,9},{5,7,11}),
  ({0,2,4,11},{5,7,9}),
  ({0,2,5,6},{7,8,11}),
  ({0,2,5,9},{3,7,11}),
  ({0,2,5,10},{3,8,11}),
  ({0,2,7,10},{3,5,8}),
  ({0,2,7,11},{3,5,9}),
  ({0,2,9,10},{3,5,11}),
  ({0,2,9,11},{3,5,7}),
  ({0,3,4,8},{6,9,11}),
  ({0,3,4,10},{5,6,11}),
  ({0,3,4,11},{5,6,9}),
  ({0,3,5,6},{1,8,11}),
  ({0,3,5,8},{1,6,11}),
  ({0,3,5,10},{6,8,11}),
  ({0,3,5,12},{1,6,8}),
  ({0,3,6,7},{1,8,9}),
  ({0,3,6,8},{1,9,11}),
  ({0,3,7,11},{1,5,9}),
  ({0,3,7,12},{1,5,8}),
  ({0,3,8,11},{1,6,9}),
  ({0,3,10,12},{5,6,8}),
  ({0,3,11,12},{1,5,6}),
  ({0,4,6,8},{2,9,11}),
  ({0,4,6,9},{2,7,11}),
  ({0,4,8,10},{2,6,11}),
  ({0,4,9,10},{2,5,11}),
  ({0,4,9,12},{2,5,7}),
  ({0,4,10,12},{2,5,6}),
  ({0,4,11,12},{5,6,7}),
  ({0,5,6,9},{1,7,11}),
  ({0,5,6,12},{1,7,8}),
  ({0,5,8,9},{1,3,11}),
  ({0,5,8,10},{3,6,11}),
  ({0,5,8,11},{1,3,6}),
  ({0,5,9,11},{1,3,7}),
  ({0,5,11,12},{1,6,7}),
  ({0,6,7,8},{1,2,9}),
  ({0,6,7,12},{1,2,8}),
  ({0,6,8,9},{1,2,11}),
  ({0,6,9,12},{1,2,7}),
  ({0,7,8,9},{1,2,3}),
  ({0,7,8,11},{1,3,9}),
  ({0,7,9,10},{2,3,5}),
  ({0,7,9,11},{1,3,5}),
  ({0,7,9,12},{1,2,5}),
  ({0,7,10,12},{2,5,8}),
  ({0,8,9,10},{2,3,11}),
  ({0,9,11,12},{1,5,7})]
set_option maxRecDepth 32768 in
theorem valid : ∀ t ∈ catalog, quad t.1 ∧ 0 ∈ t.1 ∧ ∀ k ∈ t.2, avoids t.1 k := by
  have h : catalog.all (fun t => decide (quad t.1 ∧ 0 ∈ t.1 ∧ ∀ k ∈ t.2, avoids t.1 k)) = true := by decide +kernel
  exact fun t ht => of_decide_eq_true (List.all_eq_true.mp h t ht)
-- Each entry names a catalog block covering the normalized point and line choices.
def indices : List (List (List ℕ)) := [
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [35, 0, 0, 35, 0, 35, 35, 39, 36, 53, 0, 41, 38], [60, 0, 0, 0, 0, 0, 60, 60, 60, 62, 0, 0, 61], [55, 0, 0, 0, 0, 55, 0, 64, 55, 55, 0, 57, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [41, 0, 0, 41, 0, 0, 0, 41, 0, 67, 0, 41, 42], [36, 0, 0, 36, 0, 36, 0, 0, 36, 0, 0, 43, 38], [53, 0, 0, 0, 0, 53, 53, 0, 0, 53, 0, 58, 54], [35, 0, 0, 35, 0, 35, 35, 39, 0, 0, 0, 0, 38], [39, 0, 0, 39, 0, 0, 39, 39, 40, 0, 0, 41, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [35, 0, 0, 35, 0, 35, 35, 0, 36, 53, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [60, 0, 0, 0, 0, 0, 60, 60, 60, 62, 0, 0, 61], [4, 4, 0, 0, 4, 0, 4, 11, 5, 47, 14, 0, 7], [13, 13, 0, 0, 0, 0, 0, 13, 13, 64, 14, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [49, 0, 0, 0, 49, 0, 0, 66, 0, 49, 49, 0, 50], [5, 5, 0, 0, 5, 0, 0, 0, 5, 0, 15, 0, 7], [4, 4, 0, 0, 4, 0, 4, 0, 0, 47, 0, 0, 7], [11, 11, 0, 0, 0, 0, 11, 11, 0, 0, 14, 0, 12], [4, 4, 0, 0, 4, 0, 4, 11, 5, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [46, 0, 0, 0, 46, 0, 46, 0, 46, 47, 48, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [55, 0, 0, 0, 0, 55, 0, 64, 55, 55, 0, 57, 0], [13, 13, 0, 0, 0, 0, 0, 13, 13, 64, 14, 0, 0], [0, 0, 0, 0, 0, 0, 0, 2, 13, 26, 8, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [28, 0, 28, 0, 0, 0, 0, 28, 0, 30, 28, 29, 0], [8, 8, 0, 0, 0, 8, 0, 0, 15, 0, 8, 9, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 8, 0, 0], [2, 2, 2, 0, 0, 0, 0, 2, 13, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [26, 0, 26, 0, 0, 26, 0, 0, 55, 26, 27, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [41, 0, 0, 41, 0, 0, 0, 41, 0, 67, 0, 41, 42], [49, 0, 0, 0, 49, 0, 0, 66, 0, 49, 49, 0, 50], [28, 0, 28, 0, 0, 0, 0, 28, 0, 30, 28, 29, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 18, 18, 18, 0, 0, 20, 0, 23, 21, 24, 42], [33, 0, 0, 33, 33, 0, 0, 0, 0, 0, 33, 34, 44], [23, 0, 23, 0, 23, 0, 0, 0, 0, 23, 0, 24, 50], [20, 0, 20, 20, 0, 0, 0, 20, 0, 0, 21, 0, 42], [18, 0, 18, 18, 18, 0, 0, 20, 0, 0, 0, 24, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 18, 18, 18, 0, 0, 0, 0, 23, 21, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [36, 0, 0, 36, 0, 36, 0, 0, 36, 0, 0, 43, 38], [5, 5, 0, 0, 5, 0, 0, 0, 5, 0, 15, 0, 7], [8, 8, 0, 0, 0, 8, 0, 0, 15, 0, 8, 9, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [33, 0, 0, 33, 33, 0, 0, 0, 0, 0, 33, 34, 44], [5, 5, 0, 32, 5, 8, 0, 0, 5, 0, 8, 6, 7], [6, 6, 0, 0, 6, 9, 0, 0, 0, 0, 0, 6, 7], [8, 8, 0, 37, 0, 8, 0, 0, 0, 0, 8, 0, 10], [5, 5, 0, 32, 5, 0, 0, 0, 5, 0, 0, 6, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [32, 0, 0, 32, 32, 36, 0, 0, 32, 0, 33, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [53, 0, 0, 0, 0, 53, 53, 0, 0, 53, 0, 58, 54], [4, 4, 0, 0, 4, 0, 4, 0, 0, 47, 0, 0, 7], [0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [23, 0, 23, 0, 23, 0, 0, 0, 0, 23, 0, 24, 50], [6, 6, 0, 0, 6, 9, 0, 0, 0, 0, 0, 6, 7], [0, 0, 0, 0, 4, 0, 1, 0, 0, 23, 0, 3, 7], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 10], [1, 1, 1, 0, 4, 0, 1, 0, 0, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [22, 0, 22, 0, 22, 25, 22, 0, 0, 23, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [35, 0, 0, 35, 0, 35, 35, 39, 0, 0, 0, 0, 38], [11, 11, 0, 0, 0, 0, 11, 11, 0, 0, 14, 0, 12], [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 8, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [20, 0, 20, 20, 0, 0, 0, 20, 0, 0, 21, 0, 42], [8, 8, 0, 37, 0, 8, 0, 0, 0, 0, 8, 0, 10], [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 10], [0, 0, 0, 19, 0, 0, 1, 2, 0, 0, 8, 0, 10], [1, 1, 1, 19, 0, 0, 1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [19, 0, 19, 19, 0, 25, 19, 0, 0, 0, 21, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [39, 0, 0, 39, 0, 0, 39, 39, 40, 0, 0, 41, 0], [4, 4, 0, 0, 4, 0, 4, 11, 5, 0, 0, 0, 0], [2, 2, 2, 0, 0, 0, 0, 2, 13, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 18, 18, 18, 0, 0, 20, 0, 0, 0, 24, 0], [5, 5, 0, 32, 5, 0, 0, 0, 5, 0, 0, 6, 0], [1, 1, 1, 0, 4, 0, 1, 0, 0, 0, 0, 3, 0], [1, 1, 1, 19, 0, 0, 1, 2, 0, 0, 0, 0, 0], [1, 1, 1, 18, 4, 0, 1, 2, 5, 0, 0, 3, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 18, 18, 18, 0, 19, 0, 32, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [35, 0, 0, 35, 0, 35, 35, 0, 36, 53, 0, 0, 0], [46, 0, 0, 0, 46, 0, 46, 0, 46, 47, 48, 0, 0], [26, 0, 26, 0, 0, 26, 0, 0, 55, 26, 27, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 18, 18, 18, 0, 0, 0, 0, 23, 21, 0, 0], [32, 0, 0, 32, 32, 36, 0, 0, 32, 0, 33, 0, 0], [22, 0, 22, 0, 22, 25, 22, 0, 0, 23, 0, 0, 0], [19, 0, 19, 19, 0, 25, 19, 0, 0, 0, 21, 0, 0], [18, 0, 18, 18, 18, 0, 19, 0, 32, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [18, 0, 18, 18, 18, 25, 19, 0, 32, 23, 21, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
[[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def witness (l k r : V) : Side × Side :=
  let i := (((indices.getD l.val []).getD k.val []).getD r.val 0) % 72
  catalog[i]'(by have len : catalog.length = 72 := rfl; rw [len]; exact Nat.mod_lt _ (by decide))
theorem witness_valid (l k r : V) : witness l k r ∈ catalog := List.getElem_mem _
def lookup (l k r : V) : Bool :=
  let t := witness l k r
  decide (l ∈ t.2 ∧ k ∈ t.2 ∧ r ∈ t.1)
private theorem row0 : ∀ k r : V, ¬ inc 0 0 → ¬ inc 0 k → ¬ inc r 0 → ¬ inc r k → lookup 0 k r = true := by decide +kernel
private theorem row1 : ∀ k r : V, ¬ inc 0 1 → ¬ inc 0 k → ¬ inc r 1 → ¬ inc r k → lookup 1 k r = true := by decide +kernel
private theorem row2 : ∀ k r : V, ¬ inc 0 2 → ¬ inc 0 k → ¬ inc r 2 → ¬ inc r k → lookup 2 k r = true := by decide +kernel
private theorem row3 : ∀ k r : V, ¬ inc 0 3 → ¬ inc 0 k → ¬ inc r 3 → ¬ inc r k → lookup 3 k r = true := by decide +kernel
private theorem row4 : ∀ k r : V, ¬ inc 0 4 → ¬ inc 0 k → ¬ inc r 4 → ¬ inc r k → lookup 4 k r = true := by decide +kernel
private theorem row5 : ∀ k r : V, ¬ inc 0 5 → ¬ inc 0 k → ¬ inc r 5 → ¬ inc r k → lookup 5 k r = true := by decide +kernel
private theorem row6 : ∀ k r : V, ¬ inc 0 6 → ¬ inc 0 k → ¬ inc r 6 → ¬ inc r k → lookup 6 k r = true := by decide +kernel
private theorem row7 : ∀ k r : V, ¬ inc 0 7 → ¬ inc 0 k → ¬ inc r 7 → ¬ inc r k → lookup 7 k r = true := by decide +kernel
private theorem row8 : ∀ k r : V, ¬ inc 0 8 → ¬ inc 0 k → ¬ inc r 8 → ¬ inc r k → lookup 8 k r = true := by decide +kernel
private theorem row9 : ∀ k r : V, ¬ inc 0 9 → ¬ inc 0 k → ¬ inc r 9 → ¬ inc r k → lookup 9 k r = true := by decide +kernel
private theorem row10 : ∀ k r : V, ¬ inc 0 10 → ¬ inc 0 k → ¬ inc r 10 → ¬ inc r k → lookup 10 k r = true := by decide +kernel
private theorem row11 : ∀ k r : V, ¬ inc 0 11 → ¬ inc 0 k → ¬ inc r 11 → ¬ inc r k → lookup 11 k r = true := by decide +kernel
private theorem row12 : ∀ k r : V, ¬ inc 0 12 → ¬ inc 0 k → ¬ inc r 12 → ¬ inc r k → lookup 12 k r = true := by decide +kernel
theorem supported : ∀ l k r : V, ¬ inc 0 l → ¬ inc 0 k → ¬ inc r l → ¬ inc r k → lookup l k r = true := by
  intro l
  fin_cases l
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
  · exact row11
  · exact row12

def shift (Q : Side) (p : V) := Q.image (·+p)
theorem shift_inc (a p l : V) : inc (a+p) l ↔ inc a (l-p) := by
  unfold inc; rw [show a+p-l = a-(l-p) by abel]
theorem shift_quad (Q : Side) (p : V) (h : quad Q) : quad (shift Q p) := by
  constructor
  · simpa only [shift,card_image_of_injective _ (add_left_injective p)] using h.1
  intro k
  simpa only [shift,filter_image,shift_inc,card_image_of_injective _ (add_left_injective p)] using h.2 (k-p)
theorem shift_avoids (Q : Side) (p k : V) (h : avoids Q (k-p)) : avoids (shift Q p) k := by
  intro u hu
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hu
  exact fun e => h v hv ((shift_inc _ _ _).mp e)

theorem extend_two (p r l k : V) (pl : ¬inc p l) (pk : ¬inc p k)
    (rl : ¬inc r l) (rk : ¬inc r k) :
    ∃ Q : Side, quad Q ∧ p ∈ Q ∧ r ∈ Q ∧ avoids Q l ∧ avoids Q k := by
  have inv (a b : V) : inc (a-p) (b-p) ↔ inc a b := by unfold inc; rw [sub_sub_sub_cancel_right]
  have test := supported (l-p) (k-p) (r-p) (by simpa using fun h => pl ((inv p l).mp h))
    (by simpa using fun h => pk ((inv p k).mp h)) (fun h => rl ((inv r l).mp h)) (fun h => rk ((inv r k).mp h))
  let t := witness (l-p) (k-p) (r-p)
  have h : (l-p) ∈ t.2 ∧ (k-p) ∈ t.2 ∧ (r-p) ∈ t.1 := of_decide_eq_true test
  obtain ⟨hq,hz,ha⟩ := valid t (witness_valid _ _ _)
  exact ⟨shift t.1 p,shift_quad _ _ hq,mem_image.mpr ⟨0,hz,zero_add _⟩,
    mem_image.mpr ⟨r-p,h.2.2,sub_add_cancel _ _⟩,
    shift_avoids _ _ _ (ha _ h.1),shift_avoids _ _ _ (ha _ h.2.1)⟩

abbrev Up (F : Side → Side → Prop) := ∀ {A B C D : Side}, A ⊆ C → B ⊆ D → F A B → F C D
def extLines (Q : Side) := univ.filter (avoids Q)
theorem cross (F H : Side → Side → Prop) (fm : Up F) (hm : Up H)
    (reject : ∀ Q, quad Q → ¬(F Q (extLines Q) ∧ H Q (extLines Q)))
    (p r l k : V) (pl : ¬inc p l) (rk : ¬inc r k) (f : F {p} {l}) (h : H {r} {k}) :
    inc p k ∨ inc r l := by
  by_contra! no
  obtain ⟨Q,q,hp,hr,hl,hk⟩ := extend_two p r l k pl no.1 no.2 rk
  exact reject Q q ⟨fm (singleton_subset_iff.mpr hp) (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_univ _,hl⟩)) f,
    hm (singleton_subset_iff.mpr hr) (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_univ _,hk⟩)) h⟩

def E : Finset (V × V) := univ.filter fun e => inc e.1 e.2
theorem edge_iff (x y : V) : (x,y) ∈ E ↔ inc x y := by simp [E]
theorem thin : ∀ x z y w, x ≠ z → y ≠ w →
    ¬ ((x,y) ∈ E ∧ (x,w) ∈ E ∧ (z,y) ∈ E ∧ (z,w) ∈ E) := by
  have bound : ∀ x z : V, x ≠ z → (univ.filter fun y => inc x y ∧ inc z y).card ≤ 1 := by decide +kernel
  intro x z y w ne diff h
  simp only [edge_iff] at h
  apply diff
  apply card_le_one.mp (bound x z ne)
  · exact mem_filter.mpr ⟨mem_univ _,h.1,h.2.2.1⟩
  · exact mem_filter.mpr ⟨mem_univ _,h.2.1,h.2.2.2⟩

theorem six_from_tests (F H : Side → Side → Prop) (fm : Up F) (hm : Up H)
    (reject : ∀ Q, quad Q → ¬(F Q (extLines Q) ∧ H Q (extLines Q)))
    (a b : Fin 4 ↪ V) (frame : ∀ i, ¬inc (a i) (b i) ∧ F {a i} {b i})
    (rows : ∀ x, (univ.filter fun i => inc x (b i)).card ≤ 2)
    (cols : ∀ y, (univ.filter fun i => inc (a i) y).card ≤ 2)
    (T : Finset (V × V)) (errors : ∀ e ∈ T, ¬inc e.1 e.2 ∧ H {e.1} {e.2}) : T.card ≤ 6 := by
  apply PEqualNP.Research.PlaneGatePrice.four_pairs_six_errors E T thin a b
  · simpa only [edge_iff] using rows
  · simpa only [edge_iff] using cols
  intro e he i
  simp only [edge_iff]
  have h := cross F H fm hm reject _ _ _ _ (frame i).1 (errors e he).1 (frame i).2 (errors e he).2
  exact h.symm

def A (i : Fin 4) : V := ![0,1,2,5] i
def B (i : Fin 4) : V := ![3,6,8,7] i
def leftErrors : Finset (V × V) := univ.image fun i : Fin 4 => (A i,B i)
def rightErrors : Finset (V × V) := {(3,1),(4,5),(6,2),(7,12),(8,0),(9,4)}
theorem sharp_frame :
    Function.Injective A ∧ Function.Injective B ∧ leftErrors.card = 4 ∧ rightErrors.card = 6 ∧
    (∀ x : V, (univ.filter fun i => inc x (B i)).card ≤ 2) ∧
    (∀ y : V, (univ.filter fun i => inc (A i) y).card ≤ 2) ∧
    (∀ e ∈ leftErrors ∪ rightErrors, ¬inc e.1 e.2) ∧
    ∀ e ∈ leftErrors, ∀ f ∈ rightErrors, inc e.1 f.2 ∨ inc f.1 e.2 := by
  unfold Function.Injective
  decide +kernel

def hits (S : Finset (V × V)) (P L : Side) := ∃ e ∈ S, e.1 ∈ P ∧ e.2 ∈ L
theorem sharp_factors (P L : Side) :
    (hits (E ∪ leftErrors) P L ∧ hits (E ∪ rightErrors) P L) ↔ hits E P L := by
  constructor
  · rintro ⟨⟨e,he,hp,hl⟩,⟨f,hf,hq,hk⟩⟩
    rcases mem_union.mp he with he|he
    · exact ⟨e,he,hp,hl⟩
    rcases mem_union.mp hf with hf|hf
    · exact ⟨f,hf,hq,hk⟩
    rcases sharp_frame.2.2.2.2.2.2.2 e he f hf with e1|e2
    · exact ⟨(e.1,f.2),(edge_iff _ _).mpr e1,hp,hk⟩
    · exact ⟨(f.1,e.2),(edge_iff _ _).mpr e2,hq,hl⟩
  · rintro ⟨e,he,hp,hl⟩
    exact ⟨⟨e,mem_union_left _ he,hp,hl⟩,⟨e,mem_union_left _ he,hp,hl⟩⟩

/-- Three collinear points and three concurrent lines separately escape all negative tests. -/
theorem boundary_limit (Q : Side) (q : quad Q) :
    ¬ ({0,1,3} : Side) ⊆ Q ∧ ¬ ({0,1,5} : Side) ⊆ extLines Q := by
  constructor
  · intro sub
    have incl : ({0,1,3} : Side) ⊆ Q.filter (fun u => inc u 0) := by
      intro x hx
      have yes : ∀ u ∈ ({0,1,3} : Side), inc u 0 := by decide +kernel
      exact mem_filter.mpr ⟨sub hx,yes x hx⟩
    have n := card_le_card incl
    have three : ({0,1,3} : Side).card = 3 := by decide
    have two := q.2 0
    omega
  · intro sub
    have cert : ∀ u : V, ¬inc u 0 → ¬inc u 1 → ¬inc u 5 → u ∈ ({7,11,12} : Side) := by decide +kernel
    have incQ : Q ⊆ ({7,11,12} : Side) := by
      intro u hu
      have avoid (l : V) (hl : l ∈ ({0,1,5} : Side)) := (mem_filter.mp (sub hl)).2 u hu
      exact cert _ (avoid _ (by decide)) (avoid _ (by decide)) (avoid _ (by decide))
    have n := card_le_card incQ
    have three : ({7,11,12} : Side).card = 3 := by decide
    have four := q.1
    omega

end PEqualNP.Research.QuadrangleBoundary
