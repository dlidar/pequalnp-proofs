import Mathlib
set_option maxHeartbeats 0
namespace Mask20233Matching
abbrev Cell := Nat × Nat
def edge (i j : Nat) := (14466700110149527140 : Nat).testBit (8*i+j)
def cells : List Cell := ((List.range 8).flatMap fun i => (List.range 8).map fun j => (i,j)).filter fun (i,j) => !edge i j
def compatible (x y : Cell) : Bool :=
  x.1 != y.1 && x.2 != y.2 && edge x.1 y.2 == edge y.1 x.2
def families : List Cell → List (List Cell)
  | [] => [[]]
  | x :: xs => let t := families xs
               t ++ (t.filter fun s => s.all (compatible x)).map (x :: ·)
theorem complete {s xs : List Cell} (sub : s.Sublist xs)
    (h : s.Pairwise fun x y => compatible x y = true) : s ∈ families xs := by
  induction sub with
  | slnil => simp [families]
  | cons _ _ ih => exact List.mem_append_left _ (ih h)
  | cons_cons x _ ih =>
    rw [List.pairwise_cons] at h
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨ih h.2,List.all_eq_true.mpr h.1⟩,rfl⟩
def census : List Nat := (List.range 7).map fun k => ((families cells).filter fun s => s.length == k).length
theorem census_exact : census = [1,40,304,596,336,48,1] := by decide +kernel
theorem finite_max : (families cells).all (fun s => s.length ≤ 6) = true := by decide +kernel
theorem matching_bound {s : List Cell} (sub : s.Sublist cells)
    (h : s.Pairwise fun x y => compatible x y = true) : s.length ≤ 6 := by
  have v := List.all_eq_true.mp finite_max s (complete sub h)
  simpa using v
def attainingFamily : List Cell := [(1,7),(2,1),(3,3),(4,0),(5,4),(7,5)]
theorem matching_attains : attainingFamily.Sublist cells ∧ attainingFamily.Pairwise (fun x y => compatible x y = true) ∧ attainingFamily.length = 6 := by decide +kernel
theorem unique_maximum : ((families cells).filter fun l => l.length == 6) = [attainingFamily] := by decide +kernel
end Mask20233Matching
#print axioms Mask20233Matching.census_exact
#print axioms Mask20233Matching.matching_bound
#print axioms Mask20233Matching.matching_attains

#print axioms Mask20233Matching.unique_maximum
